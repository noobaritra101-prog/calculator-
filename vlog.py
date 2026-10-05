import os
import json
import time
import asyncio
from datetime import datetime, timezone

from aiogram.types import (
    Message, 
    BufferedInputFile, 
    InlineKeyboardMarkup, 
    InlineKeyboardButton
)
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ChatType

import config
from config import bot, main_router, ADMIN_IDS, resolve_target, get_mention, load_db, save_db

# ==========================================
# CONFIGURATION
# ==========================================
LOG_RETENTION_SECS = 30 * 24 * 3600    # Logs older than 30 days are auto-purged
LOG_RETENTION_DAYS = LOG_RETENTION_SECS // 86400
CLEANUP_INTERVAL_SECS = 3600           # Background purge runs every hour
VLOGS_FILE = "vlog.json"               # Saved inside database.zip

_TYPE_LABELS = {
    "sgive_sent":     "💠 SHARD GIFT — SENT",
    "sgive_received": "💠 SHARD GIFT — RECEIVED",
    "gift_sent":      "🎁 CARD GIFT — SENT",
    "gift_received":  "🎁 CARD GIFT — RECEIVED",
    "burn":           "🔥 CARD BURNED",
    "web_burn":       "🔥 CARD BURNED — WEB APP",
    "trade_sent":     "🔄 CARD TRADE",
    "store_buy_online":   "🛒 STORE PURCHASE — ONLINE",
    "store_buy_offline":  "🛍️ STORE PURCHASE — OFFLINE",
    "store_sell_offline": "💰 STORE SALE — OFFLINE",
    "weekly_claim":   "📅 WEEKLY CLAIM — SHARDS EARNED",
    "bowling_win":    "🎳 BOWLING — SHARDS EARNED",
    "basketball_win": "🏀 BASKETBALL — SHARDS EARNED",
    "promo_shards":   "🎫 PROMO CODE — SHARDS EARNED",
    "market_sell":    "📈 STOCK MARKET — SELL",
    "market_liquidation": "📉 STOCK MARKET — FORCED LIQUIDATION",
    "mines_win":      "💣 MINES — SHARDS EARNED",
    "ad_reward":      "📺 ADSGRAM — DAILY CARD REWARD",
    "scramble_win":     "🧩 SCRAMBLE — SOLVED (CHAT)",
    "scramble_web_win": "🧩 SCRAMBLE — SOLVED (WEB APP)",
}

_vlogs_cache = {}
_vlogs_dirty = False

# ==========================================
# THREAD-SAFE STORAGE ENGINE
# ==========================================
def load_vlogs() -> dict:
    """Load logs database from disk into memory cache."""
    global _vlogs_cache
    if _vlogs_cache:
        return _vlogs_cache
    if os.path.exists(VLOGS_FILE):
        try:
            with open(VLOGS_FILE, "r", encoding="utf-8") as f:
                _vlogs_cache = json.load(f)
        except Exception:
            _vlogs_cache = {}
    else:
        _vlogs_cache = {}
    return _vlogs_cache


def save_vlogs():
    """Flag logs as dirty. Fast in-memory execution; gets saved asynchronously."""
    global _vlogs_dirty
    _vlogs_dirty = True


def _flush_vlogs(force: bool = False):
    """Write logs to disk safely. Called inside non-blocking background thread pools."""
    global _vlogs_dirty
    if not _vlogs_dirty and not force:
        return
    try:
        tmp = VLOGS_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(_vlogs_cache, f, indent=2, ensure_ascii=False)
        os.replace(tmp, VLOGS_FILE)
        _vlogs_dirty = False
    except Exception as e:
        print(f"[VLOG] Error writing vlog.json: {e}")


def log_action(db: dict, user_id: str, entry: dict):
    """Append a log entry asynchronously."""
    entry = dict(entry)
    entry["ts"] = time.time()
    
    vlogs = load_vlogs()
    user_logs = vlogs.setdefault(str(user_id), [])
    user_logs.append(entry)
    
    _purge_user_logs(user_logs)
    save_vlogs()


def _purge_user_logs(logs: list) -> bool:
    """In-place purge of entries older than the retention window."""
    cutoff = time.time() - LOG_RETENTION_SECS
    before = len(logs)
    logs[:] = [e for e in logs if e.get("ts", 0) >= cutoff]
    return len(logs) != before


def _purge_all_vlogs() -> bool:
    """Purge old entries across all users."""
    changed = False
    vlogs = load_vlogs()
    for uid in list(vlogs.keys()):
        if _purge_user_logs(vlogs[uid]):
            changed = True
        if not vlogs[uid]:
            del vlogs[uid]
            changed = True
    return changed


async def vlog_cleanup_loop():
    """Background task to hourly purge expired records."""
    while True:
        try:
            if _purge_all_vlogs():
                save_vlogs()
        except Exception as e:
            print(f"[VLOG] Background cleanup error: {e}")
        await asyncio.sleep(CLEANUP_INTERVAL_SECS)


# ==========================================
# REPORT BUILDER
# ==========================================
def _format_entry(entry: dict, idx: int) -> str:
    ts    = entry.get("ts", 0)
    dt    = datetime.fromtimestamp(ts, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    etype = entry.get("type")
    label = _TYPE_LABELS.get(etype, etype or "UNKNOWN")

    lines = [f"[{idx}] {label}", f"Time         : {dt}"]

    if etype in ("sgive_sent", "sgive_received"):
        lines.append(f"Amount       : {entry.get('amount', 0):,} Shards")
        lines.append(f"Counterparty : {entry.get('cp_name', 'Unknown')} (ID: {entry.get('cp_id', '?')})")
    elif etype in ("gift_sent", "gift_received", "trade_sent"):
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Counterparty : {entry.get('cp_name', 'Unknown')} (ID: {entry.get('cp_id', '?')})")
    elif etype in ("burn", "web_burn"):
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Shards Earned: +{entry.get('shards_earned', 0):,}")
    elif etype == "store_buy_online":
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Price Paid   : -{entry.get('price', 0):,} Shards")
    elif etype == "store_buy_offline":
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Price Paid   : -{entry.get('price', 0):,} Shards")
        lines.append(f"Seller       : {entry.get('cp_name', 'Unknown')} (ID: {entry.get('cp_id', '?')})")
    elif etype == "store_sell_offline":
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Price Earned : +{entry.get('price', 0):,} Shards")
        lines.append(f"Buyer        : {entry.get('cp_name', 'Unknown')} (ID: {entry.get('cp_id', '?')})")
    elif etype == "weekly_claim":
        lines.append(f"Shards Earned: +{entry.get('amount', 0):,}")
        if entry.get("bio_bonus"):
            lines.append(f"Bio Bonus    : Yes")
    elif etype in ("bowling_win", "basketball_win"):
        lines.append(f"Shards Earned: +{entry.get('amount', 0):,}")
    elif etype == "promo_shards":
        lines.append(f"Promo Code   : {entry.get('code', 'Unknown')}")
        lines.append(f"Shards Earned: +{entry.get('amount', 0):,}")
    elif etype == "market_sell":
        lines.append(f"Symbol       : {entry.get('symbol', 'Unknown')}")
        lines.append(f"Shares Sold  : {entry.get('shares', 0)}")
        lines.append(f"Net Payout   : +{entry.get('amount', 0):,} Shards")
        profit = entry.get("profit", 0)
        lines.append(f"P/L          : {'+' if profit >= 0 else ''}{profit:,} Shards")
    elif etype == "market_liquidation":
        lines.append(f"Symbol       : {entry.get('symbol', 'Unknown')}")
        lines.append(f"Shares Sold  : {entry.get('shares', 0)}")
        lines.append(f"Net Payout   : +{entry.get('amount', 0):,} Shards")
        profit = entry.get("profit", 0)
        lines.append(f"P/L          : {'+' if profit >= 0 else ''}{profit:,} Shards")
        lines.append(f"Reason       : Nightly forced liquidation")
    elif etype == "mines_win":
        lines.append(f"Bet          : {entry.get('bet', 0):,} Shards")
        lines.append(f"Mines        : {entry.get('mines', 0)}")
        lines.append(f"Gems Found   : {entry.get('gems_found', 0)}")
        lines.append(f"Multiplier   : {entry.get('multiplier', 0)}x")
        lines.append(f"Payout       : +{entry.get('amount', 0):,} Shards")
    elif etype in ("scramble_win", "scramble_web_win"):
        lines.append(f"Card         : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")
        lines.append(f"Solve Time   : {entry.get('time', 0)}s")
        if entry.get("moves") is not None:
            lines.append(f"Moves        : {entry.get('moves')}")
        lines.append(f"Shards Earned: +{entry.get('amount', 0):,}")
        if entry.get("earned", 0) > entry.get("amount", 0):
            lines.append(f"Note         : Daily cap reached (tier was worth {entry.get('earned'):,})")
    elif etype == "ad_reward":
        lines.append(f"Card Earned  : {entry.get('card_name', 'Unknown')}")
        lines.append(f"Rarity       : {entry.get('rarity', 'Unknown')}")

    lines.append(f"Chat         : {entry.get('chat_title', 'Unknown')} (ID: {entry.get('chat_id', '?')})")
    lines.append("-" * 44)
    return "\n".join(lines)


def _build_report(target_id: str, target_name: str, logs: list) -> str:
    logs_sorted = sorted(logs, key=lambda e: e.get("ts", 0))
    
    separator = "=" * 44
    header = (
        "NEXUS VAULT ACTIVITY LOG\n"
        f"{separator}\n"
        f"User       : {target_name} (ID: {target_id})\n"
        f"Generated  : {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')}\n"
        f"Window     : Last {LOG_RETENTION_DAYS} days (older entries auto-deleted)\n"
        f"Entries    : {len(logs_sorted)}\n"
        f"{separator}\n\n"
    )
    body = "\n".join(_format_entry(e, i) for i, e in enumerate(logs_sorted, start=1))
    return header + body


# ==========================================
# /vlog — ADMIN ONLY
# ==========================================
@main_router.message(Command("vlog"))
async def vlog_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    # ── Resolve target ────────────────────────────────────────────────────────
    if message.reply_to_message and message.reply_to_message.from_user:
        target_id   = str(message.reply_to_message.from_user.id)
        target_name = message.reply_to_message.from_user.first_name
    elif command.args:
        target_id, target_name = await resolve_target(command.args.strip(), message)
        if not target_id:
            await message.reply(
                f"⚠️ Could not resolve target <code>{command.args.strip()}</code>.",
                parse_mode=ParseMode.HTML
            )
            return
        target_id = str(target_id)
    else:
        await message.reply(
            "<b>「 📄 VAULT LOG 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            "Reply to a user, or:\n"
            "<code>/vlog &lt;@username | user_id&gt;</code>\n\n"
            f"Returns a full <code>.logs</code> log of that user's\n"
            "<b>/sgive</b>, <b>/gift</b>, <b>/trade</b>, <b>/burn</b>,\n"
            "<b>store</b> (online + offline), and all\n"
            "<b>shard-earning</b> activity — weekly claims, bowling/\n"
            "basketball wins, promo codes, stock market sales, and\n"
            f"mines — from the last {LOG_RETENTION_DAYS} days.",
            parse_mode=ParseMode.HTML
        )
        return

    # Prune expired records across the logs database
    if _purge_all_vlogs():
        save_vlogs()

    vlogs = load_vlogs()
    logs = vlogs.get(target_id, [])
    if not logs:
        await message.reply(
            f"No activity logged for <b>{target_name}</b> (<code>{target_id}</code>) in the last {LOG_RETENTION_DAYS} days.",
            parse_mode=ParseMode.HTML
        )
        return

    report = _build_report(target_id, target_name, logs)
    file = BufferedInputFile(report.encode("utf-8"), filename=f"{target_id}.logs")
    
    admin_id = message.from_user.id
    caption_text = f"📄 <b>Vault log</b> for <b>{target_name}</b> (<code>{target_id}</code>) — {len(logs)} entries, last {LOG_RETENTION_DAYS} days."

    # ── Delivery Execution ───────────────────────────────────────────────────
    if message.chat.type == ChatType.PRIVATE:
        await message.reply_document(
            document=file,
            caption=caption_text,
            parse_mode=ParseMode.HTML
        )
    else:
        try:
            await bot.send_document(
                chat_id=admin_id,
                document=file,
                caption=caption_text,
                parse_mode=ParseMode.HTML
            )
            
            bot_info = await bot.get_me()
            bot_username = bot_info.username
            
            kb = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="View 📁", url=f"https://t.me/{bot_username}")]
            ])
            
            target_mention = get_mention(target_id, target_name)
            await message.reply(
                f"✨ {target_mention} logs Sent to Your DM !",
                reply_markup=kb,
                parse_mode=ParseMode.HTML
            )
        except Exception:
            await message.reply(
                "⚠️ <b>Could not send logs to your DM!</b>\n"
                "Please verify that you have initiated a private chat with the bot first.",
                parse_mode=ParseMode.HTML
            )
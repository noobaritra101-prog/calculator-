import io
import os
import sys
import time
import json
import uuid
import asyncio
import traceback
import random
import difflib
import aiohttp
from datetime import datetime, timezone
from aiogram import F
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto, FSInputFile
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ChatType
from aiogram.exceptions import TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest

import config # 👈 FIXED: Added the missing config import

from config import (
    bot, main_router, ADMIN_IDS, SUPREME_OWNER_ID, DB_GROUP_ID,
    RARITIES, format_rarity, load_db, save_db, perform_backup,
    get_mention, resolve_target, bot_start_time, DB_FILE,
    BROWSE_PER_PAGE, RARITY_SAFE, SAFE_RARITY,
    is_ghost_banned, is_shadow_banned, ensure_user,
    parse_gban_duration_token, format_duration_seconds,
    log_gban_to_public, log_gunban_to_public, # 👈 Added
    QUERY_GROUP_ID, active_drops
)

from handlers import trigger_drop

# deck.py owns the ad-reward system and its shared error logger — reuse the
# same objects here rather than duplicating them, so /dlog and /bug read the
# exact log file (and get_user_from_db logic) deck.py itself writes to.
from deck import get_user_from_db, DLOG_PATH, dlog, ADSGRAM_ADS_PER_CYCLE, BACKEND_PUBLIC_URL, _today_str

# Shared banner detection/storage helpers — build_profile_banner() (used by
# handlers.py's /profile) and all banner-related commands (/ab, /rb,
# /lbanner, /set_default, /mybanners) now live entirely in banners.py; only
# get_active_banner_id() is needed here, for /check's user inspector.
from banners import get_active_banner_id

# ==========================================
# ADMIN ACTIVITY LOGGER (/adl)
# ==========================================
ADMIN_LOG_FILE = "admins_history.logs"
ADMIN_LOG_ROTATE_SECONDS = 30 * 24 * 3600  # ~1 month

def _admin_log_needs_rotation() -> bool:
    """True if the current log file is older than the rotation window (or unreadable)."""
    if not os.path.exists(ADMIN_LOG_FILE):
        return False
    try:
        with open(ADMIN_LOG_FILE, "r", encoding="utf-8") as f:
            first_line = f.readline().strip()
        if first_line.startswith("# LOG STARTED:"):
            started_ts = float(first_line.split(":", 1)[1].strip())
            return (time.time() - started_ts) >= ADMIN_LOG_ROTATE_SECONDS
    except Exception:
        pass
    return True  # unreadable/corrupt header — safest to rotate

def log_admin_action(admin_id: int, admin_name: str, action: str, details: str = ""):
    """Append an entry to the rolling admin activity log.
    The file auto-rotates: once it's ~1 month old, it's deleted and a
    fresh one starts on the next logged action."""
    try:
        if _admin_log_needs_rotation():
            os.remove(ADMIN_LOG_FILE)
    except Exception:
        pass

    is_new = not os.path.exists(ADMIN_LOG_FILE)
    try:
        with open(ADMIN_LOG_FILE, "a", encoding="utf-8") as f:
            if is_new:
                f.write(f"# LOG STARTED: {time.time()}\n")
                f.write("# Admin/Owner activity log — resets automatically every ~30 days\n")
                f.write("=" * 60 + "\n")
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            line = f"[{ts}] {admin_name} ({admin_id}) — {action}"
            if details:
                line += f": {details}"
            f.write(line + "\n")
    except Exception as e:
        print(f"[ADMIN_LOG] Failed to write entry: {e}")

@main_router.message(Command("adl"))
async def admin_log_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return

    if _admin_log_needs_rotation():
        try:
            os.remove(ADMIN_LOG_FILE)
        except Exception:
            pass

    if not os.path.exists(ADMIN_LOG_FILE):
        await message.reply("📄 No admin activity has been logged yet this cycle.", parse_mode=ParseMode.HTML)
        return

    try:
        doc = FSInputFile(ADMIN_LOG_FILE, filename="admins_history.logs")
        await message.reply_document(document=doc, caption="📜 <b>Admin Activity Log</b>", parse_mode=ParseMode.HTML)
    except Exception as e:
        await message.reply(f"⚠️ Failed to send log file: {e}", parse_mode=ParseMode.HTML)

# ==========================================
# /dlog COMMAND (SEND dlog.txt — ADMIN ONLY)
# Moved here from deck.py so every admin command lives in one place.
# ==========================================
@main_router.message(Command("dlog"))
async def dlog_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not os.path.exists(DLOG_PATH) or os.path.getsize(DLOG_PATH) == 0:
        await message.reply("<b>dlog.txt</b> is empty — no errors logged.", parse_mode=ParseMode.HTML)
        return

    # Flush the handler so the very latest error (if any just happened) is
    # actually on disk before we read/send the file.
    for h in dlog.handlers:
        h.flush()

    await message.reply_document(
        FSInputFile(DLOG_PATH),
        caption=f"<b>dlog.txt</b> — {os.path.getsize(DLOG_PATH)} bytes",
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /bug <user_id> COMMAND — LIVE DIAGNOSTIC (ADMIN ONLY, bot DM only)
# ==========================================
# Pulls together the three things that actually explain "the web app won't
# load for me": their DB/ban state, a live hit against the SAME endpoint the
# mini app itself calls (so we see real status/latency, not a guess), and
# any dlog.txt entries tagged with their ID — including /clientlog reports
# the frontend already sends for network/JS failures the backend would
# otherwise never see.
@main_router.message(Command("bug"))
async def bug_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    # Only usable in the bot's DM — silently ignore if run in a group/supergroup/channel.
    if message.chat.type != "private":
        return

    if not command.args or not command.args.strip().isdigit():
        await message.reply("<b>Usage:</b> <code>/bug &lt;user_id&gt;</code>", parse_mode=ParseMode.HTML)
        return

    target_uid = command.args.strip()
    lines = [f"<b>「 BUG REPORT — {target_uid} 」</b>", "━━━━━━━━━━━━━━━━━"]

    # 1. DB / ban state
    db = load_db()
    actual_key, user_data = get_user_from_db(db, target_uid)
    if not user_data:
        ensure_user(target_uid, "User", None)
        db = load_db()
        actual_key, user_data = get_user_from_db(db, target_uid)

    if not user_data:
        lines.append("<b>DB record:</b> not found (even after ensure_user)")
    else:
        cards = user_data.get("cards", {}) if isinstance(user_data.get("cards"), dict) else {}
        progress = user_data.get("ad_progress", {}) if isinstance(user_data.get("ad_progress"), dict) else {}
        uid_int = int(target_uid)
        lines.append(f"<b>DB key:</b> <code>{actual_key}</code> ({type(actual_key).__name__})")
        lines.append(f"<b>Cards owned:</b> {len(cards)}  |  <b>Shards:</b> {user_data.get('nexus_shards', 0)}")
        lines.append(f"<b>Ghost banned:</b> {is_ghost_banned(uid_int)}  |  <b>Shadow banned:</b> {is_shadow_banned(uid_int)}")
        lines.append(
            f"<b>Ad progress:</b> {progress.get('watched', 0)}/{ADSGRAM_ADS_PER_CYCLE} "
            f"(date={progress.get('date', '—')}, claimed={progress.get('claimed', False)})"
        )

    # 2. Live reachability check — same endpoint the deck mini app calls
    lines.append("━━━━━━━━━━━━━━━━━")
    check_url = f"{BACKEND_PUBLIC_URL}/api/deck/state/{target_uid}"
    t0 = time.monotonic()
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as session:
            async with session.get(check_url) as resp:
                elapsed_ms = int((time.monotonic() - t0) * 1000)
                lines.append(f"<b>/api/deck/state check:</b> HTTP {resp.status} in {elapsed_ms}ms")
                if resp.status == 200:
                    try:
                        data = await resp.json()
                        if data.get("error"):
                            lines.append("Endpoint responded but flagged <code>error: true</code> internally — check dlog.txt for the crash.")
                    except Exception:
                        lines.append("Response wasn't valid JSON")
    except Exception as e:
        elapsed_ms = int((time.monotonic() - t0) * 1000)
        lines.append(f"<b>/api/deck/state check:</b> FAILED after {elapsed_ms}ms — {type(e).__name__}: {e}")

    # 3. Recent dlog.txt entries mentioning this user (includes /clientlog hits)
    lines.append("━━━━━━━━━━━━━━━━━")
    matches = []
    if os.path.exists(DLOG_PATH):
        for h in dlog.handlers:
            h.flush()
        try:
            with open(DLOG_PATH, "r", encoding="utf-8") as f:
                matches = [ln.rstrip() for ln in f if target_uid in ln]
        except Exception as e:
            matches = [f"(failed to read dlog.txt: {e})"]

    if matches:
        recent = matches[-5:]
        lines.append(f"<b>dlog.txt hits ({len(matches)} total, showing last {len(recent)}):</b>")
        for m in recent:
            safe = m.replace("<", "&lt;").replace(">", "&gt;")[:300]
            lines.append(f"<code>{safe}</code>")
    else:
        lines.append("<b>dlog.txt:</b> no entries mention this user ID")

    await message.reply("\n".join(lines), parse_mode=ParseMode.HTML)


# ==========================================
# /adstats COMMAND — AD WATCH/CLAIM STATS (ADMIN ONLY)
# ==========================================
# Ad watch counts only ever live in each user's per-day ad_progress dict,
# which resets on the next UTC day the user is touched — there's no
# separate all-time counter anywhere in the db. So this reports an
# aggregate snapshot of today's activity across every user, not a
# historical lifetime total; it's the only accurate number this data
# supports.
@main_router.message(Command("adstats"))
async def adstats_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    db = load_db()
    users = db.get("users", {}) if isinstance(db, dict) else {}
    today = _today_str()

    total_users = len(users)
    active_today = 0
    views_today = 0
    completed_today = 0
    claimed_today = 0
    ready_unclaimed = 0

    for user_data in users.values():
        if not isinstance(user_data, dict):
            continue
        progress = user_data.get("ad_progress")
        if not isinstance(progress, dict) or progress.get("date") != today:
            continue
        watched = progress.get("watched", 0)
        if watched > 0:
            active_today += 1
            views_today += watched
        if watched >= ADSGRAM_ADS_PER_CYCLE:
            completed_today += 1
        if progress.get("claimed"):
            claimed_today += 1
        elif watched >= ADSGRAM_ADS_PER_CYCLE:
            ready_unclaimed += 1

    lines = [
        "<b>「 AD STATS — TODAY 」</b>",
        "━━━━━━━━━━━━━━━━━",
        f"<b>Total users:</b> {total_users}",
        f"<b>Watched at least 1 ad today:</b> {active_today}",
        f"<b>Total ad views today:</b> {views_today}",
        f"<b>Hit today's requirement ({ADSGRAM_ADS_PER_CYCLE}/{ADSGRAM_ADS_PER_CYCLE}):</b> {completed_today}",
        f"<b>Claimed today's reward:</b> {claimed_today}",
        f"<b>Ready to claim but haven't yet:</b> {ready_unclaimed}",
    ]
    await message.reply("\n".join(lines), parse_mode=ParseMode.HTML)


# ==========================================
# SAFE ANIME-NAME <-> CALLBACK KEY MAPPING
# ==========================================
# Telegram callback_data has a hard 64-byte limit, so long anime titles
# can't be embedded directly. Previously this was "solved" by truncating
# the name to 35 characters, which silently corrupted any title longer
# than that (e.g. "The Angel Next Door Spoils Me Rotten" — 36 chars) and
# broke exact-match lookups downstream. Instead, we use a short stable
# hash of the full name as the callback key, and resolve it back to the
# real name on demand by hashing the live anime list and matching.
import hashlib

def anime_hash_key(anime_name: str) -> str:
    """Short, stable, collision-resistant key safe for callback_data."""
    return hashlib.md5(anime_name.encode("utf-8")).hexdigest()[:12]


def anime_key_lookup(db: dict, anime_key: str) -> str | None:
    """Resolves a hash key back to the full, untruncated anime name by
    checking it against every anime title currently in global_cards."""
    cards = db.get("global_cards", {})
    anime_titles = set(c["anime"] for c in cards.values())
    for anime in anime_titles:
        if anime_hash_key(anime) == anime_key:
            return anime
    return None


# ==========================================
# CENTRALISED DB-GROUP ACTIVITY LOGGER
# ==========================================
async def send_log(text: str):
    """Send a structured log message to the backup/log group. Silent on failure."""
    try:
        await bot.send_message(
            chat_id=config.DATABASE_BACKUP_ID,
            text=text,
            parse_mode=ParseMode.HTML,
            disable_web_page_preview=True
        )
    except Exception as e:
        print(f"[LOG] Failed to send log to backup group: {e}")

# ==========================================
# AUTO GROUP REGISTRATION MIDDLEWARE
# ==========================================
@main_router.message.middleware()
async def auto_register_group_mw(handler, message: Message, data: dict):
    """If a command is used inside a group/supergroup that isn't tracked in
    the database yet, silently register it before the command handler runs —
    so /bnxcast, /info, /cleangroups etc. always see it, without needing the
    bot to have caught a separate 'added to group' event first."""
    if (
        message.chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
        and message.text
        and message.text.startswith("/")
    ):
        db = load_db()
        gid = str(message.chat.id)
        if gid not in db.get("groups", {}):
            db.setdefault("groups", {})[gid] = {
                "title": message.chat.title or "Unknown Group",
                "joined": int(time.time()),
                "drops": 0,
                "claims": 0
            }
            save_db()

    return await handler(message, data)

# ==========================================
# POWERFUL EVALUATION COMMAND (/eval)
# ==========================================
@main_router.message(Command("eval"))
async def eval_cmd(message: Message, command: CommandObject):
    if message.from_user.id != SUPREME_OWNER_ID: return
    if not command.args:
        await message.reply("⚠️ Provide code to evaluate.", parse_mode=ParseMode.HTML)
        return

    code = command.args
    old_stdout = sys.stdout
    redirected_output = sys.stdout = io.StringIO()

    variables = {
        'bot': bot,
        'message': message,
        'command': command,
        'config': config,
        'db': load_db(),
        'save_db': save_db,
        'asyncio': asyncio,
        'sys': sys,
        'os': os,
        'time': time
    }

    formatted_code = f"async def _eval_expr():\n" + "".join(f"    {line}\n" for line in code.split("\n"))

    try:
        exec(formatted_code, variables)
        _eval_expr = variables['_eval_expr']
        result = await _eval_expr()
        stdout_val = redirected_output.getvalue()
    except Exception:
        stdout_val = redirected_output.getvalue()
        result = traceback.format_exc()
    finally:
        sys.stdout = old_stdout

    output = stdout_val.strip() or str(result)
    if len(output) > 3000:
        output = output[:3000] + "\n... truncated due to size limit ..."

    await message.reply(
        f"<b>📝 Evaluation Output:</b>\n"
        f"<code>{output}</code>",
        parse_mode=ParseMode.HTML
    )

# ==========================================
# SYSTEM MAINTENANCE TOOLS
# ==========================================
@main_router.message(Command("ping"))
async def ping_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    start_time = time.time()
    msg = await message.reply("⚡ <b>Measuring latency...</b>", parse_mode=ParseMode.HTML)
    latency = round((time.time() - start_time) * 1000)
    await msg.edit_text(
        f"🏓 <b>Pong!</b>\nLatency is <b>{latency}ms</b>.", 
        parse_mode=ParseMode.HTML
    )

# os.execv() replaces the running process image outright — nothing after that
# call ever runs, so refresh_cmd can never edit its own status message once
# the reload has actually finished. Instead we drop a small breadcrumb file
# with the chat/message to edit, and a startup hook on the fresh process
# picks it up and finishes the edit once the bot is back online.
REFRESH_STATE_FILE = "refresh_pending.json"

@main_router.message(Command("refresh"))
async def refresh_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    status_msg = await message.reply("🔄 <b>Synchronizing cache & hot-restarting bot engines...</b>", parse_mode=ParseMode.HTML)

    try:
        with open(REFRESH_STATE_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "chat_id": status_msg.chat.id,
                "message_id": status_msg.message_id,
                "started_at": time.time(),
            }, f)
    except Exception:
        pass

    save_db()
    await perform_backup()

    os.execv(sys.executable, [sys.executable] + sys.argv)


@main_router.startup()
async def _finish_refresh_notice():
    """Runs once whenever the bot (re)starts. If a /refresh just fired
    os.execv on us, a breadcrumb file is sitting on disk — edit the original
    'Synchronizing...' message into a completion notice and clean up.
    On a normal boot (no breadcrumb) this is a silent no-op."""
    if not os.path.exists(REFRESH_STATE_FILE):
        return

    try:
        with open(REFRESH_STATE_FILE, "r", encoding="utf-8") as f:
            state = json.load(f)
    except Exception:
        state = None
    finally:
        try:
            os.remove(REFRESH_STATE_FILE)
        except Exception:
            pass

    if not state:
        return

    elapsed = time.time() - state.get("started_at", time.time())
    try:
        await bot.edit_message_text(
            chat_id=state["chat_id"],
            message_id=state["message_id"],
            text=f"✅ <b>Refresh complete!</b> Bot engines are back online.\n⏱ <b>Downtime:</b> <code>{elapsed:.1f}s</code>",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass

@main_router.message(Command("cleangroups"))
async def clean_groups_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    msg = await message.reply("🧹 <b>Scanning database records for invalid group memberships...</b>", parse_mode=ParseMode.HTML)
    
    db = load_db()
    inactive_groups = []
    
    for gid in list(db.get("groups", {}).keys()):
        try:
            await bot.get_chat_member(chat_id=int(gid), user_id=message.bot.id)
        except Exception:
            inactive_groups.append(gid)
            
    for gid in inactive_groups:
        db["groups"].pop(gid, None)
        
    save_db()
    await msg.edit_text(
        f"✅ <b>Cleanup Complete!</b>\n"
        f"Removed <b>{len(inactive_groups)} groups</b> where the bot is no longer present.", 
        parse_mode=ParseMode.HTML
    )

# ==========================================
# ADMINISTRATIVE PICTURE AND SYSTEM TOOLS
# ==========================================
@main_router.message(Command("up"))
async def update_pictures(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    
    valid_modes = ["st", "hp", "lb", "sm", "store", "onst", "offst"]
    if not command.args or command.args.lower() not in valid_modes:
        await message.reply(
            "⚠️ <b>Usage:</b> Reply to a photo with <code>/up &lt;mode&gt;</code>\n\n"
            "<b>Valid Modes:</b>\n"
            "• <code>st</code>: Start Page Pic\n"
            "• <code>hp</code>: Help Page Pic\n"
            "• <code>lb</code>: Leaderboard Page Pic\n"
            "• <code>sm</code>: Stock Market Pic\n"
            "• <code>store</code>: Main Store Pic\n"
            "• <code>onst</code>: Online Store Pic\n"
            "• <code>offst</code>: Offline Store Pic", 
            parse_mode=ParseMode.HTML
        )
        return
    
    if not message.reply_to_message or not message.reply_to_message.photo:
        await message.reply("⚠️ You must reply to an image to update the picture parameter.", parse_mode=ParseMode.HTML)
        return
        
    mode = command.args.lower()
    file_id = message.reply_to_message.photo[-1].file_id
    db = load_db()
    
    target_map = {
        "st": ("start_pic", "Start picture"),
        "hp": ("help_pic", "Help picture"),
        "lb": ("leaderboard_pic", "Leaderboard picture"),
        "sm": ("pic_stockmarket", "Stock Market picture"),
        "store": ("pic_store", "Main Store picture"),
        "onst": ("pic_online_store", "Online Store picture"),
        "offst": ("pic_offline_store", "Offline Store picture")
    }
    
    key, label = target_map[mode]
    db.setdefault("settings", {})[key] = file_id
    save_db()
    await message.reply(f"✅ <b>{label}</b> has been updated successfully!", parse_mode=ParseMode.HTML)

@main_router.message(Command("backup"))
async def backup_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    await message.reply("⚙️ Backing up database to group...")
    await perform_backup()
    await message.reply("✅ Backup completed and pinned.")

@main_router.message(Command("import"))
async def import_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    if not message.reply_to_message or not message.reply_to_message.document:
        await message.reply("⚠️ Reply to a database.json document to import.", parse_mode=ParseMode.HTML)
        return
    doc = message.reply_to_message.document
    if not doc.file_name.endswith(".json"):
        await message.reply("⚠️ File must be a JSON document.", parse_mode=ParseMode.HTML)
        return
    msg = await message.reply("📥 Downloading and importing database...", parse_mode=ParseMode.HTML)
    try:
        file_info = await bot.get_file(doc.file_id)
        await bot.download_file(file_info.file_path, destination=DB_FILE)

        # ── CRITICAL FIX: Invalidate the in-memory cache so load_db() re-reads
        # the freshly downloaded file on the very next call instead of serving
        # the stale pre-import snapshot that was already in RAM.
        import config as _cfg
        _cfg._db_cache = None
        _cfg._db_dirty = False

        await msg.edit_text("✅ Database successfully imported and loaded into memory!", parse_mode=ParseMode.HTML)
    except Exception as e:
        await msg.edit_text(f"Import failed: {e}", parse_mode=ParseMode.HTML)

# ==========================================
# CARD MANAGEMENT CONTROLS
# ==========================================
@main_router.message(Command("add_card"))
async def add_card(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args or not message.reply_to_message or not message.reply_to_message.photo:
        await message.reply("⚠️ Reply to an image.\n<code>/add_card Name | Anime | Rarity</code>", parse_mode=ParseMode.HTML)
        return
    try:
        args = command.args.split("|")
        char_name, anime_name, rarity = args[0].strip(), args[1].strip(), args[2].strip()
    except Exception:
        await message.reply("⚠️ Format: <code>/add_card Character | Anime | Rarity</code>", parse_mode=ParseMode.HTML)
        return

    formatted_rar = format_rarity(rarity)
    if formatted_rar not in RARITIES:
        await message.reply(f"⚠️ Invalid rarity! Use one of:\n" + "\n".join(f"  <code>{r}</code>" for r in RARITIES), parse_mode=ParseMode.HTML)
        return

    file_id = message.reply_to_message.photo[-1].file_id
    card_id = f"DB-{str(uuid.uuid4())[:6].upper()}"
    db = load_db()

    added_by = message.from_user.id
    added_by_mention = get_mention(added_by, message.from_user.first_name)

    log_text = (
        "<b>「 📥 DATABASE LOG : NEW CARD 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        "<blockquote><i>A new collectable character card has been registered globally.</i></blockquote>\n\n"
        f"• 🆔 <b>Card ID:</b> <code>{card_id}</code>\n"
        f"• 👤 <b>Character:</b> <b>{char_name}</b>\n"
        f"• 📺 <b>Anime:</b> <i>{anime_name}</i>\n"
        f"• 🌟 <b>Rarity:</b> <b>{formatted_rar}</b>\n"
        f"• — <b>Added By:</b> {added_by_mention}\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    msg_id = None
    try: 
        msg = await bot.send_photo(DB_GROUP_ID, photo=file_id, caption=log_text, parse_mode=ParseMode.HTML)
        msg_id = msg.message_id
    except Exception as e: 
        print(f"[LOG_GROUP] Send failed: {e}")

    db["global_cards"][card_id] = {
        "name": char_name, "anime": anime_name, "rarity": formatted_rar,
        "file_id": file_id, "msg_id": msg_id, "added_by": added_by
    }
    save_db()

    log_admin_action(
        added_by, message.from_user.first_name,
        "ADD CARD", f"{char_name} [{anime_name}] ({formatted_rar}) — ID: {card_id}"
    )

    await message.reply(log_text + "\n\n✅ Saved!", parse_mode=ParseMode.HTML)

@main_router.message(Command("remove_card"))
async def remove_card(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args:
        await message.reply("⚠️ Format: <code>/remove_card DB-XXXXXX</code>", parse_mode=ParseMode.HTML)
        return
        
    card_id = command.args.split()[0].strip().upper()
    db = load_db()
    
    if card_id not in db["global_cards"]:
        await message.reply(f"Card <code>{card_id}</code> not found.", parse_mode=ParseMode.HTML)
        return
        
    removed = db["global_cards"].pop(card_id)

    # Also strip this card out of every user's personal inventory
    affected_users = 0
    for u_data in db.get("users", {}).values():
        user_cards = u_data.get("cards")
        if user_cards and card_id in user_cards:
            del user_cards[card_id]
            affected_users += 1

    save_db()

    # If this card is currently live as a drop in any group, that drop
    # would otherwise become permanently unseizable — /seize looks it up
    # fresh from global_cards and would find nothing, but the drop stays
    # stuck in active_drops until it eventually expires, blocking that
    # chat's drop rotation the whole time. Clear it here immediately.
    stale_chats = [cid for cid, d in active_drops.items() if d.get("card_id") == card_id]
    for cid in stale_chats:
        drop_data = active_drops.pop(cid, None)
        if drop_data and drop_data.get("message_id"):
            try:
                await bot.delete_message(chat_id=int(cid), message_id=drop_data["message_id"])
            except Exception:
                pass

    msg_id = removed.get("msg_id")
    if msg_id:
        try:
            await bot.delete_message(chat_id=DB_GROUP_ID, message_id=msg_id)
        except Exception:
            pass

    log_admin_action(
        message.from_user.id, message.from_user.first_name,
        "REMOVE CARD", f"{removed['name']} [{removed.get('anime', 'Unknown')}] — ID: {card_id}"
        + (f" — cleared {len(stale_chats)} live drop(s)" if stale_chats else "")
    )

    await message.reply(
        f"🗑️ Removed: <b>{removed['name']}</b> (<code>{card_id}</code>)\n"
        f"✅ Removed from Global Database & GC.\n"
        f"👥 Stripped from <b>{affected_users}</b> user inventor{'y' if affected_users == 1 else 'ies'}."
        + (f"\n♻️ Cleared {len(stale_chats)} live drop(s) of this card." if stale_chats else ""),
        parse_mode=ParseMode.HTML
    )

@main_router.message(Command("edit_card"))
async def edit_card(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args:
        await message.reply(
            "⚠️ <b>Usage:</b>\n<code>/edit_card DB-XXXXXX | New Name | New Anime | New Rarity</code>\n\n"
            "<i>Note: If you want to change the picture, reply to a new image with this command. If you don't reply to an image, the old picture is kept. Leave text fields blank between pipes ' | ' to keep old text.</i>", 
            parse_mode=ParseMode.HTML
        )
        return
        
    args = command.args.split("|")
    card_id = args[0].strip().upper()
    
    db = load_db()
    if card_id not in db["global_cards"]:
        await message.reply(f"Card <code>{card_id}</code> not found.", parse_mode=ParseMode.HTML)
        return
        
    card_data = db["global_cards"][card_id]
    
    new_name = args[1].strip() if len(args) > 1 and args[1].strip() else card_data["name"]
    new_anime = args[2].strip() if len(args) > 2 and args[2].strip() else card_data["anime"]
    
    new_rarity = format_rarity(args[3].strip()) if len(args) > 3 and args[3].strip() else card_data["rarity"]
    if new_rarity not in RARITIES:
        await message.reply(f"⚠️ Invalid rarity! Leave empty or use:\n" + "\n".join(f"  <code>{r}</code>" for r in RARITIES), parse_mode=ParseMode.HTML)
        return
        
    new_file_id = card_data["file_id"]
    photo_changed = False
    if message.reply_to_message and message.reply_to_message.photo:
        new_file_id = message.reply_to_message.photo[-1].file_id
        photo_changed = True

    old_name, old_anime, old_rarity = card_data["name"], card_data["anime"], card_data["rarity"]

    db["global_cards"][card_id]["name"] = new_name
    db["global_cards"][card_id]["anime"] = new_anime
    db["global_cards"][card_id]["rarity"] = new_rarity
    db["global_cards"][card_id]["file_id"] = new_file_id

    # Propagate the updated name/rarity to every user who already owns this card,
    # since owned copies store a snapshot instead of a live reference.
    synced_owners = 0
    for udata in db["users"].values():
        owned = udata.get("cards", {}).get(card_id)
        if owned:
            owned["name"] = new_name
            owned["rarity"] = new_rarity
            synced_owners += 1

    save_db()

    changes = []
    if new_name != old_name:
        changes.append(f"name: '{old_name}' → '{new_name}'")
    if new_anime != old_anime:
        changes.append(f"anime: '{old_anime}' → '{new_anime}'")
    if new_rarity != old_rarity:
        changes.append(f"rarity: '{old_rarity}' → '{new_rarity}'")
    if photo_changed:
        changes.append("photo updated")
    log_admin_action(
        message.from_user.id, message.from_user.first_name,
        "EDIT CARD", f"ID: {card_id} — " + ("; ".join(changes) if changes else "no fields changed")
    )

    log_text = (
        "<b>「 DATABASE LOG : CARD EDITED ぁ 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 Card ID  ┊ <code>{card_id}</code>\n"
        f"👤 Name     ┊ <b>{new_name}</b>\n"
        f"📺 Anime    ┊ <b>{new_anime}</b>\n"
        f"🌟 Rarity   ┊ <b>{new_rarity}</b>\n"
        f"🔄 Synced   ┊ <b>{synced_owners}</b> existing owner(s)\n"
        "━━━━━━━━━━━━━━━━━━━"
    )
    
    msg_id = card_data.get("msg_id")
    if msg_id:
        try:
            if photo_changed:
                await bot.edit_message_media(
                    chat_id=DB_GROUP_ID,
                    message_id=msg_id,
                    media=InputMediaPhoto(media=new_file_id, caption=log_text, parse_mode=ParseMode.HTML)
                )
            else:
                await bot.edit_message_caption(
                    chat_id=DB_GROUP_ID,
                    message_id=msg_id,
                    caption=log_text,
                    parse_mode=ParseMode.HTML
                )
        except Exception as e:
            print(f"[EDIT_CARD] Failed to update group message: {e}")
            
    await message.reply(f"✅ Card <code>{card_id}</code> updated successfully!\n\n" + log_text, parse_mode=ParseMode.HTML)

# ==========================================
# /forcedrop IMPLEMENTATION
# ==========================================
@main_router.message(Command("forcedrop"))
async def force_drop_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    try: await message.delete()
    except Exception: pass

    db = load_db()
    if not db.get("global_cards"):
        await message.reply("⚠️ No cards in database. Use <code>/add_card</code> first.", parse_mode=ParseMode.HTML)
        return

    if message.chat.type == ChatType.PRIVATE:
        if not command.args:
            await message.reply(
                "<b>「 FORCE DROP ぁ 」</b>\n"
                "━━━━━━━━━━━━━━━━━━━\n"
                "In DM, provide the group ID:\n"
                "<code>/forcedrop -100XXXXXXXXXX</code>\n"
                "━━━━━━━━━━━━━━━━━━━",
                parse_mode=ParseMode.HTML
            )
            return
        try: target_chat = int(command.args.split()[0])
        except ValueError:
            await message.reply("⚠️ Invalid chat ID.", parse_mode=ParseMode.HTML)
            return
        await trigger_drop(target_chat)
        await message.reply(f"✅ Drop triggered in <code>{target_chat}</code>", parse_mode=ParseMode.HTML)
    else:
        await trigger_drop(message.chat.id)

# ==========================================
# SYSTEM METRICS AND AUDITING
# ==========================================
def get_botstats_content() -> tuple[str, InlineKeyboardMarkup]:
    db = load_db()
    sec = int(time.time() - bot_start_time)
    h, r = divmod(sec, 3600); m, s = divmod(r, 60)

    start_of_today = int(datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
    users_today = sum(1 for u in db["users"].values() if u.get("joined", 0) >= start_of_today)

    rarity_count = {}
    for c in db["global_cards"].values():
        normalized_rar = format_rarity(c["rarity"])
        rarity_count[normalized_rar] = rarity_count.get(normalized_rar, 0) + 1

    rarity_lines = []
    for i, rar in enumerate(RARITIES):
        prefix = "└" if i == len(RARITIES) - 1 else "├"
        rarity_lines.append(f"  {prefix} <b>{rar}:</b> <code>{rarity_count.get(rar, 0)}</code>")
    rarity_text = "\n".join(rarity_lines)

    total_shards_circulating = sum(u.get("nexus_shards", 0) for u in db["users"].values())
    total_cards_circulating = sum(
        card.get("amount", 0)
        for u in db["users"].values()
        for card in u.get("cards", {}).values()
    )

    text = (
        "<b>「 Bot Statistics 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        "<b>System</b>\n"
        f"  ├ Uptime: <code>{h}h {m}m {s}s</code>\n"
        f"  ├ Messages Processed: <code>{config.total_messages}</code>\n"
        f"  ├ Auto-Leave Guard: <code>{'Active' if config.autoleave_enabled else 'Inactive'}</code>\n"
        f"  └ New Users Today: <code>+{users_today}</code>\n\n"
        "<b>Database</b>\n"
        f"  ├ Registered Cards: <code>{len(db['global_cards'])}</code>\n"
        f"  ├ Total Users: <code>{len(db['users'])}</code>\n"
        f"  └ Total Groups: <code>{len(db['groups'])}</code>\n\n"
        "<b>Economy</b>\n"
        f"  ├ Shards in Circulation: <code>{total_shards_circulating:,}</code> 💠\n"
        f"  └ Cards in Circulation: <code>{total_cards_circulating:,}</code>\n\n"
        "<b>Rarity Distribution</b>\n"
        f"{rarity_text}\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Refresh", callback_data="refresh_botstats")],
        [InlineKeyboardButton(text="Close", callback_data="close_msg")]
    ])
    return text, kb

@main_router.message(Command("botstats"))
async def bot_stats(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    text, kb = get_botstats_content()
    await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)

@main_router.callback_query(F.data == "refresh_botstats")
async def refresh_botstats_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS: return
    text, kb = get_botstats_content()
    try:
        await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer("Statistics updated")

@main_router.message(Command("check_db_dupes"))
async def check_db_dupes(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    db = load_db()
    seen, dupes = {}, []
    for cid, data in db.get("global_cards",{}).items():
        key = (data["name"].lower().strip(), data["anime"].lower().strip())
        if key in seen: dupes.append((cid, data["name"], data["anime"], seen[key]))
        else: seen[key] = cid
    if not dupes:
        await message.reply("✅ No duplicates found.", parse_mode=ParseMode.HTML)
        return
    text = "<b>「 DUPES ぁ 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    for d in dupes[:15]: text += f"⚠️ <b>{d[1]}</b> ({d[2]})\n  ├ <code>{d[3]}</code>\n  └ <code>{d[0]}</code>\n"
    text += "...and more." if len(dupes) > 15 else "━━━━━━━━━━━━━━━━━━━"
    await message.reply(text, parse_mode=ParseMode.HTML)

# ==========================================
# /info PANEL CONTROLS AND PAGE ACTIONS
# ==========================================
def build_info_panel_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="👥 Users List", callback_data="infousers_0"),
            InlineKeyboardButton(text="🏘️ Groups List", callback_data="infogroups_0")
        ],
        [InlineKeyboardButton(text="✕ Close", callback_data="close_msg")]
    ])

@main_router.message(Command("info"))
async def info_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    db = load_db()
    
    if command.args:
        target = command.args.split()[0].strip()
        if target in db["users"]:
            u = db["users"][target]
            await message.reply(
                f"<b>「 👤 USER REGISTRY PROFILE 」</b>\n"
                f"━━━━━━━━━━━━━━━━━━━\n\n"
                f"<blockquote><i>Database record tracking profile indices.</i></blockquote>\n\n"
                f"• 🆔 <b>User ID:</b> <code>{target}</code>\n"
                f"• 👤 <b>Mention:</b> {get_mention(target, u.get('name','User'))}\n"
                f"• 🎴 <b>Unique Items:</b> <code>{len(u.get('cards',{}))}</code>\n"
                f"• 📦 <b>Accumulated Claims:</b> <code>{u.get('total_claimed',0)}</code>\n"
                f"• 👻 <b>Global Ban Filter:</b> <i>{'Flagged 🔴' if int(target) in config.ghost_banned else 'Clear 🟢'}</i>\n"
                f"• 🔇 <b>Shadow Mute Guard:</b> <i>{'Muted 🔴' if config.is_shadow_banned(int(target)) else 'Clear 🟢'}</i>\n"
                f"━━━━━━━━━━━━━━━━━━━", 
                parse_mode=ParseMode.HTML
            )
            return
        if target in db["groups"]:
            g = db["groups"][target]
            await message.reply(
                f"<b>「 🏘️ REGISTERED GROUP DETAILS 」</b>\n"
                f"━━━━━━━━━━━━━━━━━━━\n\n"
                f"• 🆔 <b>Group ID:</b> <code>{target}</code>\n"
                f"• 🏘️ <b>Title:</b> <b>{g.get('title','?')}</b>\n"
                f"• 🎴 <b>Spawned Drops:</b> <code>{g.get('drops',0)}</code>\n"
                f"• 🏆 <b>Executed Claims:</b> <code>{g.get('claims',0)}</code>\n"
                f"━━━━━━━━━━━━━━━━━━━", 
                parse_mode=ParseMode.HTML
            )
            return
        await message.reply(f"Target ID <code>{target}</code> is not registered.", parse_mode=ParseMode.HTML)
        return
        
    text = (
        f"<b>「 📊 DATABASE INFO PANEL ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"📊 <b>Total users:</b> <code>{len(db['users'])}</code>\n"
        f"🏘️ <b>Total groups:</b> <code>{len(db['groups'])}</code>\n\n"
        f"Select an index parameter below to explore stored database records."
    )
    await message.reply(text, reply_markup=build_info_panel_keyboard(), parse_mode=ParseMode.HTML)

@main_router.callback_query(F.data == "infopanel")
async def info_panel_back_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("Admin authentication required.", show_alert=True)
        return
    db = load_db()
    text = (
        f"<b>「 📊 DATABASE INFO PANEL ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"📊 <b>Total users:</b> <code>{len(db['users'])}</code>\n"
        f"🏘️ <b>Total groups:</b> <code>{len(db['groups'])}</code>\n\n"
        f"Select an index parameter below to explore stored database records."
    )
    await cq.message.edit_text(text, reply_markup=build_info_panel_keyboard(), parse_mode=ParseMode.HTML)
    await cq.answer()

@main_router.callback_query(F.data.startswith("infousers_"))
async def info_users_page_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("Admin authentication required.", show_alert=True)
        return
    page = int(cq.data.split("_")[1])
    db = load_db()
    users = sorted(db["users"].items(), key=lambda x: x[1].get("joined", 0), reverse=True)
    
    per_page = 10
    total = len(users)
    total_pages = max(1, (total - 1) // per_page + 1)
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start = page * per_page
    end = start + per_page
    sliced = users[start:end]
    
    text = f"<b>「 REGISTERED PLAYERS LIST (Page {page+1}/{total_pages}) 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    for idx, (uid, udata) in enumerate(sliced, start=start+1):
        mention = get_mention(uid, udata.get("name", "User"))
        username_str = f" (@{udata['username']})" if udata.get("username") else ""
        text += f"{idx}. {mention}{username_str} ➜ <code>{uid}</code>\n"
    text += "━━━━━━━━━━━━━━━━━━━"
    
    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"infousers_{page-1}"))
    if end < total:
        nav_buttons.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"infousers_{page+1}"))
        
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        nav_buttons,
        [InlineKeyboardButton(text="🏠 Back to Panel", callback_data="infopanel")],
        [InlineKeyboardButton(text="✕ Close", callback_data="close_msg")]
    ])
    
    await cq.message.edit_text(text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
    await cq.answer()

@main_router.callback_query(F.data.startswith("infogroups_"))
async def info_groups_page_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("Admin authentication required.", show_alert=True)
        return
    page = int(cq.data.split("_")[1])
    db = load_db()
    groups = sorted(db["groups"].items(), key=lambda x: x[1].get("joined", 0), reverse=True)
    
    per_page = 10
    total = len(groups)
    total_pages = max(1, (total - 1) // per_page + 1)
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start = page * per_page
    end = start + per_page
    sliced = groups[start:end]
    
    text = f"<b>「 REGISTERED GROUPS LIST (Page {page+1}/{total_pages}) 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    for idx, (gid, gdata) in enumerate(sliced, start=start+1):
        text += f"{idx}. <b>{gdata.get('title', 'Unknown')}</b> ➜ <code>{gid}</code>\n"
    text += "━━━━━━━━━━━━━━━━━━━"
    
    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"infogroups_{page-1}"))
    if end < total:
        nav_buttons.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"infogroups_{page+1}"))
        
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        nav_buttons,
        [InlineKeyboardButton(text="🏠 Back to Panel", callback_data="infopanel")],
        [InlineKeyboardButton(text="✕ Close", callback_data="close_msg")]
    ])
    
    await cq.message.edit_text(text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
    await cq.answer()

@main_router.message(Command("autoleave"))
async def autoleave_toggle(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args or command.args.lower() not in ["on", "off"]:
        await message.reply("⚠️ Usage: <code>/autoleave on</code> or <code>off</code>", parse_mode=ParseMode.HTML)
        return
    
    config.autoleave_enabled = (command.args.lower() == "on")
    db = load_db()
    db["settings"]["autoleave"] = config.autoleave_enabled
    save_db()
    await message.reply(f"🔄 Auto-leave: {'✅ ON' if config.autoleave_enabled else 'OFF'}\nMin: {config.AUTOLEAVE_MIN_MEMBERS} members", parse_mode=ParseMode.HTML)

# ==========================================
# RESTRICTION AND MODERATION CONTROLS
# ==========================================
async def _sban_target_blocked(uid: int, name: str, message: Message) -> str | None:
    """Checks whether an /sban or /sunban target is off-limits. Returns the
    HTML reply text to send if blocked, or None if the action may proceed.
    Checked in order: moderator -> channel -> bot, each with its own message."""

    if uid in ADMIN_IDS:
        return (
            "<b>⊘ ACTION DENIED</b>\n\n"
            "<b>Moderators are protected and cannot be shadow banned.</b>"
        )

    is_reply = bool(message.reply_to_message)

    # Anonymous channel posts (message sent "as" a linked channel)
    sender_chat = message.reply_to_message.sender_chat if is_reply else None
    if sender_chat and sender_chat.type == ChatType.CHANNEL:
        return (
            "<b>⊘ ACTION DENIED</b>\n\n"
            "<b>Channels cannot be shadow banned.</b>"
        )

    # Bots
    reply_user = message.reply_to_message.from_user if is_reply else None
    if reply_user and reply_user.is_bot:
        return (
            "<b>⊘ ACTION DENIED</b>\n\n"
            "<b>Bots cannot be shadow banned.</b>"
        )
    if not reply_user and isinstance(name, str) and name.lower().endswith("bot"):
        # Best-effort fallback for id/username based resolution, where a
        # full User object (with a reliable is_bot flag) isn't available.
        return (
            "<b>⊘ ACTION DENIED</b>\n\n"
            "<b>Bots cannot be shadow banned.</b>"
        )

    return None

@main_router.message(Command("gunban"))
async def global_unban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    uid, name = await resolve_target(command.args, message)
    if not uid:
        await message.reply("⚠️ <b>Format:</b> Reply to user or use:\n• <code>/gunban &lt;user_id&gt;</code>\n• <code>/gunban &lt;@username&gt;</code>", parse_mode=ParseMode.HTML)
        return

    if not is_ghost_banned(uid):
        await message.reply(f"⚠️ {get_mention(uid, name)} is not currently globally banned.", parse_mode=ParseMode.HTML)
        return

    config.ghost_banned.discard(uid)
    config.gban_meta.pop(uid, None)
    db = load_db()
    db["settings"]["ghost_banned"] = list(config.ghost_banned)
    db["settings"]["gban_meta"]    = {str(k): v for k, v in config.gban_meta.items()}
    save_db()

    # Trigger centralized logging to Topic 3
    await log_gunban_to_public(
        unbanned_uid=uid,
        unbanned_name=name,
        admin_uid=message.from_user.id,
        admin_name=message.from_user.first_name
    )

    await message.reply(f"✅ {get_mention(uid, name)} has been globally unbanned.", parse_mode=ParseMode.HTML)

@main_router.message(Command("gban"))
async def global_ban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    raw_args = (command.args or "").strip()
    is_reply = bool(message.reply_to_message and message.reply_to_message.from_user)

    if is_reply:
        uid  = message.reply_to_message.from_user.id
        name = message.reply_to_message.from_user.first_name
        remainder = raw_args
    else:
        if not raw_args:
            await message.reply(
                "⚠️ <b>Usage:</b>\n"
                "<code>/gban &lt;user_id | @username&gt; [reason] [duration]</code>\n"
                "Or reply to a user's message with <code>/gban [reason] [duration]</code>\n\n"
                "<b>Duration examples:</b> <code>30d</code>, <code>7h</code>, <code>45m</code>, <code>2w</code>, <code>permanent</code>\n"
                "If no reason is given it defaults to <b>None</b>. If no duration is given it defaults to <b>Permanent</b>.",
                parse_mode=ParseMode.HTML
            )
            return
        parts = raw_args.split(maxsplit=1)
        identifier = parts[0]
        remainder  = parts[1] if len(parts) > 1 else ""
        uid, name = await resolve_target(identifier, message)
        if not uid:
            await message.reply(f"⚠️ Could not resolve target <code>{identifier}</code>.", parse_mode=ParseMode.HTML)
            return

    # ── target immunity checks ──
    if uid == SUPREME_OWNER_ID:
        await message.reply(
            "<b>⊘ BAN FAILED</b>\n\n"
            "<b>Bold move... but the owner is untouchable.</b>",
            parse_mode=ParseMode.HTML
        )
        return

    if uid in ADMIN_IDS:
        await message.reply(
            "<b>⊘ ACTION DENIED</b>\n\n"
            "<b>Moderators are protected and cannot be banned.</b>",
            parse_mode=ParseMode.HTML
        )
        return

    # Process duration and reason tokens
    reason         = remainder
    duration_token = None
    if remainder:
        tokens = remainder.rsplit(maxsplit=1)
        parsed = parse_gban_duration_token(tokens[-1])
        if parsed is not None:
            duration_token = parsed
            reason = tokens[0] if len(tokens) > 1 else ""

    reason = reason.strip() or "None"
    is_permanent = duration_token is None or duration_token == "permanent"
    expires_at   = None if is_permanent else int(time.time()) + duration_token
    duration_display = "Permanent" if is_permanent else format_duration_seconds(duration_token)

    # Persist state
    config.ghost_banned.add(uid)
    config.gban_meta[uid] = {
        "reason": reason,
        "expires_at": expires_at,
        "banned_by": message.from_user.id,
        "banned_at": int(time.time())
    }
    db = load_db()
    db["settings"]["ghost_banned"] = list(config.ghost_banned)
    db["settings"]["gban_meta"]    = {str(k): v for k, v in config.gban_meta.items()}
    save_db()

    # Trigger centralized logging to Topic 3
    await log_gban_to_public(
        banned_uid=uid,
        banned_name=name,
        duration_str=duration_display,
        reason_str=reason,
        admin_uid=message.from_user.id,
        admin_name=message.from_user.first_name
    )

    await message.reply(
    f"<b>⊘ GLOBAL BAN ISSUED</b>\n\n"
    f"<b>Banned User:</b> {get_mention(uid, name)}\n"
    f"<b>Reason:</b> {reason}\n"
    f"<b>Duration:</b> {duration_display}",
    parse_mode=ParseMode.HTML
    )

@main_router.message(Command("sban"))
async def shadow_ban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    uid, name = await resolve_target(command.args, message)
    if not uid:
        await message.reply("⚠️ <b>Format:</b> Reply to user or use:\n• <code>/sban &lt;user_id&gt;</code>\n• <code>/sban &lt;@username&gt;</code>", parse_mode=ParseMode.HTML)
        return

    block_reason = await _sban_target_blocked(uid, name, message)
    if block_reason:
        await message.reply(block_reason, parse_mode=ParseMode.HTML)
        return

    existing_expiry = config.shadow_banned.get(uid)
    if existing_expiry and existing_expiry > time.time():
        remaining = format_duration_seconds(int(existing_expiry - time.time()))
        await message.reply(
            f"⚠️ {get_mention(uid, name)} is already shadow banned. ⏳ <b>Remaining:</b> {remaining}",
            parse_mode=ParseMode.HTML
        )
        return

    config.shadow_banned[uid] = time.time() + config.SHADOW_BAN_DUR
    db = load_db()
    db["settings"]["shadow_banned"] = config.shadow_banned
    save_db()

    admin_mention = get_mention(message.from_user.id, message.from_user.first_name)
    await send_log(
        f"<b>「 SHADOW BAN ISSUED 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"• 🎯 <b>Target:</b> {get_mention(uid, name)} (<code>{uid}</code>)\n"
        f"• ⏳ <b>Duration:</b> 10 minutes\n"
        f"• 🛡️ <b>Admin:</b> {admin_mention}\n"
        f"• 🕐 <b>Time:</b> {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )
    await message.reply(f"{get_mention(uid, name)} has been <b>shadow banned</b> for 10 minutes.", parse_mode=ParseMode.HTML)

@main_router.message(Command("sunban"))
async def shadow_unban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    uid, name = await resolve_target(command.args, message)
    if not uid:
        await message.reply("⚠️ <b>Format:</b> Reply to user or use:\n• <code>/sunban &lt;user_id&gt;</code>\n• <code>/sunban &lt;@username&gt;</code>", parse_mode=ParseMode.HTML)
        return

    block_reason = await _sban_target_blocked(uid, name, message)
    if block_reason:
        await message.reply(block_reason, parse_mode=ParseMode.HTML)
        return

    if uid not in config.shadow_banned:
        await message.reply(f"⚠️ {get_mention(uid, name)} is not currently shadow banned.", parse_mode=ParseMode.HTML)
        return

    config.shadow_banned.pop(uid, None)
    db = load_db()
    db["settings"]["shadow_banned"] = config.shadow_banned
    save_db()

    admin_mention = get_mention(message.from_user.id, message.from_user.first_name)
    await send_log(
        f"<b>「 SHADOW BAN LIFTED 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"• 🎯 <b>Target:</b> {get_mention(uid, name)} (<code>{uid}</code>)\n"
        f"• 🛡️ <b>Admin:</b> {admin_mention}\n"
        f"• 🕐 <b>Time:</b> {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )
    await message.reply(f"{get_mention(uid, name)} <b>shadow ban</b> restriction removed.", parse_mode=ParseMode.HTML)

@main_router.message(Command("sbans"))
async def shadow_bans_list(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    now = time.time()
    active_shadows = {uid: exp for uid, exp in config.shadow_banned.items() if exp > now}
    
    if not active_shadows:
        await message.reply("📝 Shadow Ban list is currently empty.", parse_mode=ParseMode.HTML)
        return
        
    db = load_db()
    text = "<b>「 SHADOW BANNED USERS 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    for idx, (uid, exp) in enumerate(active_shadows.items(), start=1):
        name = db["users"].get(str(uid), {}).get("name", "User")
        rem = int(exp - now)
        m, s = divmod(rem, 60)
        text += f"{idx}. {get_mention(uid, name)} ➜ <code>{uid}</code> (Rem: <b>{m}m {s}s</b>)\n"
    text += "━━━━━━━━━━━━━━━━━━━"
    await message.reply(text, parse_mode=ParseMode.HTML)

@main_router.message(Command("gbans"))
async def global_bans_list(message: Message):
    if message.from_user.id not in ADMIN_IDS: return

    now = time.time()
    # Calling is_ghost_banned() on each uid also auto-expires/cleans up any
    # entry whose duration has already lapsed, same as real enforcement does.
    active = [uid for uid in list(config.ghost_banned) if is_ghost_banned(uid)]

    if not active:
        await message.reply("📝 Global Ban list is currently empty.", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    text = "<b>「 👻 GLOBALLY BANNED USERS 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    for idx, uid in enumerate(active, start=1):
        name = db["users"].get(str(uid), {}).get("name", "User")
        meta = config.gban_meta.get(uid, {})
        reason = meta.get("reason", "None")
        expires_at = meta.get("expires_at")
        duration_display = f"{format_duration_seconds(int(expires_at - now))} left" if expires_at else "Permanent"
        text += f"{idx}. {get_mention(uid, name)} ➜ <code>{uid}</code>\n   └ Reason: {reason} | {duration_display}\n"
    text += "━━━━━━━━━━━━━━━━━━━"
    await message.reply(text, parse_mode=ParseMode.HTML)

def build_admin_help_text() -> str:
    """Builds the full admin help guide shown by /a_help."""
    return (
        "<b>「 🛡️ ADMIN SYSTEM HELP 」\n"
        "━━〔 ⟡ 管理指令 ⟡ 〕━━</b>\n\n"
        "<b>➷ /a_help\n〻 View this admin guide\n\n"
        "➷ /up [mode] (reply img)\n〻 Update interface images (st/hp/lb/sm/store/onst/offst)\n\n"
        "➷ /add_card Character|Anime|Rarity\n〻 Upload a new card image (reply to photo)\n\n"
        "➷ /edit_card DB-ID | Name | Anime | Rarity\n〻 Edit an existing card's details/image\n\n"
        "➷ /remove_card [ID]\n〻 Remove card from global db & GC\n\n"
        "➷ /forcedrop\n〻 Manually trigger a drop in chat\n\n"
        "➷ /backup\n〻 Force instant backup upload\n\n"
        "➷ /import (reply to file)\n〻 Import data from JSON DB\n\n"
        "➷ /eval [code]\n〻 Run raw Python executions and manipulate DB variables\n\n"
        "➷ /ping\n〻 Measure current engine latency [Admin Only]\n\n"
        "➷ /refresh\n〻 Perform a hard reload of process and script modules\n\n"
        "➷ /cleangroups\n〻 Clean database records for inactive/kicked chats\n\n"
        "➷ /info\n〻 Interactive DB player & group list\n\n"
        "➷ /check [ID / Name]\n〻 Interactively inspect user or global card profiles [Admin Only]\n\n"
        "➷ /cards\n〻 Browse global database [Admin Only]\n\n"
        "➷ /ab / /eb / /rb / /lbanner / /set_default / /lock_banner / /unlock_banner\n〻 Manage the profile banner pool [Admin Only]\n\n"
        "➷ /add_promo\n〻 Generate promo codes [Admin Only]\n\n"
        "➷ /list_promos\n〻 View all active promotional codes [Admin Only]\n\n"
        "➷ /del_promo [Code]\n〻 Delete an active promotional code [Admin Only]\n\n"
        "➷ /gban /gunban &lt;reply/id/@user&gt;\n〻 Restrict user globally\n\n"
        "➷ /gbans\n〻 List globally restricted users\n\n"
        "➷ /sban /sunban &lt;reply/id/@user&gt;\n〻 Mute user temporarily\n\n"
        "➷ /sbans\n〻 List muted users\n\n"
        "➷ /autoleave on|off\n〻 Toggle automated small group departure\n\n"
        "➷ /lock_drop &lt;anime name&gt;\n〻 Prevent a specific anime series from appearing in drops\n\n"
        "➷ /unlock_drop &lt;anime name&gt;\n〻 Re-enable drops for a previously locked anime series\n\n"
        "➷ /hide on|off &lt;anime name&gt;\n〻 Show/hide a series from the /cardlists browser\n\n"
        "➷ /hide status\n〻 List all anime series currently hidden from /cardlists\n\n"
        "➷ /bnxcast [mode] (reply to msg)\n〻 Broadcast/forward a message to users/groups/all</b>\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

# ==========================================
# BROADCAST SYSTEM (/bnxcast) [ADMIN ONLY]
# ==========================================
BNXCAST_USAGE = (
    "⚠️ <b>Usᴀɢᴇ:</b> Rᴇᴘʟʏ ᴛᴏ ᴀ ᴍᴇssᴀɢᴇ ᴡɪᴛʜ:\n"
    "<code>/bnxcast [mode]</code>\n\n"
    "<b>Mᴏᴅᴇs:</b>\n"
    "┣ <code>users</code> - Cᴏᴘʏ ᴛᴏ ᴀʟʟ ᴜsᴇʀs\n"
    "┣ <code>gcs</code> - Cᴏᴘʏ ᴛᴏ ᴀʟʟ ɢʀᴏᴜᴘs\n"
    "┣ <code>all</code> - Cᴏᴘʏ ᴛᴏ ᴇᴠᴇʀʏᴏɴᴇ\n"
    "┣ <code>fusers</code> - Fᴏʀᴡᴀʀᴅ ᴛᴏ ᴜsᴇʀs\n"
    "┣ <code>fgcs</code> - Fᴏʀᴡᴀʀᴅ ᴛᴏ ɢʀᴏᴜᴘs\n"
    "┗ <code>fall</code> - Fᴏʀᴡᴀʀᴅ ᴛᴏ ᴇᴠᴇʀʏᴏɴᴇ"
)
BNXCAST_MODES = {"users", "gcs", "all", "fusers", "fgcs", "fall"}

# 👈 FAST & SMART, WITHOUT STARVING OTHER COMMANDS:
# - The whole send loop runs as a detached background task (asyncio.create_task),
#   not awaited inside the command handler. The handler acks and returns
#   immediately, so the dispatcher is free to process every other update
#   (any command, any user) the instant it arrives — it's never stuck
#   waiting on this handler to finish.
# - A shared token-bucket rate limiter caps how many Telegram API calls the
#   broadcast itself issues per second (well under Telegram's ~30 msg/sec
#   global ceiling), leaving headroom in that global budget for whatever
#   other commands need to send at the same time. Concurrency alone
#   (workers) controls how many sends are in flight, not how fast Telegram
#   actually lets them through — the limiter is what keeps a big broadcast
#   from monopolizing that budget.
BNXCAST_CONCURRENCY = 25
BNXCAST_RATE_PER_SEC = 15         # broadcast's own share of Telegram's global rate limit
BNXCAST_PROGRESS_INTERVAL = 1.5   # seconds between live progress edits

_bnxcast_bg_tasks: set = set()    # keeps fire-and-forget tasks alive until done


class _RateLimiter:
    """Simple async token-bucket spacer: `await limiter.wait()` blocks just
    long enough that calls across ALL callers stay under `rate`/sec, no
    matter how many workers are hammering it at once."""
    def __init__(self, rate_per_sec: float):
        self._interval = 1.0 / rate_per_sec
        self._lock = asyncio.Lock()
        self._next_slot = 0.0

    async def wait(self):
        async with self._lock:
            now = time.monotonic()
            self._next_slot = max(self._next_slot, now) + self._interval
            delay = self._next_slot - now
        if delay > 0:
            await asyncio.sleep(delay)


async def _run_broadcast(status_msg, mode: str, forward: bool, target_ids: list,
                          src_chat_id: int, src_msg_id: int, src_reply_markup,
                          admin_id: int, admin_name: str):
    """The actual send loop — runs detached from the command handler (see
    broadcast_cmd) so it can take as long as it needs without ever blocking
    other commands from being handled in the meantime."""
    total = len(target_ids)
    sent = 0
    failed = 0
    done = 0
    counters_lock = asyncio.Lock()
    edit_lock = asyncio.Lock()
    sem = asyncio.Semaphore(BNXCAST_CONCURRENCY)
    limiter = _RateLimiter(BNXCAST_RATE_PER_SEC)
    last_edit = 0.0

    def _bar(pct: int, width: int = 12) -> str:
        filled = round(width * pct / 100)
        return "▰" * filled + "▱" * (width - filled)

    async def _maybe_update_progress(force: bool = False):
        nonlocal last_edit
        now = time.monotonic()
        if not force and (now - last_edit) < BNXCAST_PROGRESS_INTERVAL:
            return
        async with edit_lock:
            now = time.monotonic()
            if not force and (now - last_edit) < BNXCAST_PROGRESS_INTERVAL:
                return
            last_edit = now
            pct = int((done / total) * 100) if total else 100
            try:
                await status_msg.edit_text(
                    f"📡 <b>Broadcasting...</b> ({'Forward' if forward else 'Copy'})\n"
                    f"{_bar(pct)} <code>{pct}%</code>\n"
                    f"• Progress: <code>{done}/{total}</code>\n"
                    f"• ✅ Delivered: <code>{sent}</code>  •  Failed: <code>{failed}</code>",
                    parse_mode=ParseMode.HTML
                )
            except TelegramBadRequest:
                pass  # "message not modified" or similar — harmless
            except Exception:
                pass

    async def _send_one(raw_id):
        nonlocal sent, failed, done
        async with sem:
            try:
                chat_id_int = int(raw_id)
            except (TypeError, ValueError):
                async with counters_lock:
                    failed += 1
                    done += 1
                await _maybe_update_progress()
                return

            for attempt in range(2):
                await limiter.wait()  # 👈 shared throttle — other commands' sends aren't queued behind this
                try:
                    if forward:
                        await bot.forward_message(chat_id=chat_id_int, from_chat_id=src_chat_id, message_id=src_msg_id)
                    else:
                        # reply_markup passed explicitly so buttons/formatting carry over 1:1
                        await bot.copy_message(
                            chat_id=chat_id_int,
                            from_chat_id=src_chat_id,
                            message_id=src_msg_id,
                            reply_markup=src_reply_markup
                        )
                    async with counters_lock:
                        sent += 1
                    break
                except TelegramRetryAfter as e:
                    await asyncio.sleep(e.retry_after)
                    continue
                except (TelegramForbiddenError, TelegramBadRequest):
                    async with counters_lock:
                        failed += 1
                    break
                except Exception:
                    async with counters_lock:
                        failed += 1
                    break

            async with counters_lock:
                done += 1
            await _maybe_update_progress()

    t0 = time.monotonic()
    await asyncio.gather(*(_send_one(rid) for rid in target_ids))
    elapsed = time.monotonic() - t0
    await _maybe_update_progress(force=True)

    admin_mention = get_mention(admin_id, admin_name)
    try:
        await status_msg.edit_text(
            f"<b>「 📡 BROADCAST COMPLETE 」</b>\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"• 🧭 <b>Mode:</b> <code>{mode}</code>\n"
            f"• ✅ <b>Delivered:</b> <code>{sent}</code>\n"
            f"• <b>Failed:</b> <code>{failed}</code>\n"
            f"• 📦 <b>Total Targets:</b> <code>{total}</code>\n"
            f"• ⏱ <b>Time:</b> <code>{elapsed:.1f}s</code>\n"
            f"━━━━━━━━━━━━━━━━━━━",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass

    await send_log(
        f"<b>「 📡 BROADCAST EXECUTED 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"• 🛡️ <b>Admin:</b> {admin_mention}\n"
        f"• 🧭 <b>Mode:</b> <code>{mode}</code>\n"
        f"• ✅ <b>Delivered:</b> <code>{sent}</code> / <b>Failed:</b> <code>{failed}</code>\n"
        f"• ⏱ <b>Duration:</b> <code>{elapsed:.1f}s</code>\n"
        f"• 🕐 <b>Time:</b> {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )


@main_router.message(Command("bnxcast"))
async def broadcast_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    if not message.reply_to_message or not command.args:
        await message.reply(BNXCAST_USAGE, parse_mode=ParseMode.HTML)
        return

    mode = command.args.split()[0].strip().lower()
    if mode not in BNXCAST_MODES:
        await message.reply(BNXCAST_USAGE, parse_mode=ParseMode.HTML)
        return

    forward  = mode.startswith("f")
    base_mode = mode[1:] if forward else mode  # users / gcs / all

    db = load_db()
    target_ids = []
    if base_mode in ("users", "all"):
        target_ids += list(db["users"].keys())
    if base_mode in ("gcs", "all"):
        target_ids += list(db["groups"].keys())

    if not target_ids:
        await message.reply("No registered targets found for this mode.", parse_mode=ParseMode.HTML)
        return

    src_chat_id = message.chat.id
    src_msg_id  = message.reply_to_message.message_id
    # 👈 FIXED: bot.copy_message strips the inline keyboard unless it's
    # passed explicitly, so grab the source message's reply_markup (if any)
    # and re-attach it on every copy so buttons survive the broadcast.
    src_reply_markup = message.reply_to_message.reply_markup

    total = len(target_ids)
    status_msg = await message.reply(
        f"📡 <b>Broadcast started...</b>\n"
        f"Target: <code>{total}</code> chats ({'Forward' if forward else 'Copy'})\n"
        f"⚡ <code>{BNXCAST_CONCURRENCY}</code> parallel workers running in the background —"
        f" other commands stay responsive.",
        parse_mode=ParseMode.HTML
    )

    # 👈 Detached task: broadcast_cmd returns right here. The send loop keeps
    # running on its own; it never holds up this handler (or the dispatcher)
    # from picking up the next update/command.
    task = asyncio.create_task(_run_broadcast(
        status_msg, mode, forward, target_ids,
        src_chat_id, src_msg_id, src_reply_markup,
        message.from_user.id, message.from_user.first_name
    ))
    _bnxcast_bg_tasks.add(task)
    task.add_done_callback(_bnxcast_bg_tasks.discard)

@main_router.message(Command("a_help"))
async def admin_help_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    text = build_admin_help_text()
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="✕ Close", callback_data="close_msg")]])
    await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)

# ==========================================
# PROMOTIONAL CODES MANAGER (/add_promo) [ADMIN ONLY]
# ==========================================
@main_router.message(Command("add_promo"))
async def add_promo_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if uid_int not in ADMIN_IDS: return

    if not command.args:
        await message.reply(
            "⚠️ <b>Usage:</b>\n"
            "<code>/add_promo CODE max_claims reward1 [reward2] ...</code>\n\n"
            "<b>Reward String Formats:</b>\n"
            "• 💠 <b>Shards:</b> <code>shards:amount</code> (Example: <code>shards:500</code>)\n"
            "• 🎴 <b>Cards:</b> <code>card:Rarity:quantity</code> (Example: <code>card:Divine:1</code>)\n"
            "• 🖼️ <b>Banner:</b> <code>banner:amount:id</code> — <code>id</code> is a specific banner ID "
            "(see /lbanner) or <code>r</code> for a random non-default banner (Example: <code>banner:1:r</code>)\n\n"
            "<b>Multi-Gift Examples:</b>\n"
            "• <code>/add_promo WELCOME 100 shards:1000 card:Elite:1</code>\n"
            "• <code>/add_promo MEGA 50 shards:5000 card:Divine:2 card:Elite:1 banner:1:r</code>",
            parse_mode=ParseMode.HTML
        )
        return

    parts = command.args.split()
    if len(parts) < 3:
        await message.reply("⚠️ Invalid parameters. You must supply a Code, Claim Limit, and at least 1 Reward block.", parse_mode=ParseMode.HTML)
        return

    code = parts[0].upper().strip()
    try:
        max_claims = int(parts[1])
    except ValueError:
        await message.reply("⚠️ Max claims parameter must be an integer.", parse_mode=ParseMode.HTML)
        return

    rewards = []
    for r_str in parts[2:]:
        r_parts = r_str.split(":")
        if not r_parts: continue
        r_type = r_parts[0].lower().strip()
        
        if r_type == "shards":
            if len(r_parts) < 2:
                await message.reply(f"⚠️ Invalid format in shards block: <code>{r_str}</code>", parse_mode=ParseMode.HTML)
                return
            try:
                amt = int(r_parts[1])
                rewards.append({"type": "shards", "shards": amt})
            except ValueError:
                await message.reply(f"⚠️ Shard quantity in <code>{r_str}</code> must be an integer.", parse_mode=ParseMode.HTML)
                return
                
        elif r_type == "card":
            if len(r_parts) < 2:
                await message.reply(f"⚠️ Invalid format in card block: <code>{r_str}</code>", parse_mode=ParseMode.HTML)
                return
            rarity_raw = r_parts[1].strip()
            rarity_normalized = format_rarity(rarity_raw)
            if rarity_normalized not in RARITIES:
                await message.reply(f"⚠️ Invalid rarity in card block: <code>{r_str}</code>", parse_mode=ParseMode.HTML)
                return
            
            quantity = 1
            if len(r_parts) >= 3:
                try:
                    quantity = int(r_parts[2])
                except ValueError:
                    pass
            rewards.append({"type": "card", "rarity": rarity_normalized, "amount": quantity})

        elif r_type == "banner":
            if len(r_parts) < 3:
                await message.reply(
                    f"⚠️ Invalid format in banner block: <code>{r_str}</code>\n"
                    "Use <code>banner:amount:id</code> — <code>id</code> is a banner ID or <code>r</code> for random.",
                    parse_mode=ParseMode.HTML
                )
                return
            try:
                b_amount = int(r_parts[1])
            except ValueError:
                await message.reply(f"⚠️ Banner amount in <code>{r_str}</code> must be an integer.", parse_mode=ParseMode.HTML)
                return

            b_target = r_parts[2].strip().lower()
            db_peek = load_db()
            banners_pool = db_peek.get("banners", {})
            default_id_peek = db_peek.get("settings", {}).get("default_banner_id")

            if b_target != "r":
                if b_target not in banners_pool:
                    await message.reply(f"⚠️ No banner with ID <code>{b_target}</code>. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
                    return
                if b_target == default_id_peek:
                    await message.reply(
                        "⚠️ That banner is the current default — it's already free for everyone via /profile, "
                        "so it can't be used as a promo reward. Pick a different ID or use <code>r</code>.",
                        parse_mode=ParseMode.HTML
                    )
                    return
                if banners_pool[b_target].get("drop_locked"):
                    await message.reply(
                        f"⚠️ Banner <code>{b_target}</code> is locked from drops (/lock_banner) and can't be used as a "
                        "promo reward. Unlock it with /unlock_banner first, or pick a different ID.",
                        parse_mode=ParseMode.HTML
                    )
                    return
            else:
                if not [b for b, m in banners_pool.items() if b != default_id_peek and not m.get("drop_locked")]:
                    await message.reply("⚠️ No non-default, unlocked banners exist yet to randomly award. Add one with /ab first, or /unlock_banner an existing one.", parse_mode=ParseMode.HTML)
                    return

            rewards.append({"type": "banner", "amount": b_amount, "banner_id": b_target})

        else:
            await message.reply(f"⚠️ Unknown reward block type: <code>{r_str}</code>. Use <code>shards</code>, <code>card</code>, or <code>banner</code>.", parse_mode=ParseMode.HTML)
            return

    db = load_db()
    promos = db.setdefault("promos", {})
    
    promos[code] = {
        "rewards": rewards,
        "max_claims": max_claims,
        "claimed_by": []
    }
    save_db()

    reward_descriptions = []
    for r in rewards:
        if r["type"] == "shards":
            reward_descriptions.append(f"• 💠 <b>Nexus Shards:</b> +{r['shards']}")
        elif r["type"] == "banner":
            target_desc = "Random (non-default)" if r["banner_id"] == "r" else f"ID {r['banner_id']}"
            reward_descriptions.append(f"• 🖼️ <b>Banner:</b> x{r['amount']} ({target_desc})")
        else:
            reward_descriptions.append(f"• 🎴 <b>[{r['rarity']}] Cards:</b> x{r['amount']}")

    desc_text = "\n".join(reward_descriptions)
    await message.reply(
        f"✅ <b>Promo Code Added</b>\n"
        f"🎫 Code: <code>{code}</code>\n"
        f"👥 Max Claims Allowed: <b>{max_claims}</b>\n\n"
        f"📦 <b>Bundled Rewards:</b>\n{desc_text}",
        parse_mode=ParseMode.HTML
    )

# ==========================================
# PROMOTIONAL CODES AUDITOR (/list_promos) [ADMIN ONLY]
# ==========================================
@main_router.message(Command("list_promos"))
async def list_promos_cmd(message: Message):
    uid_int = message.from_user.id
    if uid_int not in ADMIN_IDS: return

    db = load_db()
    promos = db.setdefault("promos", {})

    if not promos:
        await message.reply("📝 No promotional codes are currently active.", parse_mode=ParseMode.HTML)
        return

    text = "<b>「 🎫 ACTIVE PROMO CODES 」</b>\n━━━━━━━━━━━━━━━━━━━\n\n"
    for idx, (code, data) in enumerate(promos.items(), start=1):
        claimed = len(data.get("claimed_by", []))
        limit = data.get("max_claims", 0)
        
        rewards_summary = []
        if "rewards" in data:
            for r in data["rewards"]:
                if r["type"] == "shards":
                    rewards_summary.append(f"💠 {r['shards']} Shards")
                elif r["type"] == "banner":
                    target_desc = "Random" if r.get("banner_id") == "r" else f"ID {r.get('banner_id')}"
                    rewards_summary.append(f"🖼️ x{r['amount']} Banner ({target_desc})")
                else:
                    rewards_summary.append(f"🎴 x{r['amount']} {r['rarity']}")
        else:
            if data.get("type") == "shards":
                rewards_summary.append(f"💠 {data.get('shards', 0)} Shards")
            else:
                rewards_summary.append(f"🎴 x{data.get('amount', 1)} {data.get('rarity')}")
                
        payouts_desc = ", ".join(rewards_summary)
        text += f"{idx}. 🎫 <code>{code}</code> ➜ [{payouts_desc}]\n   └ Claims Status: <b>{claimed}/{limit}</b>\n\n"
        
    text += "━━━━━━━━━━━━━━━━━━━"
    await message.reply(text, parse_mode=ParseMode.HTML)

# ==========================================
# PROMOTIONAL CODES DESTROYER (/del_promo) [ADMIN ONLY]
# ==========================================
@main_router.message(Command("del_promo"))
async def del_promo_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if uid_int not in ADMIN_IDS: return

    if not command.args:
        await message.reply("⚠️ Usage: <code>/del_promo CODE</code>\nExample: <code>/del_promo GOLD</code>", parse_mode=ParseMode.HTML)
        return

    code = command.args.upper().strip()
    db = load_db()
    promos = db.setdefault("promos", {})

    if code not in promos:
        await message.reply(f"Promo code <code>{code}</code> does not exist.", parse_mode=ParseMode.HTML)
        return

    del promos[code]
    save_db()
    await message.reply(f"🗑️ Promotional code <code>{code}</code> has been deleted and invalidated.", parse_mode=ParseMode.HTML)


# ==========================================
# GLOBAL DB BROWSER LOGIC & PAGES (/cards)
# ==========================================
async def show_anime_list(event, edit=False, page=0):
    db = load_db()
    cards = db.get("global_cards", {})
    anime_titles = sorted(list(set(c["anime"] for c in cards.values())))
    
    if not anime_titles:
        text = "<b>「 GLOBAL DATABASE EMPTY 」</b>\n━━━━━━━━━━━━━━━━━━━\nNo cards are registered yet."
        if edit and isinstance(event, CallbackQuery):
            await event.message.edit_text(text, parse_mode=ParseMode.HTML)
        else:
            target = event.message if isinstance(event, CallbackQuery) else event
            await target.reply(text, parse_mode=ParseMode.HTML)
        return

    per_page = 10
    total = len(anime_titles)
    total_pages = max(1, (total - 1) // per_page + 1)
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start = page * per_page
    end = min(start + per_page, total)
    sliced = anime_titles[start:end]

    # ── Detailed rarity breakdown across the ENTIRE card pool (not just
    # the current page) — total unique cards AND total copies in
    # circulation, per rarity tier, so admins can see the pool's shape
    # at a glance every time /cards is opened.
    rarity_unique_counts = {r: 0 for r in RARITIES}
    rarity_circulation_counts = {r: 0 for r in RARITIES}
    for cid, cdata in cards.items():
        r = format_rarity(cdata["rarity"])
        if r not in rarity_unique_counts:
            continue  # unknown/legacy rarity string, skip rather than crash
        rarity_unique_counts[r] += 1

    users = db.get("users", {})
    for u_data in users.values():
        for cid, holding in u_data.get("cards", {}).items():
            cdata = cards.get(cid)
            if not cdata:
                continue
            r = format_rarity(cdata["rarity"])
            if r not in rarity_circulation_counts:
                continue
            rarity_circulation_counts[r] += holding.get("amount", 0)

    breakdown_lines = "\n".join(
        f"  {r}  —  <code>{rarity_unique_counts[r]}</code> unique  ┊  <code>{rarity_circulation_counts[r]}</code> in circulation"
        for r in RARITIES
    )
    
    text = (
        f"<b>「 📺 GLOBAL CARD BROWSER 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"<b>📊 Rarity Breakdown:</b>\n"
        f"{breakdown_lines}\n"
        f"  🎴 <b>Total Unique Cards:</b> <code>{len(cards)}</code>\n"
        f"  📺 <b>Total Anime Series:</b> <code>{total}</code>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"Select an anime to view its registered card pool:\n\n"
    )
    
    locked_animes = {a.lower() for a in db.get("settings", {}).get("locked_animes", [])}

    buttons = []
    row = []
    for idx, anime in enumerate(sliced, start=start+1):
        is_locked = anime.lower() in locked_animes
        lock_tag  = " 🔒" if is_locked else ""
        text += f"<b>{idx})</b> {anime}{lock_tag}\n"
        # FIXED: previously did anime.replace("|","¦")[:35] which SILENTLY
        # TRUNCATES any anime title longer than 35 characters (e.g. "The
        # Angel Next Door Spoils Me Rotten" is 36 chars). The truncated
        # name then failed exact-match lookups further down the chain,
        # producing the "broken name" / card-not-found bug. Now we use a
        # short stable hash as the callback key instead of the name itself
        # — callback_data stays tiny regardless of title length, and the
        # full, untruncated name is recovered via anime_key_lookup().
        anime_key = anime_hash_key(anime)
        button_label = f"🔒 {idx}" if is_locked else f"{idx}"
        row.append(InlineKeyboardButton(text=button_label, callback_data=f"an|{anime_key}"))
        if len(row) == 5:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    
    text += f"\n━━━━━━━━━━━━━━━━━━━\nPage <b>{page+1}/{total_pages}</b>"
    
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"anlist_page_{page-1}"))
    if end < total:
        nav.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"anlist_page_{page+1}"))
    
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton(text="✕ Close", callback_data="close_msg")])
    
    markup = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    if edit and isinstance(event, CallbackQuery):
        try:
            await event.message.edit_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)
        except Exception:
            pass
    else:
        target = event.message if isinstance(event, CallbackQuery) else event
        await target.reply(text, reply_markup=markup, parse_mode=ParseMode.HTML)


@main_router.message(Command("cards"))
async def cards_browse_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    await show_anime_list(message)


@main_router.callback_query(F.data.startswith("anlist_page_"))
async def anime_list_page_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("⚠️ Admin restricted.", show_alert=True)
        return
    page = int(cq.data.split("_")[2])
    await cq.answer()
    await show_anime_list(cq, edit=True, page=page)


# ==========================================
# UNIVERSAL INSPECTOR (/check) [ADMIN ONLY]
# ==========================================
@main_router.message(Command("check"))
async def check_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    
    if not command.args:
        await message.reply(
            "⚠️ <b>Usage:</b>\n"
            "• <code>/check &lt;user_id / @username&gt;</code> - Inspect user profile\n"
            "• <code>/check &lt;card name&gt;</code> - Inspect global card details\n"
            "• Or reply to a user message with <code>/check</code>", 
            parse_mode=ParseMode.HTML
        )
        return

    query = command.args.strip()
    db = load_db()

    # 1. Inspect User Path
    uid, name = await resolve_target(query, message)
    if uid and str(uid) in db["users"]:
        u_data = db["users"][str(uid)]
        cards = u_data.get("cards", {})

        # Banner ownership + selection — mirrors get_active_banner_id()'s
        # precedence (personal pick, only if still owned & on disk, else
        # the global default) so this matches what the user's /profile
        # actually shows.
        owned_banners = {bid: m for bid, m in u_data.get("banners", {}).items() if m.get("amount", 0) > 0}
        active_banner_id = get_active_banner_id(db, uid)
        all_banners_db = db.get("banners", {})
        default_id = db.get("settings", {}).get("default_banner_id")

        if active_banner_id and active_banner_id in all_banners_db:
            active_name = all_banners_db[active_banner_id].get("name", "Unnamed")
            source = "personal pick" if active_banner_id == u_data.get("current_banner_id") else "server default"
            banner_line = f"<code>{active_banner_id}</code> ┊ {active_name} ({source})"
        else:
            banner_line = "None"

        text = (
            f"<b>「 👤 USER REGISTRY PROFILE 」</b>\n"
            f"━━━━━━━━━━━━━━━━━━━\n\n"
            f"<blockquote><i>Database record tracking profile indices.</i></blockquote>\n\n"
            f"• 🆔 <b>User ID:</b> <code>{uid}</code>\n"
            f"• 👤 <b>Mention:</b> {get_mention(uid, name)}\n"
            f"• 🎴 <b>Unique Items:</b> <code>{len(cards)}</code>\n"
            f"• 📦 <b>Claims:</b> <code>{u_data.get('total_claimed', 0)}</code>\n"
            f"• 💠 <b>Shards:</b> <code>{u_data.get('nexus_shards', 0)}</code>\n"
            f"• 🖼️ <b>Active Banner:</b> {banner_line}\n"
            f"• 🎨 <b>Banners Owned:</b> <code>{len(owned_banners)}</code>\n"
            f"• 👻 <b>Global Ban:</b> <i>{'Flagged 🔴' if int(uid) in config.ghost_banned else 'Clear 🟢'}</i>\n"
            f"• 🔇 <b>Shadow Mute:</b> <i>{'Muted 🔴' if config.is_shadow_banned(int(uid)) else 'Clear 🟢'}</i>\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )

        if owned_banners:
            text += "\n\n<b>🖼️ Owned Banners:</b>\n"
            for bid, meta in sorted(owned_banners.items(), key=lambda x: int(x[0])):
                bname = all_banners_db.get(bid, {}).get("name", "Unknown/Removed")
                marker = " ★" if bid == u_data.get("current_banner_id") else ""
                text += f" • <code>{bid}</code> ┊ {bname} x{meta.get('amount', 0)}{marker}\n"

        if cards:
            text += "\n\n<b>🎴 Sample Inventory:</b>\n"
            sorted_cards = sorted(cards.items(), key=lambda x: format_rarity(x[1]["rarity"]))
            for cid, cdata in sorted_cards[:15]:
                rar = format_rarity(cdata["rarity"])
                text += f" • <b>{cdata['name']}</b> ({rar}) x{cdata['amount']}\n"
            if len(sorted_cards) > 15:
                text += f" <i>...and {len(sorted_cards) - 15} more unique cards.</i>"
                
        await message.reply(text, parse_mode=ParseMode.HTML)
        return

    # 2. Inspect Card Path (Fuzzy Matching)
    query_lower = query.lower()
    global_cards = db.get("global_cards", {})
    
    best_match = None
    best_ratio = 0.0

    for cid, cdata in global_cards.items():
        name_lower = cdata["name"].lower()
        if query_lower == name_lower:
            best_match = (cid, cdata)
            break
        if query_lower in name_lower:
            ratio = 0.8 + (len(query_lower) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)
        else:
            ratio = difflib.SequenceMatcher(None, query_lower, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)

    if best_match:
        cid, cdata = best_match
        display_rarity = format_rarity(cdata["rarity"])
        
        owners_count = sum(1 for u in db["users"].values() if cid in u.get("cards", {}))
        total_copies = sum(u.get("cards", {}).get(cid, {}).get("amount", 0) for u in db["users"].values())

        card_text = (
            f"<b>「 🎴 CARD REFERENCE LOOKUP 」</b>\n"
            f"━━━━━━━━━━━━━━━━━━━\n\n"
            f"• 🆔 <b>Card ID:</b> <code>{cid}</code>\n"
            f"• 👤 <b>Name:</b> <b>{cdata['name']}</b>\n"
            f"• 📺 <b>Anime:</b> <i>{cdata.get('anime', 'Unknown')}</i>\n"
            f"• 🌟 <b>Rarity:</b> <b>{display_rarity}</b>\n"
            f"• 👥 <b>Unique Owners:</b> <code>{owners_count}</code> players\n"
            f"• 📦 <b>Circulation:</b> <code>{total_copies} copies</code>\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )
        
        try:
            await message.reply_photo(photo=cdata["file_id"], caption=card_text, parse_mode=ParseMode.HTML)
        except Exception:
            await message.reply(card_text, parse_mode=ParseMode.HTML)
        return

    await message.reply(
        f"No registered users or card titles match the query: <b>{query}</b>.", 
        parse_mode=ParseMode.HTML
    )




@main_router.callback_query(F.data.startswith("an|"))
async def anime_rarity_picker(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): 
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return

    if uid_int not in ADMIN_IDS:
        await cq.answer("⚠️ Restricted to administrators.", show_alert=True)
        return 
        
    anime_key = cq.data.split("|")[1]
    db = load_db()
    anime_name = anime_key_lookup(db, anime_key)
    if not anime_name:
        await cq.answer("This anime no longer exists in the database (titles may have changed). Please reopen /cards.", show_alert=True)
        return

    locked_animes = {a.lower() for a in db.get("settings", {}).get("locked_animes", [])}
    is_locked = anime_name.lower() in locked_animes
    lock_line = "\n🔒 <i>Drops are currently locked for this series.</i>" if is_locked else ""

    text = f"<b>「 📺 {anime_name} 」</b>\n━━━━━━━━━━━━━━━━━━━{lock_line}\nSelect a rarity filter to browse cards:"
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❄️ Divine", callback_data=f"crd|{anime_key}|divine|0")],
        [InlineKeyboardButton(text="⚓ Elite", callback_data=f"crd|{anime_key}|elite|0")],
        [InlineKeyboardButton(text="🃏 Basic", callback_data=f"crd|{anime_key}|basic|0")],
        [InlineKeyboardButton(text="🌟 All Rarities", callback_data=f"crd|{anime_key}|all|0")],
        [InlineKeyboardButton(text="◀️ Back to Anime List", callback_data="anlist_page_0")],
        [InlineKeyboardButton(text="✕ Close", callback_data="close_msg")]
    ])
    
    try:
        await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()

@main_router.callback_query(F.data.startswith("crd|"))
async def browse_filtered_cards(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    if uid_int not in ADMIN_IDS:
        await cq.answer("⚠️ Restricted.", show_alert=True)
        return

    # Parse the callback data
    parts = cq.data.split("|")
    anime_key = parts[1]
    rarity_filter = parts[2]
    page = int(parts[3])

    db = load_db()
    anime_name = anime_key_lookup(db, anime_key)
    if not anime_name:
        await cq.answer("This anime no longer exists in the database. Please reopen /cards.", show_alert=True)
        return

    all_cards = db.get("global_cards", {})
    
    # Apply filters
    filtered_cards = []
    for cid, c in all_cards.items():
        if c["anime"] == anime_name:
            if rarity_filter == "all":
                filtered_cards.append((cid, c))
            else:
                # Compare against the safe mapping from config
                r_safe = RARITY_SAFE.get(format_rarity(c["rarity"]))
                if r_safe == rarity_filter:
                    filtered_cards.append((cid, c))
                    
    if not filtered_cards:
        await cq.answer("No cards found for this rarity.", show_alert=True)
        return

    # Calculate pagination bounds
    per_page = BROWSE_PER_PAGE
    total = len(filtered_cards)
    total_pages = max(1, (total - 1) // per_page + 1)
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start = page * per_page
    end = start + per_page
    sliced = filtered_cards[start:end]

    # Build the display string
    disp_rarity = rarity_filter.title() if rarity_filter != "all" else "All Rarities"
    text = f"<b>「 📺 {anime_name} - {disp_rarity} 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
    
    for idx, (cid, c) in enumerate(sliced, start=start+1):
        text += f"{idx}. <b>{c['name']}</b> ({format_rarity(c['rarity'])})\n"
        
    text += f"━━━━━━━━━━━━━━━━━━━\nPage <b>{page+1}/{total_pages}</b>"
    
    # Build navigation matrix
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"crd|{anime_key}|{rarity_filter}|{page-1}"))
    if end < total:
        nav_row.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"crd|{anime_key}|{rarity_filter}|{page+1}"))
        
    kb_layout = []
    if nav_row:
        kb_layout.append(nav_row)
    kb_layout.append([InlineKeyboardButton(text="🔙 Back to Rarities", callback_data=f"an|{anime_key}")])
    kb_layout.append([InlineKeyboardButton(text="✕ Close", callback_data="close_msg")])
    
    kb = InlineKeyboardMarkup(inline_keyboard=kb_layout)
    
    try:
        await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()

# ==========================================
# /lock_drop AND /unlock_drop CONTROLS
# ==========================================
# Series-level only: locks/unlocks a whole anime series, stored in
# settings["locked_animes"]. Individual cards can't be locked. Banners have
# their own commands: /lock_banner and /unlock_banner (see banners.py).
@main_router.message(Command("lock_drop"))
async def lock_drop_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args or not command.args.strip():
        await message.reply("⚠️ <b>Usage:</b> <code>/lock_drop &lt;anime series name&gt;</code>", parse_mode=ParseMode.HTML)
        return

    anime_name = command.args.strip()
    db = load_db()

    # Verify the anime actually exists in DB card records
    anime_lower = anime_name.lower().strip()
    db_anime_name = None
    for c in db.get("global_cards", {}).values():
        if c["anime"].lower().strip() == anime_lower:
            db_anime_name = c["anime"]
            break

    if not db_anime_name:
        await message.reply("Anime not found in the database.", parse_mode=ParseMode.HTML)
        return

    if "settings" not in db:
        db["settings"] = {}
    if "locked_animes" not in db["settings"]:
        db["settings"]["locked_animes"] = []

    locked = db["settings"]["locked_animes"]
    if any(a.lower() == anime_lower for a in locked):
        await message.reply(f"⚠️ <b>{db_anime_name}</b> is already locked from dropping.", parse_mode=ParseMode.HTML)
        return

    locked.append(db_anime_name)
    save_db(db)
    await perform_backup()
    log_admin_action(message.from_user.id, message.from_user.first_name, "LOCK DROP", db_anime_name)
    await message.reply(f"🔒 <b>{db_anime_name}</b> drops have been locked successfully!", parse_mode=ParseMode.HTML)


@main_router.message(Command("unlock_drop"))
async def unlock_drop_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return
    if not command.args or not command.args.strip():
        await message.reply("⚠️ <b>Usage:</b> <code>/unlock_drop &lt;anime series name&gt;</code>", parse_mode=ParseMode.HTML)
        return

    anime_name = command.args.strip()
    db = load_db()

    if "settings" not in db:
        db["settings"] = {}
    if "locked_animes" not in db["settings"]:
        db["settings"]["locked_animes"] = []

    locked = db["settings"]["locked_animes"]
    anime_lower = anime_name.lower().strip()

    # Verify the anime name exists in the DB to give better feedback
    db_anime_name = None
    for c in db.get("global_cards", {}).values():
        if c["anime"].lower().strip() == anime_lower:
            db_anime_name = c["anime"]
            break

    if not db_anime_name:
        await message.reply("Anime not found in the database.", parse_mode=ParseMode.HTML)
        return

    found = False
    for item in list(locked):
        if item.lower() == anime_lower:
            locked.remove(item)
            found = True

    if not found:
        await message.reply(f"⚠️ <b>{db_anime_name}</b> is not currently locked.", parse_mode=ParseMode.HTML)
        return

    save_db(db)
    await perform_backup()
    log_admin_action(message.from_user.id, message.from_user.first_name, "UNLOCK DROP", db_anime_name)
    await message.reply(f"🔓 <b>{db_anime_name}</b> drops have been unlocked successfully!", parse_mode=ParseMode.HTML)


# ==========================================
# /hide — HIDE ANIME SERIES FROM /cardlists [ADMIN ONLY]
# Independent of /lock_drop (which only affects the drop pool). A hidden
# anime simply doesn't show up in the /cardlists anime browser; the cards
# themselves, drops, and everything else are untouched.
# ==========================================
HIDE_USAGE = (
    "⚠️ <b>Usage:</b>\n"
    "<code>/hide on &lt;anime series name&gt;</code>\n"
    "<code>/hide off &lt;anime series name&gt;</code>\n"
    "<code>/hide status</code>"
)


@main_router.message(Command("hide"))
async def hide_anime_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    args = (command.args or "").strip()
    if not args:
        await message.reply(HIDE_USAGE, parse_mode=ParseMode.HTML)
        return

    parts = args.split(maxsplit=1)
    mode = parts[0].lower()

    db = load_db()
    if "settings" not in db:
        db["settings"] = {}
    if "hidden_animes" not in db["settings"]:
        db["settings"]["hidden_animes"] = []
    hidden = db["settings"]["hidden_animes"]

    # ── /hide status ──────────────────────────────────────────────
    if mode == "status":
        if not hidden:
            await message.reply("👁️ No anime series are currently hidden from /cardlists.", parse_mode=ParseMode.HTML)
            return
        text = "<b>「 🙈 HIDDEN FROM /cardlists 」</b>\n━━━━━━━━━━━━━━━━━━━\n"
        for idx, anime in enumerate(hidden, start=1):
            text += f"{idx}. {anime}\n"
        text += "━━━━━━━━━━━━━━━━━━━"
        await message.reply(text, parse_mode=ParseMode.HTML)
        return

    # ── /hide on|off <anime> ─────────────────────────────────────
    if mode not in ("on", "off"):
        await message.reply(HIDE_USAGE, parse_mode=ParseMode.HTML)
        return

    if len(parts) < 2 or not parts[1].strip():
        await message.reply(HIDE_USAGE, parse_mode=ParseMode.HTML)
        return

    anime_name = parts[1].strip()
    anime_lower = anime_name.lower().strip()

    # Verify the anime actually exists in DB card records
    db_anime_name = None
    for c in db.get("global_cards", {}).values():
        if c["anime"].lower().strip() == anime_lower:
            db_anime_name = c["anime"]
            break

    if not db_anime_name:
        await message.reply("Anime not found in the database.", parse_mode=ParseMode.HTML)
        return

    if mode == "on":
        if any(a.lower() == anime_lower for a in hidden):
            await message.reply(f"⚠️ <b>{db_anime_name}</b> is already hidden from /cardlists.", parse_mode=ParseMode.HTML)
            return
        hidden.append(db_anime_name)
        save_db(db)
        await perform_backup()
        await message.reply(f"🙈 <b>{db_anime_name}</b> is now hidden from /cardlists.", parse_mode=ParseMode.HTML)
    else:
        found = False
        for item in list(hidden):
            if item.lower() == anime_lower:
                hidden.remove(item)
                found = True
        if not found:
            await message.reply(f"⚠️ <b>{db_anime_name}</b> is not currently hidden.", parse_mode=ParseMode.HTML)
            return
        save_db(db)
        await perform_backup()
        await message.reply(f"👁️ <b>{db_anime_name}</b> is now visible in /cardlists again.", parse_mode=ParseMode.HTML)


# ==========================================
# SUPPORT QUERY SYSTEM — ADMIN SIDE (/aq, /nansq)
# Submission (/qry) lives in handlers.py. This answers tickets and lists
# unanswered ones. Ticket data lives in db["queries"][qry_id].
# ==========================================
def _find_query(db: dict, raw_id: str):
    """Case-insensitive lookup of a query ticket ID. Returns (id, data) or (None, None)."""
    target = raw_id.strip().upper()
    for qid, qdata in db.get("queries", {}).items():
        if qid.upper() == target:
            return qid, qdata
    return None, None


@main_router.message(Command("aq"))
async def answer_query_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    args = (command.args or "").strip()
    if not args:
        await message.reply("<b>Format:</b> <code>/aq Qry01 your answer text</code>\nOr reply to a text message with <code>/aq Qry01</code>.", parse_mode=ParseMode.HTML)
        return

    parts = args.split(maxsplit=1)
    raw_id = parts[0]
    answer_text = parts[1].strip() if len(parts) > 1 else ""

    if not answer_text:
        # Fall back to using the text of the message being replied to.
        reply_msg = message.reply_to_message
        if reply_msg:
            answer_text = (reply_msg.text or reply_msg.caption or "").strip()

    if not answer_text:
        await message.reply("<b>Format:</b> <code>/aq Qry01 your answer text</code>\nOr reply to a text message with <code>/aq Qry01</code>.", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    qry_id, qdata = _find_query(db, raw_id)
    if not qdata:
        await message.reply(f"<b>Query not found:</b> <code>{raw_id.strip().upper()}</code>", parse_mode=ParseMode.HTML)
        return

    if qdata.get("status") == "answered":
        answered_by = qdata.get("answered_by")
        answerer_mention = get_mention(answered_by, "Admin") if answered_by else "an admin"
        safe_prev_answer = str(qdata.get("answer", "")).replace("<", "&lt;").replace(">", "&gt;")
        await message.reply(
            f"<b>{qry_id} is already answered</b> by {answerer_mention}.\n\n"
            f"<b>Existing answer:</b>\n<blockquote>{safe_prev_answer}</blockquote>",
            parse_mode=ParseMode.HTML
        )
        return

    qdata["status"] = "answered"
    qdata["answer"] = answer_text
    qdata["answered_by"] = message.from_user.id
    qdata["answered_at"] = int(time.time())
    save_db()

    asker_id = qdata["user_id"]
    safe_question = qdata["question"].replace("<", "&lt;").replace(">", "&gt;")
    safe_answer = answer_text.replace("<", "&lt;").replace(">", "&gt;")

    dm_text = (
        "<b><u>Query answered</u></b>\n\n"
        f"🎫 <b>Ticket:</b> {qry_id}\n"
        f"<b>Your Ques❓:</b>\n"
        f"<blockquote>{safe_question}</blockquote>\n\n"
        f"<b>Answer:</b>\n{safe_answer}"
    )

    dm_failed = False
    try:
        await bot.send_message(chat_id=int(asker_id), text=dm_text, parse_mode=ParseMode.HTML)
    except Exception:
        dm_failed = True

    # --- Single merged confirmation ---
    admin_mention = get_mention(message.from_user.id, message.from_user.first_name)
    if dm_failed:
        confirm_text = f"<b>{qry_id}</b> answered by {admin_mention}.\n<b>Couldn't DM the user</b> (they may have blocked the bot)."
    else:
        confirm_text = f"<b>{qry_id}</b> answered by {admin_mention}.\n<b>Answer sent to the user.</b>"

    log_msg_id = qdata.get("log_msg_id")
    if message.chat.id == QUERY_GROUP_ID and log_msg_id:
        # Already in the ticket group — thread the single confirmation onto the original log message.
        try:
            await bot.send_message(chat_id=QUERY_GROUP_ID, text=confirm_text, parse_mode=ParseMode.HTML, reply_to_message_id=log_msg_id)
        except Exception:
            await message.reply(confirm_text, parse_mode=ParseMode.HTML)
    else:
        # Answered from elsewhere (DM/another chat) — confirm to the admin here,
        # and separately notify the ticket group once since they won't see this reply.
        await message.reply(confirm_text, parse_mode=ParseMode.HTML)
        if log_msg_id:
            try:
                await bot.send_message(chat_id=QUERY_GROUP_ID, text=confirm_text, parse_mode=ParseMode.HTML, reply_to_message_id=log_msg_id)
            except Exception:
                pass


def _query_group_link(msg_id: int):
    """Builds a t.me/c/... deep link to a message inside the (private) query group."""
    if not msg_id:
        return None
    gid = str(QUERY_GROUP_ID)
    if gid.startswith("-100"):
        return f"https://t.me/c/{gid[4:]}/{msg_id}"
    return None


@main_router.message(Command("nansq"))
async def unanswered_queries_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return

    db = load_db()
    pending = [
        (qid, qdata) for qid, qdata in db.get("queries", {}).items()
        if qdata.get("status") == "pending"
    ]
    if not pending:
        await message.reply("<b>No unanswered queries.</b>", parse_mode=ParseMode.HTML)
        return

    pending.sort(key=lambda x: x[1].get("created_at", 0))

    SHOW_LIMIT = 15
    lines = [f"<b><u>Unanswered Queries</u></b> ({len(pending)})\n"]
    for qid, qdata in pending[:SHOW_LIMIT]:
        name = str(qdata.get("name", "Unknown")).replace("<", "&lt;").replace(">", "&gt;")
        preview = qdata.get("question", "")
        if len(preview) > 60:
            preview = preview[:60].rstrip() + "..."
        preview = preview.replace("<", "&lt;").replace(">", "&gt;")

        link = _query_group_link(qdata.get("log_msg_id"))
        ticket_part = f'<a href="{link}">{qid}</a>' if link else qid

        lines.append(f"🎫 <b>{ticket_part}</b> — {name}\n<code>{preview}</code>")

    if len(pending) > SHOW_LIMIT:
        lines.append(f"\n<b>+{len(pending) - SHOW_LIMIT} more.</b>")

    await message.reply("\n\n".join(lines), parse_mode=ParseMode.HTML, disable_web_page_preview=True)

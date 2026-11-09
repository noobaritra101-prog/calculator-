import time
import random
import asyncio
import io
from datetime import datetime, timezone
from PIL import Image, ImageDraw, ImageFont
from aiogram import F
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, BufferedInputFile, InputMediaPhoto
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ButtonStyle
from aiogram.exceptions import TelegramBadRequest

import config
from config import bot, main_router, load_db, save_db, ensure_user, STOCKS, ADMIN_IDS
from config import is_ghost_banned, is_shadow_banned
from html import escape as _html_esc
from vlog import log_action

# ==========================================
# MARKET CRASH SETTINGS (🔴 Extreme Risk only)
# ==========================================
# Any stock with volatility above this is eligible to crash. This matches
# the existing "🔴 Extreme Risk (Gamble)" tier threshold used in the UI.
# (Scaled down 0.4x alongside STOCKS volatility — was 0.25)
CRASH_VOLATILITY_THRESHOLD = 0.10
# How long trading (buying AND selling) is frozen on a crashed stock.
CRASH_FREEZE_SECONDS = 2 * 60 * 60
# Crashed price = this fraction of the stock's base_price.
CRASH_PRICE_FLOOR_PCT = 0.05
# Only these symbols can ever crash — random or forced via /fcrash.
CRASHABLE_SYMBOLS = {"NEX", "TRK"}

# ── POST-CRASH RECOVERY ASSIST ──
# CRASHABLE_SYMBOLS get zero mean-reversion while below base_price — that's
# intentional, it's what lets real selling pressure walk one down to a
# crash. But right after a crash, the price is so low that the random walk
# itself (proportional to price × volatility) produces tiny absolute
# swings — under 1 shard — so with no one actively trading it, it can
# drift sideways for a very long, streaky stretch before luck alone moves
# it. This adds a small FLAT (not price-proportional) upward nudge, active
# only while price is still close to the crash floor, just large enough to
# reliably win against that dead-zone effect and give it real forward
# motion out of the bottom. Scaled off base_price (not current price) so
# it works consistently across stocks with very different post-crash price
# levels (e.g. TRK reopens around 2-3, NEX around 10). It's deliberately
# weak enough that real, sustained selling can still overpower it and
# crash the stock again — this only fixes getting passively stuck, not
# the ability to be actively pushed back down.
POST_CRASH_RECOVERY_BAND_PCT = 0.20   # nudge is active while price < this fraction of base_price
POST_CRASH_RECOVERY_PUSH_PCT = 0.005  # nudge size = this fraction of base_price, per tick, while in the band

# How strongly price gets pulled back toward base_price each tick.
# Higher = prices snap back faster and drift less. (was 0.02)
MEAN_REVERSION_PCT = 0.06

# Max multiple of base_price any stock can ever reach. (was 20x)
PRICE_CEILING_MULTIPLIER = 4

# ── WINDFALL (PROGRESSIVE PROFIT) TAX ──
# On top of the flat brokerage fee, sales that more than double the
# average buy price get an extra tax on the profit portion only —
# targets "held forever, cashed out huge" without touching normal trades.
PROFIT_TAX_THRESHOLD = 2.0   # tax kicks in once sale price >= 2x avg buy price
PROFIT_TAX_RATE = 0.08       # 8% of the profit portion, once past threshold (was 15%)

# ── REWARDED ADS: EXTRA DAILY BUY ALLOTMENT ──
# Each rewarded ad watched (confirmed by Adsgram's server postback) adds
# AD_BONUS_SHARES to that day's buy limit, up to AD_MAX_PER_DAY ads/day.
# Credited by deck.py's existing Adsgram postback (/api/deck/ads/reward) via
# credit_market_ad(); there is no separate market reward URL.
# Resets with the daily buy limit (UTC midnight).
AD_BONUS_SHARES = 10
AD_MAX_PER_DAY = 3


def _market_ad_watched(udata: dict) -> int:
    """Rewarded ads confirmed today (auto-resets on the UTC date change)."""
    today = config.get_shop_rotation_seed()
    ad = udata.setdefault("market_ad", {"date": today, "watched": 0})
    if ad.get("date") != today:
        ad["date"] = today
        ad["watched"] = 0
    return ad.get("watched", 0)


def credit_market_ad(udata: dict) -> int:
    """Called from the existing Adsgram postback in deck.py. Caller saves the db."""
    watched = _market_ad_watched(udata)
    if watched < AD_MAX_PER_DAY:
        udata["market_ad"]["watched"] = watched + 1
    return udata["market_ad"]["watched"]


def _daily_limit(udata: dict) -> int:
    """Today's buy allotment including ad bonuses."""
    return config.DAILY_STOCK_BUY_LIMIT + _market_ad_watched(udata) * AD_BONUS_SHARES


# ── MARKET HOURS ──
# The market trades 24 hours a day, Monday through Friday. At the Friday
# -> Saturday UTC rollover every open position is auto-sold at the current
# price (same fee/tax as a manual sale), and the market stays closed for
# all of Saturday and Sunday, reopening automatically at Monday 00:00 UTC.
MARKET_CLOSED_WEEKDAYS = {5, 6}   # Python weekday(): Saturday=5, Sunday=6


STOCKMARKET_APP_LINK = "https://t.me/Animenx_bot/stockmarket"


def is_extreme_risk(sym: str) -> bool:
    return STOCKS.get(sym, {}).get("volatility", 0) > CRASH_VOLATILITY_THRESHOLD


def is_frozen(market_entry: dict) -> bool:
    """True if this stock is currently inside its post-crash trading freeze."""
    frozen_until = market_entry.get("frozen_until", 0)
    return time.time() < frozen_until


def freeze_time_left_str(market_entry: dict) -> str:
    seconds_left = max(0, int(market_entry.get("frozen_until", 0) - time.time()))
    h, rem = divmod(seconds_left, 3600)
    m, _ = divmod(rem, 60)
    if h: return f"{h}h {m}m"
    return f"{m}m"


def is_stock_banned(db: dict, uid) -> bool:
    """True if this user is restricted from all stock market features."""
    return str(uid) in db.get("settings", {}).get("stock_banned", {})


def stock_ban_reply_text(db: dict, uid) -> str:
    meta = db.get("settings", {}).get("stock_banned", {}).get(str(uid), {})
    reason = meta.get("reason", "None")
    return f"🚫 You are restricted from using the Stock Market.\nReason: {reason}"


def _touch_market_daily(db: dict) -> dict:
    """Returns today's stock-market daily-stats dict, resetting it if the
    date rolled over (UTC calendar day)."""
    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    daily = db.setdefault("market_daily_stats", {})
    if daily.get("date") != today_str:
        daily["date"] = today_str
        daily["buy_orders"] = 0
        daily["shares_bought"] = 0
        daily["shards_spent"] = 0
        daily["sell_orders"] = 0
        daily["shares_sold"] = 0
        daily["shards_generated"] = 0
        daily["fees_collected"] = 0
        daily["windfall_tax_collected"] = 0
        daily["shards_destroyed"] = 0
        daily["crashes"] = 0
        daily["by_symbol"] = {}
    return daily


def _touch_user_stock_daily(udata: dict) -> dict:
    """Returns this user's running today's-realized-stock-profit tracker,
    rolling yesterday's total into prev_day_profit the first time it's
    touched after the UTC date changes. Profit here means net money in/out
    from selling (manual sells AND the nightly forced liquidation), after
    fees/tax — i.e. sale payout minus cost basis. Caller is responsible for
    save_db()."""
    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    tracker = udata.setdefault("stock_daily_profit", {"date": today_str, "profit": 0, "prev_day_profit": 0})
    if tracker.get("date") != today_str:
        tracker["prev_day_profit"] = tracker.get("profit", 0)
        tracker["profit"] = 0
        tracker["date"] = today_str
    return tracker


def apply_crash(db: dict, sym: str) -> int:
    """Crashes `sym`: it has reached a price of 0, so trading is frozen for
    2 hours and every holder's position in it is wiped to nothing (their
    shares are now worth 0, same as the price). Returns holders_wiped.
    Caller is responsible for save_db()."""
    market = db.setdefault("market", {})
    stock_info = STOCKS[sym]
    entry = market.setdefault(sym, {"current_price": stock_info["base_price"], "history": [stock_info["base_price"]], "flow": 0})

    crash_price = max(1, int(stock_info["base_price"] * CRASH_PRICE_FLOOR_PCT))
    entry["current_price"] = crash_price
    entry["precise_price"] = float(crash_price)
    entry["history"].append(crash_price)
    if len(entry["history"]) > 24:
        entry["history"].pop(0)
    entry["frozen_until"] = time.time() + CRASH_FREEZE_SECONDS
    entry["flow"] = 0

    # Wipe every holder's position in this stock — it hit 0, so there's
    # nothing left to wipe FROM; their shares are simply gone. The shards
    # they originally paid for those shares (cost basis) are counted as
    # destroyed — real currency that vanishes from the economy.
    wiped_holders = 0
    shards_destroyed = 0
    for u_id, u_data in db.get("users", {}).items():
        u_stocks = u_data.get("stocks", {})
        if sym in u_stocks and u_stocks[sym].get("shares", 0) > 0:
            pos = u_stocks[sym]
            shards_destroyed += int(pos.get("shares", 0) * pos.get("avg_price", 0))
            del u_stocks[sym]
            wiped_holders += 1
    entry["last_crash_wiped_holders"] = wiped_holders
    entry["last_crash_shards_destroyed"] = shards_destroyed

    mstats = db.setdefault("market_stats", {})
    mstats["total_shards_destroyed"] = mstats.get("total_shards_destroyed", 0) + shards_destroyed
    mstats["total_crashes"] = mstats.get("total_crashes", 0) + 1

    daily = _touch_market_daily(db)
    daily["shards_destroyed"] += shards_destroyed
    daily["crashes"] += 1

    return wiped_holders


async def announce_crash_in_main_group(db: dict, sym: str, wiped: int):
    """Posts the crash announcement to the main group and pins it. Used by
    both engine-driven crashes (price hit 0) and /fcrash so every crash —
    automatic or manual — gets the same public notification."""
    entry = db.get("market", {}).get(sym, {})
    text = (
        f"<b>「 💥 CRASH 💥 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🏢 <b>{STOCKS[sym]['name']} ({sym})</b> has crashed — price hit <b>0 💠</b>.\n\n"
        f"💵 <b>Reopening price:</b> {entry.get('current_price', '?')} 💠\n"
        f"🚫 <b>Trading frozen for:</b> {freeze_time_left_str(entry)}\n"
        f"☠️ <b>{wiped} holder(s)</b> had their position in {sym} become worth <b>0 💠</b>."
    )
    try:
        msg = await config.bot.send_message(
            chat_id=config.MAIN_GROUP_USERNAME,
            text=text,
            parse_mode=ParseMode.HTML
        )
        await config.bot.pin_chat_message(
            chat_id=config.MAIN_GROUP_USERNAME,
            message_id=msg.message_id,
            disable_notification=False
        )
    except Exception as announce_err:
        print(f"[CRASH ANNOUNCE] Failed to post/pin in main group: {announce_err}")


# ==========================================
# MARKET HOURS (24h weekdays, closed Sat/Sun)
# ==========================================
def is_market_open() -> bool:
    """True Mon–Fri, all 24 hours. False all day Saturday and Sunday (UTC).
    This is the wall-clock schedule check used by the engine loop to decide
    WHEN to run the close/reopen transition — it does not gate trading
    directly (see is_trading_open below)."""
    return datetime.now(timezone.utc).weekday() not in MARKET_CLOSED_WEEKDAYS


def is_trading_open(db: dict) -> bool:
    """The actual switch that buy/sell handlers check. True Mon–Fri, false
    on Sat/Sun. Positions are now force-liquidated every night at the UTC
    midnight rollover (see market_engine_loop), not just on the Friday
    weekend transition — so this flag purely gates weekday vs weekend
    trading, independent of the nightly settlement.

    The weekend lock is checked against the LIVE UTC weekday every call
    (not just the cached market_state["open"] flag) so buying/selling is
    always locked on Saturday and Sunday — even right after a bot restart,
    before the engine loop has had a chance to run its daily rollover.

    The one exception is a same-day admin override via /fopen: if an
    owner force-opened the market for TODAY's specific weekend date, that
    (and only that) day is unlocked. It never carries over to the other
    weekend day or to future weeks."""
    now = datetime.now(timezone.utc)
    weekday = now.weekday()
    state = db.get("market_state", {})

    if weekday in MARKET_CLOSED_WEEKDAYS:
        today_str = now.strftime("%Y-%m-%d")
        return (
            state.get("forced_open_date") == today_str
            and state.get("forced_open_weekday") == weekday
        )

    return state.get("open", True)


def market_closed_reply() -> str:
    return (
        "<b>「 📈 MARKET CLOSED 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "The Nexus Stock Exchange is closed for the weekend.\n"
        "Trading reopens <b>Monday, 00:00 UTC</b>."
    )


def _liquidate_all_positions(db: dict) -> dict:
    """Force-sells every user's open position at the current market price,
    using the same brokerage fee / windfall tax math as a normal sale.
    Runs once at every UTC midnight rollover (nightly, not just on the
    Friday -> Saturday weekend transition). Caller is responsible for
    save_db()."""
    market = db.get("market", {})
    summary = {"users_affected": 0, "total_payout": 0, "total_shares": 0}

    mstats = db.setdefault("market_stats", {})
    daily = _touch_market_daily(db)

    for uid, udata in db.get("users", {}).items():
        user_stocks = udata.get("stocks", {})
        if not user_stocks:
            continue

        user_payout = 0
        user_shares = 0
        for sym, pos in list(user_stocks.items()):
            shares = pos.get("shares", 0)
            if shares <= 0 or sym not in STOCKS:
                continue

            price = market.get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
            avg_price = pos.get("avg_price", price)
            gross_payout = price * shares
            fee = int(gross_payout * config.MARKET_FEE_PCT)

            cost_basis = avg_price * shares
            profit = gross_payout - cost_basis
            profit_tax = 0
            if avg_price > 0 and price >= avg_price * PROFIT_TAX_THRESHOLD and profit > 0:
                profit_tax = int(profit * PROFIT_TAX_RATE)

            net_payout = gross_payout - fee - profit_tax
            udata["nexus_shards"] = udata.get("nexus_shards", 0) + net_payout

            daily_tracker = _touch_user_stock_daily(udata)
            daily_tracker["profit"] += int(net_payout - cost_basis)

            user_payout += net_payout
            user_shares += shares

            mstats["total_sell_orders"] = mstats.get("total_sell_orders", 0) + 1
            mstats["total_shares_sold"] = mstats.get("total_shares_sold", 0) + shares
            mstats["total_shards_generated"] = mstats.get("total_shards_generated", 0) + net_payout
            mstats["total_fees_collected"] = mstats.get("total_fees_collected", 0) + fee
            mstats["total_windfall_tax_collected"] = mstats.get("total_windfall_tax_collected", 0) + profit_tax

            daily["sell_orders"] += 1
            daily["shares_sold"] += shares
            daily["shards_generated"] += net_payout
            daily["fees_collected"] += fee
            daily["windfall_tax_collected"] += profit_tax

            log_action(db, uid, {
                "type": "market_liquidation",
                "amount": net_payout,
                "symbol": sym,
                "shares": shares,
                "profit": int(profit),
                "chat_title": "System (Nightly Liquidation)"
            })

        if user_shares > 0:
            user_stocks.clear()
            summary["users_affected"] += 1
            summary["total_payout"] += user_payout
            summary["total_shares"] += user_shares

    return summary


async def announce_market_close(summary: dict):
    text = (
        "<b>「 📉 MARKET CLOSED FOR THE WEEKEND 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n"
        "All open positions have been automatically sold at the closing price.\n\n"
        f"👤 <b>Players Settled:</b> {summary['users_affected']}\n"
        f"📦 <b>Total Shares Liquidated:</b> {summary['total_shares']:,}\n"
        f"💠 <b>Total Payout:</b> {summary['total_payout']:,} Shards\n\n"
        "Trading reopens <b>Monday, 00:00 UTC</b>."
    )
    try:
        await config.bot.send_message(
            chat_id=config.MAIN_GROUP_USERNAME,
            text=text,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[MARKET CLOSE ANNOUNCE] Failed: {e}")


async def announce_market_open():
    text = (
        "<b>「 📈 MARKET OPEN 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n"
        "The Nexus Stock Exchange is now open for trading, 24 hours a day "
        "through Friday."
    )
    try:
        await config.bot.send_message(
            chat_id=config.MAIN_GROUP_USERNAME,
            text=text,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[MARKET OPEN ANNOUNCE] Failed: {e}")



# ==========================================
# PRIVACY CHECK HELPER
# ==========================================
async def verify_user(cq: CallbackQuery, target_id: str) -> bool:
    """Ensures only the user who executed the command can use the buttons."""
    if str(cq.from_user.id) != str(target_id):
        await cq.answer("❌ This menu is not for you!", show_alert=True)
        return False
    return True

# ==========================================
# MARKET ENGINE (Runs periodically)
# ==========================================
async def market_engine_loop():
    while True:
        await asyncio.sleep(config.MARKET_UPDATE_INTERVAL)
        db = load_db()
        market = db.setdefault("market", {})

        # ── Nightly UTC-midnight rollover: force-liquidate open positions ──
        # Fires every night (not just Friday). On a weekday->weekday roll
        # the market stays open and trading resumes immediately with
        # everyone's positions cleared. On Fri->Sat it also triggers the
        # weekend close; on Sun->Mon it reopens (nothing left to liquidate).
        state = db.setdefault("market_state", {"open": True, "last_reset_date": config.get_shop_rotation_seed()})
        today_str = config.get_shop_rotation_seed()

        if state.get("last_reset_date") != today_str:
            was_open = state.get("open", True)
            summary = _liquidate_all_positions(db)
            state["last_reset_date"] = today_str

            market_open_now = is_market_open()
            state["open"] = market_open_now
            save_db()

            if market_open_now:
                if not was_open:
                    await announce_market_open()
                # Weekday nightly liquidation stays silent — no group message.
            else:
                await announce_market_close(summary)

        # This is the actual "is the market live right now" check for price
        # ticking — it must agree with is_trading_open() (which buy/sell use),
        # so that a same-day /fopen override also resumes price movement, not
        # just trading. Using the raw weekday check here (is_market_open())
        # would keep prices frozen on a force-opened Saturday/Sunday even
        # though trades themselves were unlocked.
        trading_active_now = is_trading_open(db)

        if not trading_active_now:
            # Market is closed for the weekend (and not force-opened via
            # /fopen for today) — prices stay frozen, no ticks.
            continue

        for sym, stock_info in STOCKS.items():
            if sym not in market:
                market[sym] = {"current_price": stock_info["base_price"], "history": [stock_info["base_price"]] * 24, "flow": 0}

            # A /fcrash ramp-down owns this symbol's price exclusively while
            # it's in progress — skip the normal RNG tick for it so the two
            # don't fight over the same value mid-ramp. If the flag has gone
            # stale (its owning task died mid-ramp, e.g. a bot restart), clear
            # it here and let this symbol resume normal ticking instead of
            # being stuck forever.
            if market[sym].get("force_crashing"):
                if _is_force_crash_stale(market[sym]):
                    market[sym]["force_crashing"] = False
                else:
                    continue

            # While a symbol is frozen post-crash, its price must hold still.
            # Without this check, CRASHABLE_SYMBOLS (which have zero floor and
            # no mean-reversion) could keep randomly drifting during the
            # freeze and silently walk back down to 0 — so the moment the
            # freeze lifted, the very next tick's crash-check saw price <= 0
            # and re-crashed it instantly, before anyone could even trade it.
            if is_frozen(market[sym]):
                continue

            old_price = market[sym].get("precise_price", market[sym]["current_price"])
            base_price = stock_info["base_price"]
            volatility = stock_info["volatility"]

            # Player influence now reflects NET recent buy/sell activity since the
            # last tick (flow), not total outstanding shares. Total holdings can
            # only ever be >= 0, so using it as the influence meant merely HOLDING
            # shares (with no new trades) kept nudging the price up forever, with
            # no symmetric downward pull — that's what let NEX/TRK climb endlessly
            # as long as anyone held shares, guaranteeing profit. Net flow can be
            # positive (net buying) or negative (net selling), so heavy selling
            # now actually pushes the price down again.
            flow = market[sym].get("flow", 0)
            raw_influence = flow * 0.0001
            player_influence = max(-old_price * 0.05, min(raw_influence, old_price * 0.05))

            # Soft mean-reversion: nudge price back toward base each tick.
            # CRASHABLE_SYMBOLS are exempt from reversion ONLY while below
            # base_price — that's what lets sustained selling or a bad
            # volatility streak drive them all the way down to a crash.
            # Above base_price, a dampening pull now applies (half the normal
            # strength) so a hot streak of buying can't just run away to the
            # ceiling unchecked — that runaway climb was making NEX's upside
            # far too easy/high compared to everything else.
            if sym in CRASHABLE_SYMBOLS:
                if old_price > base_price:
                    reversion = (base_price - old_price) * (MEAN_REVERSION_PCT * 0.5)
                elif old_price < base_price * POST_CRASH_RECOVERY_BAND_PCT:
                    reversion = base_price * POST_CRASH_RECOVERY_PUSH_PCT
                else:
                    reversion = 0
            else:
                reversion = (base_price - old_price) * MEAN_REVERSION_PCT

            rng_shift = random.uniform(-volatility, volatility)
            # precise_price (a float) is what actually carries forward tick to
            # tick now — see old_price above. Any single tick's delta here can
            # be well under 1 shard, especially at low prices (e.g. right
            # after a crash), but it's no longer thrown away: it accumulates
            # in precise_price until it's big enough to move the rounded
            # display price. Previously old_price was re-read from the
            # rounded integer every tick, so at low prices (small
            # old_price * volatility) the max possible delta could stay
            # permanently under the 0.5 rounding threshold — mathematically
            # incapable of ever moving the displayed price. That's what let
            # a stock settle at its post-crash reopening price and sit there
            # forever, since CRASHABLE_SYMBOLS also get zero reversion below
            # base_price to pull them back up.
            raw_new_price = old_price + (old_price * rng_shift) + player_influence + reversion

            # Clamp: floor at 10% of base, ceiling at PRICE_CEILING_MULTIPLIER x
            # base. NEX/TRK are exempt from the floor — they're allowed to
            # drift all the way down to 0, which is what now triggers their
            # crash (see below). They still can't go negative.
            price_ceil = int(base_price * stock_info.get("ceiling_mult", PRICE_CEILING_MULTIPLIER))
            if sym in CRASHABLE_SYMBOLS:
                price_floor = 0
            else:
                price_floor = max(5, int(base_price * 0.10))
            if raw_new_price < price_floor: raw_new_price = price_floor
            if raw_new_price > price_ceil:  raw_new_price = price_ceil

            new_price = round(raw_new_price)

            market[sym]["precise_price"] = raw_new_price
            market[sym]["current_price"] = new_price
            market[sym]["history"].append(new_price)
            if len(market[sym]["history"]) > 24: 
                market[sym]["history"].pop(0)

            # Flow only represents activity SINCE THE LAST TICK — reset it now
            # that it's been applied, so idle holding has zero ongoing effect.
            market[sym]["flow"] = 0

        # ── PRICE-DRIVEN CRASHES (NEX/TRK only) ──────────────────────────
        # No more random roll. A crashable stock crashes the moment its
        # price actually reaches 0 — which only CRASHABLE_SYMBOLS can ever
        # do, since the floor clamp above skips them. Everything else is
        # floored at 10% of base price and can never trigger this.
        crashed_syms = []
        for sym in CRASHABLE_SYMBOLS:
            if sym not in STOCKS: continue
            entry = market[sym]
            if is_frozen(entry): continue
            if entry["current_price"] <= 0:
                crashed_syms.append(sym)

        for sym in crashed_syms:
            wiped = apply_crash(db, sym)
            await announce_crash_in_main_group(db, sym, wiped)

        save_db()

        # ── DB-Group log: market tick summary ──────────────────────────────
        try:
            lines = [f"<b>「 📈 MARKET ENGINE UPDATE 」</b>",
                     f"━━━━━━━━━━━━━━━━━━━━━━",
                     f"🕐 <b>Time:</b> {time.strftime('%Y-%m-%d %H:%M:%S')} UTC\n"]
            for sym in STOCKS:
                price = market.get(sym, {}).get("current_price", "?")
                hist  = market.get(sym, {}).get("history", [])
                prev  = hist[-2] if len(hist) >= 2 else price
                arrow = "🟢" if price >= prev else "🔴"
                lines.append(f"  {arrow} <b>{sym}</b>  ➜  <b>{price} 💠</b>")
            lines.append("━━━━━━━━━━━━━━━━━━━━━━")
            await config.bot.send_message(
                chat_id=config.DATABASE_BACKUP_ID,
                text="\n".join(lines),
                parse_mode="HTML"
            )
        except Exception as log_err:
            print(f"[MARKET LOG] Failed: {log_err}")

        print(f"[MARKET] Engine updated stock prices at {time.strftime('%X')}")

# ==========================================
# /fcrash <SYMBOL> — owner-only forced crash
# ==========================================
FCRASH_RAMP_SECONDS = 60
FCRASH_TICK_SECONDS = 2  # price steps down once every 2s -> ~30 steps over 60s
FCRASH_STALE_SECONDS = FCRASH_RAMP_SECONDS + 90  # generous buffer past the ramp


def _is_force_crash_stale(entry: dict) -> bool:
    """A force_crashing flag that's outlived the ramp + a generous buffer
    means the background ramp task died without ever clearing it — e.g.
    the bot was restarted (/refresh does a hard process restart) partway
    through the 60s ramp. Without this check, that symbol would be stuck
    forever: skipped by every engine tick AND rejected by any future
    /fcrash attempt, with no way to recover except editing the DB by hand."""
    if not entry.get("force_crashing"):
        return False
    started = entry.get("force_crashing_started_at", 0)
    return (time.time() - started) > FCRASH_STALE_SECONDS


async def _fcrash_ramp_down(sym: str, announce_chat_id):
    """Slowly walks `sym`'s price down to 0 over FCRASH_RAMP_SECONDS, then
    triggers the same apply_crash()/announcement path as an organic
    price-hits-0 crash. Runs as a detached background task so /fcrash
    returns immediately instead of blocking the command for 60 seconds."""
    db = load_db()
    market = db.setdefault("market", {})
    entry = market.setdefault(sym, {"current_price": STOCKS[sym]["base_price"], "history": [STOCKS[sym]["base_price"]] * 24, "flow": 0})

    entry["force_crashing"] = True
    entry["force_crashing_started_at"] = time.time()
    start_price = max(1, entry["current_price"])
    save_db()

    steps = max(1, FCRASH_RAMP_SECONDS // FCRASH_TICK_SECONDS)
    for step in range(1, steps + 1):
        await asyncio.sleep(FCRASH_TICK_SECONDS)
        db = load_db()
        market = db.setdefault("market", {})
        entry = market.setdefault(sym, {"current_price": start_price, "history": [start_price], "flow": 0})

        # Linear ramp down to exactly 0 on the final step.
        remaining_fraction = max(0.0, 1 - (step / steps))
        entry["current_price"] = int(start_price * remaining_fraction)
        entry["precise_price"] = float(entry["current_price"])
        entry["history"].append(entry["current_price"])
        if len(entry["history"]) > 24:
            entry["history"].pop(0)
        save_db()

    # Guarantee an exact 0 regardless of any rounding above, then crash it.
    db = load_db()
    market = db.setdefault("market", {})
    entry = market[sym]
    entry["current_price"] = 0
    entry["force_crashing"] = False
    wiped = apply_crash(db, sym)
    save_db()

    await announce_crash_in_main_group(db, sym, wiped)
    try:
        await config.bot.send_message(
            chat_id=announce_chat_id,
            text=f"✅ {sym} finished ramping down and crashed at 0 💠. Announced in the main group.",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass


@main_router.message(Command("fcrash"))
async def force_crash_cmd(message: Message, command: CommandObject):
    if message.from_user.id != config.SUPREME_OWNER_ID:
        return  # silent — don't reveal this command exists to non-owners

    arg = (command.args or "").strip().upper()
    if arg not in CRASHABLE_SYMBOLS:
        allowed = "/".join(sorted(CRASHABLE_SYMBOLS))
        await message.reply(
            f"⚠️ <b>Usage:</b> <code>/fcrash {allowed}</code>\nOnly {allowed} can be crashed.",
            parse_mode=ParseMode.HTML
        )
        return

    if arg not in STOCKS:
        await message.reply(f"❌ {arg} isn't a configured stock.", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    market = db.setdefault("market", {})
    if arg not in market:
        market[arg] = {"current_price": STOCKS[arg]["base_price"], "history": [STOCKS[arg]["base_price"]] * 24, "flow": 0}

    if market[arg].get("force_crashing"):
        if _is_force_crash_stale(market[arg]):
            market[arg]["force_crashing"] = False
            save_db()
        else:
            await message.reply(f"⏳ {arg} is already ramping down to a crash.", parse_mode=ParseMode.HTML)
            return
    if is_frozen(market[arg]):
        await message.reply(f"🚫 {arg} is still frozen from a previous crash.", parse_mode=ParseMode.HTML)
        return

    asyncio.create_task(_fcrash_ramp_down(arg, message.chat.id))
    await message.reply(
        f"📉 <b>{arg}</b> will now slowly drop to <b>0 💠</b> over the next ~{FCRASH_RAMP_SECONDS}s, then crash.",
        parse_mode=ParseMode.HTML
    )

# ==========================================
# /fopen market — owner-only forced weekend open
# ==========================================
# Lets an admin unlock trading on a Saturday or Sunday that would normally
# be locked. The override is tied to TODAY'S exact calendar date, so:
#   • Using it on Saturday opens ONLY that Saturday — Sunday of the same
#     weekend stays locked as normal.
#   • It never re-applies on a future Saturday/Sunday — each week needs
#     its own /fopen if desired.
@main_router.message(Command("fopen"))
async def force_open_market_cmd(message: Message, command: CommandObject):
    if message.from_user.id != config.SUPREME_OWNER_ID:
        return  # silent — don't reveal this command exists to non-owners

    arg = (command.args or "").strip().lower()
    if arg != "market":
        await message.reply(
            "⚠️ <b>Usage:</b> <code>/fopen market</code>\n"
            "Force-opens trading for today — only works on a Saturday or Sunday.",
            parse_mode=ParseMode.HTML
        )
        return

    now = datetime.now(timezone.utc)
    weekday = now.weekday()

    if weekday not in MARKET_CLOSED_WEEKDAYS:
        await message.reply(
            "📈 The market is already open — /fopen only does anything on a Saturday or Sunday.",
            parse_mode=ParseMode.HTML
        )
        return

    db = load_db()
    state = db.setdefault("market_state", {"open": True, "last_reset_date": config.get_shop_rotation_seed()})
    today_str = now.strftime("%Y-%m-%d")
    state["forced_open_date"] = today_str
    state["forced_open_weekday"] = weekday
    save_db()

    day_name = "Saturday" if weekday == 5 else "Sunday"
    other_day = "Sunday" if weekday == 5 else "Saturday"

    await message.reply(
        f"📈 <b>Market force-opened for today ({day_name}) only.</b>\n"
        f"Trading will lock again for {other_day} and resume its normal schedule Monday, 00:00 UTC.",
        parse_mode=ParseMode.HTML
    )
    await announce_market_open()

# ==========================================
# /stban, /stunban, /stblist — stock market ban list
# ==========================================
# A restriction scoped to the stock market only — unlike /gban (a full
# global ban), a stock-banned user can still use every other part of the
# bot, they just can't open /stockmarket or trade.
@main_router.message(Command("stban"))
async def stock_ban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    raw_args = (command.args or "").strip()
    is_reply = bool(message.reply_to_message and message.reply_to_message.from_user)

    if is_reply:
        uid = message.reply_to_message.from_user.id
        name = message.reply_to_message.from_user.first_name
        reason = raw_args or "None"
    else:
        if not raw_args:
            await message.reply(
                "⚠️ <b>Usage:</b>\n"
                "<code>/stban &lt;user_id | @username&gt; [reason]</code>\n"
                "Or reply to a user's message with <code>/stban [reason]</code>",
                parse_mode=ParseMode.HTML
            )
            return
        parts = raw_args.split(maxsplit=1)
        identifier = parts[0]
        reason = parts[1] if len(parts) > 1 else "None"
        uid, name = await config.resolve_target(identifier, message)
        if not uid:
            await message.reply(f"⚠️ Could not resolve target <code>{identifier}</code>.", parse_mode=ParseMode.HTML)
            return

    if uid == config.SUPREME_OWNER_ID:
        await message.reply("<b>⊘ FAILED</b>\nThe owner is untouchable.", parse_mode=ParseMode.HTML)
        return
    if uid in ADMIN_IDS:
        await message.reply("<b>⊘ DENIED</b>\nModerators are protected and cannot be stock-banned.", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    banned = db.setdefault("settings", {}).setdefault("stock_banned", {})
    if str(uid) in banned:
        await message.reply(f"⚠️ {config.get_mention(uid, name)}(<code>{uid}</code>) is already stock-market banned.", parse_mode=ParseMode.HTML)
        return

    banned[str(uid)] = {
        "reason": reason,
        "banned_by": message.from_user.id,
        "banned_at": int(time.time())
    }
    save_db()

    await message.reply(
        f"<b>⊘ STOCK MARKET BAN ISSUED</b>\n\n"
        f"<b>User:</b> {config.get_mention(uid, name)}(<code>{uid}</code>)\n"
        f"<b>Reason:</b> {reason}",
        parse_mode=ParseMode.HTML
    )


@main_router.message(Command("stunban"))
async def stock_unban_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS: return

    uid, name = await config.resolve_target(command.args, message)
    if not uid:
        await message.reply(
            "⚠️ <b>Format:</b> Reply to user or use:\n• <code>/stunban &lt;user_id&gt;</code>\n• <code>/stunban &lt;@username&gt;</code>",
            parse_mode=ParseMode.HTML
        )
        return

    db = load_db()
    banned = db.setdefault("settings", {}).setdefault("stock_banned", {})
    if str(uid) not in banned:
        await message.reply(f"⚠️ {config.get_mention(uid, name)}(<code>{uid}</code>) is not stock-market banned.", parse_mode=ParseMode.HTML)
        return

    banned.pop(str(uid), None)
    save_db()

    await message.reply(f"✅ {config.get_mention(uid, name)}(<code>{uid}</code>) has been unbanned from the stock market.", parse_mode=ParseMode.HTML)


@main_router.message(Command("stblist"))
async def stock_ban_list_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return

    db = load_db()
    banned = db.get("settings", {}).get("stock_banned", {})
    if not banned:
        await message.reply("📝 Stock Market ban list is currently empty.", parse_mode=ParseMode.HTML)
        return

    text = "<b>「 🚫 STOCK MARKET BANNED USERS 」</b>\n━━━━━━━━━━━━━━━━━━━━\n"
    for idx, (uid_str, meta) in enumerate(banned.items(), start=1):
        name = db["users"].get(uid_str, {}).get("name", "User")
        reason = meta.get("reason", "None")
        text += f"{idx}. {config.get_mention(int(uid_str), name)}(<code>{uid_str}</code>)\n   └ Reason: {reason}\n"
    text += "━━━━━━━━━━━━━━━━━━━━"
    await message.reply(text, parse_mode=ParseMode.HTML)

# ==========================================
# /stockstats — owner/admin market overview
# ==========================================
def _build_stockstats_text(db: dict) -> str:
    mstats = db.get("market_stats", {})
    daily = db.get("market_daily_stats", {})
    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_today = daily.get("date") == today_str

    buy_orders_today   = daily.get("buy_orders", 0) if is_today else 0
    shares_bought_today= daily.get("shares_bought", 0) if is_today else 0
    shards_spent_today = daily.get("shards_spent", 0) if is_today else 0
    sell_orders_today  = daily.get("sell_orders", 0) if is_today else 0
    shares_sold_today  = daily.get("shares_sold", 0) if is_today else 0
    shards_gen_today   = daily.get("shards_generated", 0) if is_today else 0
    fees_today         = daily.get("fees_collected", 0) if is_today else 0
    tax_today          = daily.get("windfall_tax_collected", 0) if is_today else 0
    destroyed_today    = daily.get("shards_destroyed", 0) if is_today else 0
    crashes_today      = daily.get("crashes", 0) if is_today else 0
    by_symbol_today    = daily.get("by_symbol", {}) if is_today else {}

    trading_state = "🟢 Open" if is_trading_open(db) else "🔴 Closed (weekend)"

    text = (
        "<b>📊 Stock Market Stats</b>\n\n"
        f"Market: {trading_state}\n\n"

        "<b>Today</b>\n"
        f"• Bought: <code>{shares_bought_today:,}</code> shares in <code>{buy_orders_today:,}</code> orders — <code>{shards_spent_today:,} 💠</code> spent\n"
        f"• Sold: <code>{shares_sold_today:,}</code> shares in <code>{sell_orders_today:,}</code> orders — <code>{shards_gen_today:,} 💠</code> paid out\n"
        f"• Fees collected: <code>{fees_today:,} 💠</code>\n"
        f"• Profit tax collected: <code>{tax_today:,} 💠</code>\n"
        f"• Crashes: <code>{crashes_today:,}</code> (<code>{destroyed_today:,} 💠</code> destroyed)\n"
    )

    text += "\n<b>Today by Stock</b>\n"
    for sym in STOCKS:
        sym_stats = by_symbol_today.get(sym, {"bought": 0, "sold": 0})
        text += f"• {sym} - {sym_stats.get('bought', 0):,} bought, {sym_stats.get('sold', 0):,} sold\n"

    text += (
        "\n<b>All-Time</b>\n"
        f"• Bought: <code>{mstats.get('total_shares_bought', 0):,}</code> shares in <code>{mstats.get('total_buy_orders', 0):,}</code> orders\n"
        f"• Sold: <code>{mstats.get('total_shares_sold', 0):,}</code> shares in <code>{mstats.get('total_sell_orders', 0):,}</code> orders\n"
        f"• Fees collected: <code>{mstats.get('total_fees_collected', 0):,} 💠</code>\n"
        f"• Profit tax collected: <code>{mstats.get('total_windfall_tax_collected', 0):,} 💠</code>\n"
        f"• Crashes: <code>{mstats.get('total_crashes', 0):,}</code> (<code>{mstats.get('total_shards_destroyed', 0):,} 💠</code> destroyed)"
    )
    return text


def _stockstats_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="stockstats_refresh")]
    ])


@main_router.message(Command("stockstats"))
async def stockstats_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    db = load_db()
    text = _build_stockstats_text(db)
    await message.reply(text, parse_mode=ParseMode.HTML, reply_markup=_stockstats_kb())


@main_router.callback_query(F.data == "stockstats_refresh")
async def stockstats_refresh_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("Admins only.", show_alert=True)
        return

    db = load_db()
    text = _build_stockstats_text(db)
    try:
        await cq.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=_stockstats_kb())
        await cq.answer("Refreshed ✅")
    except TelegramBadRequest:
        await cq.answer("Already up to date.")

# ==========================================
# HIGH-FIDELITY PIL GRAPH GENERATOR
# ==========================================
def generate_stock_graph(symbol: str, history: list) -> io.BytesIO:
    width, height = 600, 300
    
    # Initialize high-quality base image with transparent alpha support
    img = Image.new("RGBA", (width, height), (11, 15, 25, 255))
    draw = ImageDraw.Draw(img)
    
    color_up = (46, 204, 113, 255)     # Glowing Emerald
    color_down = (231, 76, 60, 255)    # Glowing Crimson
    grid_color = (24, 30, 43, 255)     # Subtle Grid Slate
    
    is_up = history[-1] >= history[0] if len(history) > 1 else True
    line_color = color_up if is_up else color_down

    # Draw neon technical grid structure
    for i in range(0, width, 50): 
        draw.line([(i, 0), (i, height)], fill=grid_color, width=1)
    for i in range(0, height, 50): 
        draw.line([(0, i), (width, i)], fill=grid_color, width=1)

    # Plot coordinates & calculate gradients
    if len(history) > 1:
        max_price = max(history) + 5
        min_price = min(history) - 5 if min(history) > 5 else 0
        price_range = max_price - min_price if max_price != min_price else 1
        
        x_step = width / (len(history) - 1)
        points = []
        
        for i, price in enumerate(history):
            x = i * x_step
            y = height - ((price - min_price) / price_range * height)
            points.append((x, y))
            
        # Composite semi-transparent glow fill under the plotted curve
        fill_layer = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        fill_draw = ImageDraw.Draw(fill_layer)
        poly_points = [(points[0][0], height)] + points + [(points[-1][0], height)]
        fill_color = (46, 204, 113, 30) if is_up else (231, 76, 60, 30)
        fill_draw.polygon(poly_points, fill=fill_color)
        
        img = Image.alpha_composite(img, fill_layer)
        draw = ImageDraw.Draw(img) # Re-bind draw handle to active layer
        
        # Render clean trend curve with custom antialiased thickness
        draw.line(points, fill=line_color, width=4)
        
        # Plot precise node point rings
        for pt in points:
            draw.ellipse((pt[0]-4, pt[1]-4, pt[0]+4, pt[1]+4), fill=(255, 255, 255, 255), outline=line_color, width=1)

    # Render technical information labels directly on canvas
    try:
        font = ImageFont.load_default()
    except Exception:
        font = None

    text_color = (130, 145, 175, 255)
    draw.text((15, 15), f"ASSET: {symbol}", fill=(255, 255, 255, 255), font=font)
    draw.text((15, 30), f"PRICE: {history[-1]} Shards", fill=line_color, font=font)
    draw.text((15, height - 25), "NEXUS EXCHANGE SYSTEMS", fill=text_color, font=font)

    # Convert back to standard RGB to safeguard file transfers
    final_img = img.convert("RGB")
    bio = io.BytesIO()
    final_img.save(bio, format="PNG")
    bio.seek(0)
    return bio

# ==========================================
# STOCK MARKET UI HANDLERS
# ==========================================
def _market_main_text() -> str:
    return (
        "「 📈 𝗡𝗘𝗫𝗨𝗦 𝗦𝗧𝗢𝗖𝗞 𝗘𝗫𝗖𝗛𝗔𝗡𝗚𝗘 ぁ 」\n\n"
        "<blockquote><b>Welcome to the financial heart of the Anime Nexus. Acquire, trade, and exchange fractional shares dynamically.</b></blockquote>\n\n"
        "<i>Choose a Action Below</i> 👇"
    )


def _market_rules_text() -> str:
    return (
        "<b>「 📖 MARKET RULES 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n\n"
        "<b>💡 Market Rules:</b>\n"
        "• 🏢 <b>Stocks:</b> Buy shares of elite anime factions. Buy low, sell high.\n"
        "• 📊 <b>Volatility:</b> Highly volatile factions yield rapid gains but carry steep risk.\n"
        "• ⏱️ <b>Updates:</b> Prices shift every <b>5 minutes</b> dynamically based on RNG.\n"
        "• 🕐 <b>Trading Hours:</b> Open 24 hours, <b>Monday–Friday</b>. Closed Saturday & Sunday.\n"
        "• 🌙 <b>Nightly Settlement:</b> All open positions are auto-sold at midnight UTC each night, at the last price.\n"
        "• 🏦 <b>Brokerage Fee:</b> A standard <b>1.5% fee</b> applies to both buy and sell trades.\n"
        f"• 📈 <b>Windfall Tax:</b> Selling at 2x+ your buy price adds a {int(PROFIT_TAX_RATE*100)}% tax on the profit portion.\n"
        f"• 📅 <b>Buy Limit:</b> A maximum daily allotment of <b>{config.DAILY_STOCK_BUY_LIMIT} shares</b> (+{AD_BONUS_SHARES} per rewarded ad, up to {AD_MAX_PER_DAY}/day) resets at midnight UTC.\n"
        "━━━━━━━━━━━━━━━━━"
    )


@main_router.message(Command("stockmarket"))
async def stockmarket_cmd(message: Message):
    uid = str(message.from_user.id)
    ensure_user(uid, message.from_user.first_name, message.from_user.username)

    db = load_db()
    if is_stock_banned(db, uid):
        await message.reply(stock_ban_reply_text(db, uid), parse_mode=ParseMode.HTML)
        return

    text = _market_main_text()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛒 Buy Stocks", callback_data=f"sm_bl_{uid}", style=ButtonStyle.SUCCESS),
         InlineKeyboardButton(text="💵 Sell Stocks", callback_data=f"sm_sl_{uid}", style=ButtonStyle.DANGER)],
        [InlineKeyboardButton(text="💼 Your Portfolio", callback_data=f"sm_p_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="💹 Stockmarket", url=STOCKMARKET_APP_LINK, style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="📖 Stock Market Help", callback_data=f"sm_help_{uid}")]
    ])
    
    db = load_db()
    pic = db.get("settings", {}).get("pic_stockmarket")
    
    if pic: await message.reply_photo(photo=pic, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
    else: await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)

@main_router.callback_query(F.data.startswith("sm_m_"))
async def sm_main_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = load_db()
    if is_stock_banned(db, uid):
        await cq.answer(stock_ban_reply_text(db, uid), show_alert=True)
        return

    text = _market_main_text()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛒 Buy Stocks", callback_data=f"sm_bl_{uid}", style=ButtonStyle.SUCCESS),
         InlineKeyboardButton(text="💵 Sell Stocks", callback_data=f"sm_sl_{uid}", style=ButtonStyle.DANGER)],
        [InlineKeyboardButton(text="💼 Your Portfolio", callback_data=f"sm_p_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="💹 Stockmarket", url=STOCKMARKET_APP_LINK, style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="📖 Stock Market Help", callback_data=f"sm_help_{uid}")]
    ])
    
    db = load_db()
    pic = db.get("settings", {}).get("pic_stockmarket")
    
    try:
        if pic:
            await cq.message.edit_media(InputMediaPhoto(media=pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        await cq.answer("🔄 Market Refreshed!", show_alert=False)
    except TelegramBadRequest:
        await cq.answer("⏱️ Prices haven't changed yet.", show_alert=False)
    except Exception:
        pass

@main_router.callback_query(F.data.startswith("sm_help_"))
async def sm_help_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    text = _market_rules_text()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⤶", callback_data=f"sm_m_{uid}", style=ButtonStyle.DANGER)]
    ])

    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        await cq.answer()
    except TelegramBadRequest:
        await cq.answer()
    except Exception:
        pass

@main_router.callback_query(F.data.startswith("sm_bl_"))
async def sm_buy_list_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = load_db()

    if is_stock_banned(db, uid):
        await cq.answer(stock_ban_reply_text(db, uid), show_alert=True)
        return

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    market = db.get("market", {})
    
    text = "<b>「 🛒 MARKET LISTINGS 」</b>\n━━━━━━━━━━━━━━━━━\nSelect an index to inspect financial parameters:\n\n"
    buttons = []
    row = []
    
    for idx, (sym, data) in enumerate(STOCKS.items(), start=1):
        price = market.get(sym, {}).get("current_price", data["base_price"])
        history = market.get(sym, {}).get("history", [price])
        
        old_price = history[0] if history else price
        diff = price - old_price
        pct = (diff / old_price * 100) if old_price > 0 else 0
        
        emoji = "📈" if diff >= 0 else "📉"
        sign = "+" if diff > 0 else ""
        pct_str = f" ({sign}{int(pct)}%)" if diff != 0 else " (0%)"
        
        frozen_tag = ""
        if is_frozen(market.get(sym, {})):
            frozen_tag = f" 🚫 <i>FROZEN ({freeze_time_left_str(market.get(sym, {}))})</i>"

        text += f"<b>{idx})</b> {emoji} <b>{data['name']}</b> ({sym}) - <b>{price} 💠</b><i>{pct_str}</i>{frozen_tag}\n"
        row.append(InlineKeyboardButton(text=str(idx), callback_data=f"sm_v_{uid}_{sym}_1"))
        if len(row) == 5:
            buttons.append(row)
            row = []
            
    if row: buttons.append(row)
    buttons.append([
        InlineKeyboardButton(text="🔄 Refresh", callback_data=f"sm_bl_{uid}", style=ButtonStyle.PRIMARY),
        InlineKeyboardButton(text="⤶", callback_data=f"sm_m_{uid}", style=ButtonStyle.DANGER)
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons), parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons), parse_mode=ParseMode.HTML)
        await cq.answer()
    except TelegramBadRequest:
        await cq.answer("⏱️ Prices haven't changed yet.", show_alert=False)
    except Exception: pass

@main_router.callback_query(F.data.startswith("sm_v_"))
async def sm_view_stock_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid = parts[2]
    sym = parts[3]
    # Check if a specific amount value is passed in the query path, else default to 1
    amount = int(parts[4]) if len(parts) > 4 else 1
    
    if not await verify_user(cq, uid): return

    db = load_db()
    market = db.get("market", {}).get(sym, {})
    
    stock = STOCKS[sym]
    price = market.get("current_price", stock["base_price"])
    history = market.get("history", [price])
    
    trend = "📈 BULLISH" if len(history) > 1 and history[-1] >= history[0] else "📉 BEARISH"
    
    vol = stock["volatility"]
    if vol <= 0.032: risk_level = "🟢 Low Risk (Stable)"
    elif vol <= 0.06: risk_level = "🟡 Medium Risk (Moderate)"
    elif vol <= 0.10: risk_level = "🟠 High Risk (Volatile)"
    else: risk_level = "🔴 Extreme Risk (Gamble)"
    
    base_cost = price * amount
    fee = int(base_cost * config.MARKET_FEE_PCT)
    total_cost = base_cost + fee

    # Retrieve daily buying limit statistics
    today = config.get_shop_rotation_seed()
    daily_stock_data = db["users"].get(uid, {}).get("daily_stock_bought", {"date": "", "amount": 0})
    current_daily_amount = daily_stock_data.get("amount", 0) if daily_stock_data.get("date") == today else 0
    remaining_limit = max(0, _daily_limit(db['users'].get(uid, {})) - current_daily_amount)
    
    caption = (
        f"<b>「 {stock['name']} ({sym}) 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<blockquote><i>High-fidelity analytical chart displaying the last 24 transaction nodes.</i></blockquote>\n\n"
        f"💵 <b>Current Valuation:</b> <b>{price} 💠</b>\n"
        f"📊 <b>24h Direct Trend:</b> <i>{trend}</i>\n"
        f"⚠️ <b>Risk Tier:</b> <b>{risk_level}</b>\n"
        f"📅 <b>Daily Buy Limit:</b> <code>{current_daily_amount}/{_daily_limit(db['users'].get(uid, {}))}</code> shares\n"
        f"📥 <b>Remaining Today:</b> <code>{remaining_limit}</code> shares\n\n"
        f"🛒 <b>Purchase Volume:</b> <b>{amount} shares</b>\n"
        f"💰 <b>Estimated Cost:</b> <b>{total_cost} 💠</b> <i>(incl. 1.5% fee)</i>\n\n"
        f"<i>Brokerage Fee (1.5%) applies automatically on buy executions.</i>"
    )

    frozen = is_frozen(market)
    if frozen:
        caption += (
            f"\n\n🚫 <b>TRADING HALTED</b>\n"
            f"<i>This asset crashed and is frozen for {freeze_time_left_str(market)} more. "
            f"No buying or selling until trading resumes.</i>"
        )
    
    # Calculate amount adjustments safely (ensure minimum of 1 share)
    minus_10 = max(1, amount - 10)
    minus_1 = max(1, amount - 1)
    plus_1 = amount + 1
    plus_10 = amount + 10
    
    buy_row = (
        [InlineKeyboardButton(text=f"🚫 Halted ({freeze_time_left_str(market)})", callback_data="noop", style=ButtonStyle.DANGER)]
        if frozen else
        [InlineKeyboardButton(text=f"🛒 Buy {amount} Share(s)", callback_data=f"sm_cb_{uid}_{sym}_{amount}", style=ButtonStyle.SUCCESS)]
    )

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"📦 {amount}", callback_data="noop")],
        [
            InlineKeyboardButton(text="➖10", callback_data=f"sm_v_{uid}_{sym}_{minus_10}", style=ButtonStyle.DANGER),
            InlineKeyboardButton(text="➖1", callback_data=f"sm_v_{uid}_{sym}_{minus_1}", style=ButtonStyle.DANGER),
            InlineKeyboardButton(text="➕1", callback_data=f"sm_v_{uid}_{sym}_{plus_1}", style=ButtonStyle.SUCCESS),
            InlineKeyboardButton(text="➕10", callback_data=f"sm_v_{uid}_{sym}_{plus_10}", style=ButtonStyle.SUCCESS)
        ],
        buy_row,
        [InlineKeyboardButton(text="⤶", callback_data=f"sm_bl_{uid}", style=ButtonStyle.DANGER)]
    ])
    
    graph_bytes = generate_stock_graph(sym, history)
    photo = BufferedInputFile(graph_bytes.read(), filename=f"{sym}_graph.png")
    
    try:
        if cq.message.photo:
            await cq.message.edit_media(InputMediaPhoto(media=photo, caption=caption, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            await cq.message.delete()
            await cq.message.answer_photo(photo=photo, caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)
        await cq.answer()
    except TelegramBadRequest:
        await cq.answer()
    except Exception:
        pass

# ==========================================
# CONFIRM & EXECUTE BUY
# ==========================================
@main_router.callback_query(F.data.startswith("sm_cb_"))
async def sm_confirm_buy_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    if len(parts) != 5: return
    uid, sym, amount = parts[2], parts[3], int(parts[4])
    if not await verify_user(cq, uid): return
    
    db = load_db()

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    if is_frozen(db.get("market", {}).get(sym, {})):
        await cq.answer(
            f"🚫 Trading on {sym} is halted for {freeze_time_left_str(db['market'][sym])} following a market crash.",
            show_alert=True
        )
        return

    # Midnight reset verify check for stock buy allocation
    today = config.get_shop_rotation_seed()
    daily_stock_data = db["users"].setdefault(uid, {}).setdefault("daily_stock_bought", {"date": "", "amount": 0})
    if daily_stock_data.get("date") != today:
        daily_stock_data["date"] = today
        daily_stock_data["amount"] = 0
        save_db()

    current_daily_amount = daily_stock_data.get("amount", 0)
    if current_daily_amount + amount > _daily_limit(db['users'].get(uid, {})):
        await cq.answer(
            f"❌ Limit Exceeded!\n"
            f"Daily allotment allows buying {_daily_limit(db['users'].get(uid, {}))} shares.\n"
            f"You have already bought {current_daily_amount} shares today.",
            show_alert=True
        )
        return

    price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    base_cost = price * amount
    fee = int(base_cost * config.MARKET_FEE_PCT)
    total_cost = base_cost + fee
    
    caption = (
        f"<b>「 CONFIRM ACQUISITION 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<blockquote><i>Verification required to proceed with asset transfer.</i></blockquote>\n\n"
        f"🏢 <b>Faction:</b> {STOCKS[sym]['name']} ({sym})\n"
        f"📦 <b>Volume:</b> <b>{amount} shares</b>\n"
        f"💵 <b>Base Valuation:</b> {base_cost} 💠\n"
        f"🏦 <b>Brokerage Fee (1.5%):</b> {fee} 💠\n"
        f"📅 <b>Quota Forecast:</b> <code>{current_daily_amount + amount}/{_daily_limit(db['users'].get(uid, {}))}</code> shares\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"💰 <b>Total Deducted:</b> <b>{total_cost} 💠</b>"
    )
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Confirm Buy", callback_data=f"sm_xb_{uid}_{sym}_{amount}", style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="❌ Cancel", callback_data=f"sm_v_{uid}_{sym}_{amount}", style=ButtonStyle.DANGER)]
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(caption, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer()

@main_router.callback_query(F.data.startswith("sm_xb_"))
async def sm_execute_buy_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    if len(parts) != 5: return
    uid, sym, amount = parts[2], parts[3], int(parts[4])
    if not await verify_user(cq, uid): return
    
    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    if is_frozen(db.get("market", {}).get(sym, {})):
        await cq.answer(
            f"🚫 Trading on {sym} is halted for {freeze_time_left_str(db['market'][sym])} following a market crash.",
            show_alert=True
        )
        return

    # Midnight reset check verification for active transaction
    today = config.get_shop_rotation_seed()
    daily_stock_data = db["users"][uid].setdefault("daily_stock_bought", {"date": "", "amount": 0})
    if daily_stock_data.get("date") != today:
        daily_stock_data["date"] = today
        daily_stock_data["amount"] = 0

    current_daily_amount = daily_stock_data.get("amount", 0)
    if current_daily_amount + amount > _daily_limit(db['users'].get(uid, {})):
        await cq.answer(
            f"❌ Quota Exceeded!\n"
            f"This purchase exceeds your remaining daily allowance of {_daily_limit(db['users'].get(uid, {})) - current_daily_amount} shares.",
            show_alert=True
        )
        return

    price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    
    base_cost = price * amount
    fee = int(base_cost * config.MARKET_FEE_PCT)
    total_cost = base_cost + fee
    
    if db["users"][uid].get("nexus_shards", 0) < total_cost:
        await cq.answer(f"❌ Insufficient Shards! You need {total_cost} 💠.", show_alert=True)
        return
        
    db["users"][uid]["nexus_shards"] -= total_cost
    user_stocks = db["users"][uid].setdefault("stocks", {})
    
    if sym not in user_stocks: user_stocks[sym] = {"shares": 0, "avg_price": 0.0}
        
    old_shares = user_stocks[sym]["shares"]
    old_avg = user_stocks[sym]["avg_price"]
    
    new_shares = old_shares + amount
    new_avg = ((old_shares * old_avg) + base_cost) / new_shares
    
    user_stocks[sym]["shares"] = new_shares
    user_stocks[sym]["avg_price"] = new_avg

    # Report this purchase as positive trade flow for the market engine's
    # next tick (net buying nudges price up; reset to 0 after each tick).
    market_entry = db.setdefault("market", {}).setdefault(sym, {"current_price": STOCKS[sym]["base_price"], "history": [STOCKS[sym]["base_price"]], "flow": 0})
    market_entry["flow"] = market_entry.get("flow", 0) + amount

    # Update daily tracking limits
    db["users"][uid]["daily_stock_bought"]["amount"] = current_daily_amount + amount

    # ── Market-wide stats ────────────────────────────────────────────────
    mstats = db.setdefault("market_stats", {})
    mstats["total_buy_orders"] = mstats.get("total_buy_orders", 0) + 1
    mstats["total_shares_bought"] = mstats.get("total_shares_bought", 0) + amount
    mstats["total_shards_spent"] = mstats.get("total_shards_spent", 0) + total_cost
    mstats["total_fees_collected"] = mstats.get("total_fees_collected", 0) + fee

    daily = _touch_market_daily(db)
    daily["buy_orders"] += 1
    daily["shares_bought"] += amount
    daily["shards_spent"] += total_cost
    daily["fees_collected"] += fee

    daily.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["bought"] += amount
    mstats.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["bought"] += amount

    save_db()

    # ── Public Stock Market Log ─────────────────────────────────────────
    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=(
                f"{cq.from_user.full_name} (<code>{uid}</code>) <b>Purchased</b> "
                f"[ {sym} x{amount} ] for <b>{base_cost} shards</b>"
            ),
            message_thread_id=config.LOG_THREAD_STOCKMARKET,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[LOG] Failed to send public stockmarket buy log to Topic {config.LOG_THREAD_STOCKMARKET}: {e}")
    
    success_text = (
        f"<b>「 PURCHASE SUCCESS ✅ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<blockquote><i>Fiduciary transfer complete. Securities moved to your portfolio.</i></blockquote>\n\n"
        f"Acquired <b>{amount}x {sym}</b> shares successfully.\n"
        f"📅 <b>Daily Quota Status:</b> <code>{current_daily_amount + amount}/{_daily_limit(db['users'].get(uid, {}))}</code> shares\n"
        f"💰 <b>Cost:</b> <b>{total_cost} 💠</b> (including brokerage commission)."
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⤶", callback_data=f"sm_bl_{uid}", style=ButtonStyle.DANGER)]])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer(f"✅ Bought {amount}x {sym}!", show_alert=True)

# ==========================================
# PORTFOLIO VIEW
# ==========================================
@main_router.callback_query(F.data.startswith("sm_p_"))
async def sm_portfolio_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)

    if is_stock_banned(db, uid):
        await cq.answer(stock_ban_reply_text(db, uid), show_alert=True)
        return

    my_stocks = db["users"][uid].get("stocks", {})
    market = db.get("market", {})
    
    if not my_stocks:
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⤶", callback_data=f"sm_m_{uid}", style=ButtonStyle.DANGER)]])
        prev_day_tracker = _touch_user_stock_daily(db["users"][uid])
        prev_day_profit = prev_day_tracker.get("prev_day_profit", 0)
        prev_day_status = "🟢" if prev_day_profit >= 0 else "🔴"
        save_db()
        text_empty = (
            "<b>「 💼 YOUR PORTFOLIO 」</b>\n━━━━━━━━━━━━━━━━━\n"
            "You do not own any stocks.\n\n"
            f"📅 <b>Previous Day Profit:</b> <b>{prev_day_profit} 💠 {prev_day_status}</b>"
        )
        try:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text_empty, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text_empty, reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception: pass
        return

    text = f"<b>「 💼 {cq.from_user.first_name}'s PORTFOLIO 」</b>\n━━━━━━━━━━━━━━━━━\n\n"
    total_val = 0
    total_prof = 0
    
    for sym, data in my_stocks.items():
        if data["shares"] <= 0: continue
        current_price = market.get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
        avg_price = data["avg_price"]
        shares = data["shares"]
        
        val = current_price * shares
        prof = int((current_price - avg_price) * shares)
        total_val += val
        total_prof += prof
        
        status = "🟢" if prof >= 0 else "🔴"
        text += f"🏢 <b>{STOCKS[sym]['name']} ({sym})</b>\n"
        text += f"📦 Shares: <b>{shares}</b> | Avg Buy: <i>{int(avg_price)} 💠</i>\n"
        text += f"💰 Value: <b>{val} 💠</b> | P/L: <b>{prof} {status}</b>\n\n"
        
    status_total = "🟢" if total_prof >= 0 else "🔴"
    text += "━━━━━━━━━━━━━━━━━\n"
    text += f"🏦 <b>Total Value:</b> <b>{total_val} 💠</b>\n"
    text += f"📈 <b>Net Profit/Loss:</b> <b>{total_prof} {status_total}</b>\n"

    prev_day_tracker = _touch_user_stock_daily(db["users"][uid])
    prev_day_profit = prev_day_tracker.get("prev_day_profit", 0)
    prev_day_status = "🟢" if prev_day_profit >= 0 else "🔴"
    save_db()
    text += f"📅 <b>Previous Day Profit:</b> <b>{prev_day_profit} 💠 {prev_day_status}</b>"

    sell_style = ButtonStyle.SUCCESS if total_prof >= 0 else ButtonStyle.DANGER
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💵 Sell Stocks", callback_data=f"sm_sl_{uid}", style=sell_style)],
        [InlineKeyboardButton(text="🔄 Refresh", callback_data=f"sm_p_{uid}"),
         InlineKeyboardButton(text="⤶", callback_data=f"sm_m_{uid}", style=ButtonStyle.DANGER)]
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        await cq.answer()
    except TelegramBadRequest:
        await cq.answer("⏱️ Portfolio values haven't changed yet.", show_alert=False)
    except Exception: pass

# ==========================================
# SELL FLOW & EXECUTION
# ==========================================
@main_router.callback_query(F.data.startswith("sm_sl_"))
async def sm_sell_list_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)

    if is_stock_banned(db, uid):
        await cq.answer(stock_ban_reply_text(db, uid), show_alert=True)
        return

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    my_stocks = db["users"][uid].get("stocks", {})
    market = db.get("market", {})
    
    buttons = []
    row = []
    text = "<b>「 💵 LIQUIDATE STOCKS 」</b>\n━━━━━━━━━━━━━━━━━\nSelect an asset from your active portfolio to liquidate:\n\n"
    
    idx = 1
    for sym, data in my_stocks.items():
        if data["shares"] > 0:
            current_price = market.get(sym, {}).get("current_price", STOCKS.get(sym, {}).get("base_price", 0))
            frozen_tag = " 🚫 <i>FROZEN</i>" if is_frozen(market.get(sym, {})) else ""
            text += f"<b>{idx})</b> 💵 <b>{STOCKS.get(sym, {}).get('name', sym)}</b>{frozen_tag}\n   └ 📦 Volume: <b>{data['shares']}</b> | Price: <b>{current_price} 💠</b>\n"
            
            row.append(InlineKeyboardButton(text=str(idx), callback_data=f"sm_sv_{uid}_{sym}"))
            if len(row) == 5:
                buttons.append(row)
                row = []
            idx += 1
            
    if idx == 1:
        await cq.answer("❌ You don't own any stocks to sell.", show_alert=True)
        return
        
    if row: buttons.append(row)
    buttons.append([
        InlineKeyboardButton(text="🔄 Refresh", callback_data=f"sm_sl_{uid}"),
        InlineKeyboardButton(text="⤶", callback_data=f"sm_m_{uid}", style=ButtonStyle.DANGER)
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons), parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons), parse_mode=ParseMode.HTML)
        await cq.answer()
    except TelegramBadRequest:
        await cq.answer("⏱️ Prices haven't changed yet.", show_alert=False)
    except Exception: pass

@main_router.callback_query(F.data.startswith("sm_sv_"))
async def sm_sellview_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, sym = parts[2], parts[3]
    if not await verify_user(cq, uid): return

    db = load_db()

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    shares_owned = db["users"].get(uid, {}).get("stocks", {}).get(sym, {}).get("shares", 0)
    
    if shares_owned <= 0:
        await cq.answer("❌ You don't own this stock anymore.", show_alert=True)
        return

    if sym not in STOCKS:
        await cq.answer("❌ Unknown stock symbol.", show_alert=True)
        return

    if is_frozen(db.get("market", {}).get(sym, {})):
        await cq.answer(
            f"🚫 Trading on {sym} is halted for {freeze_time_left_str(db['market'][sym])} following a market crash.",
            show_alert=True
        )
        return
        
    current_price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    
    text = (
        f"<b>「 SELL {sym} 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"📦 <b>You own:</b> <b>{shares_owned} shares</b>\n"
        f"💵 <b>Market Price:</b> <b>{current_price} 💠</b>\n\n"
        f"<i>A 1.5% brokerage commission is deducted from the payout automatically. "
        f"Sales at {int(PROFIT_TAX_THRESHOLD*100)}%+ profit also incur a {int(PROFIT_TAX_RATE*100)}% windfall tax on the profit portion.</i>"
    )
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Sell x1", callback_data=f"sm_cs_{uid}_{sym}_1", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="Sell x5", callback_data=f"sm_cs_{uid}_{sym}_5", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="Sell x10", callback_data=f"sm_cs_{uid}_{sym}_10", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="Sell ALL", callback_data=f"sm_cs_{uid}_{sym}_{shares_owned}", style=ButtonStyle.DANGER)],
        [InlineKeyboardButton(text="⤶", callback_data=f"sm_sl_{uid}", style=ButtonStyle.DANGER)]
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass

@main_router.callback_query(F.data.startswith("sm_cs_"))
async def sm_confirm_sell_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    if len(parts) != 5: return
    uid, sym, amount = parts[2], parts[3], int(parts[4])
    if not await verify_user(cq, uid): return
    
    db = load_db()

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    shares_owned = db["users"].get(uid, {}).get("stocks", {}).get(sym, {}).get("shares", 0)
    
    if shares_owned < amount:
        await cq.answer("❌ You don't have enough shares to sell this amount.", show_alert=True)
        return

    if is_frozen(db.get("market", {}).get(sym, {})):
        await cq.answer(
            f"🚫 Trading on {sym} is halted for {freeze_time_left_str(db['market'][sym])} following a market crash.",
            show_alert=True
        )
        return
        
    price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    avg_price = db["users"].get(uid, {}).get("stocks", {}).get(sym, {}).get("avg_price", price)
    gross_payout = price * amount
    fee = int(gross_payout * config.MARKET_FEE_PCT)

    cost_basis = avg_price * amount
    profit = gross_payout - cost_basis
    profit_tax = 0
    if avg_price > 0 and price >= avg_price * PROFIT_TAX_THRESHOLD and profit > 0:
        profit_tax = int(profit * PROFIT_TAX_RATE)

    net_payout = gross_payout - fee - profit_tax
    tax_line = f"📈 <b>Windfall Tax ({int(PROFIT_TAX_RATE*100)}%):</b> -{profit_tax} 💠\n" if profit_tax > 0 else ""

    caption = (
        f"<b>「 CONFIRM SALE 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<blockquote><i>Verification required to proceed with asset liquidation.</i></blockquote>\n\n"
        f"🏢 <b>Faction:</b> {STOCKS[sym]['name']} ({sym})\n"
        f"📦 <b>Volume:</b> <b>{amount} shares</b>\n"
        f"💵 <b>Market Value:</b> {gross_payout} 💠\n"
        f"🏦 <b>Brokerage Fee (1.5%):</b> -{fee} 💠\n"
        f"{tax_line}"
        f"━━━━━━━━━━━━━━━━━\n"
        f"💰 <b>Net Payout:</b> <b>{net_payout} 💠</b>"
    )
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Confirm Sell", callback_data=f"sm_xs_{uid}_{sym}_{amount}", style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="❌ Cancel", callback_data=f"sm_sv_{uid}_{sym}", style=ButtonStyle.DANGER)]
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(caption, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer()

@main_router.callback_query(F.data.startswith("sm_xs_"))
async def sm_execute_sell_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    if len(parts) != 5: return
    uid, sym, amount = parts[2], parts[3], int(parts[4])
    if not await verify_user(cq, uid): return
    
    db = load_db()

    if not is_trading_open(db):
        await cq.answer("𝗦𝘁𝗼𝗰𝗸𝗺𝗮𝗿𝗸𝗲𝘁 𝗶𝘀 𝗖𝗹𝗼𝘀𝗲𝗱 𝗼𝗻 𝗦𝗮𝘁𝘂𝗿𝗱𝗮𝘆 𝗮𝗻𝗱 𝗦𝘂𝗻𝗱𝗮𝘆.\n\nIt will be available from Monday - Friday", show_alert=True)
        return

    user_stocks = db["users"].get(uid, {}).get("stocks", {})
    shares_owned = user_stocks.get(sym, {}).get("shares", 0)
    
    if shares_owned < amount:
        await cq.answer(f"❌ You only have {shares_owned} shares of {sym}!", show_alert=True)
        return

    if is_frozen(db.get("market", {}).get(sym, {})):
        await cq.answer(
            f"🚫 Trading on {sym} is halted for {freeze_time_left_str(db['market'][sym])} following a market crash.",
            show_alert=True
        )
        return
        
    price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    avg_price = user_stocks.get(sym, {}).get("avg_price", price)
    gross_payout = price * amount
    fee = int(gross_payout * config.MARKET_FEE_PCT)

    cost_basis = avg_price * amount
    profit = gross_payout - cost_basis
    profit_tax = 0
    if avg_price > 0 and price >= avg_price * PROFIT_TAX_THRESHOLD and profit > 0:
        profit_tax = int(profit * PROFIT_TAX_RATE)

    net_payout = gross_payout - fee - profit_tax
    
    db["users"][uid]["nexus_shards"] = db["users"][uid].get("nexus_shards", 0) + net_payout
    user_stocks[sym]["shares"] -= amount
    
    if user_stocks[sym]["shares"] <= 0: del user_stocks[sym]

    daily_tracker = _touch_user_stock_daily(db["users"][uid])
    daily_tracker["profit"] += int(net_payout - cost_basis)

    # Report this sale as negative trade flow for the market engine's next
    # tick (net selling nudges price down; reset to 0 after each tick).
    market_entry = db.setdefault("market", {}).setdefault(sym, {"current_price": STOCKS[sym]["base_price"], "history": [STOCKS[sym]["base_price"]], "flow": 0})
    market_entry["flow"] = market_entry.get("flow", 0) - amount

    # ── Market-wide stats ────────────────────────────────────────────────
    mstats = db.setdefault("market_stats", {})
    mstats["total_sell_orders"] = mstats.get("total_sell_orders", 0) + 1
    mstats["total_shares_sold"] = mstats.get("total_shares_sold", 0) + amount
    mstats["total_shards_generated"] = mstats.get("total_shards_generated", 0) + net_payout
    mstats["total_fees_collected"] = mstats.get("total_fees_collected", 0) + fee
    mstats["total_windfall_tax_collected"] = mstats.get("total_windfall_tax_collected", 0) + profit_tax

    daily = _touch_market_daily(db)
    daily["sell_orders"] += 1
    daily["shares_sold"] += amount
    daily["shards_generated"] += net_payout
    daily["fees_collected"] += fee
    daily["windfall_tax_collected"] += profit_tax

    daily.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["sold"] += amount
    mstats.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["sold"] += amount

    save_db()

    log_action(db, uid, {
        "type": "market_sell",
        "amount": net_payout,
        "symbol": sym,
        "shares": amount,
        "profit": int(profit),
        "chat_id": cq.message.chat.id,
        "chat_title": cq.message.chat.title or cq.message.chat.first_name or "DM"
    })

    # ── Public Stock Market Log ─────────────────────────────────────────
    profit_int = int(profit)
    pl_label = f"(Profit: {profit_int})" if profit_int >= 0 else f"(Loss: {abs(profit_int)})"
    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=(
                f"{cq.from_user.full_name} (<code>{uid}</code>) <b>Sold</b> "
                f"[ {sym} x{amount} ] for <b>{gross_payout} shards</b> {pl_label}"
            ),
            message_thread_id=config.LOG_THREAD_STOCKMARKET,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[LOG] Failed to send public stockmarket sell log to Topic {config.LOG_THREAD_STOCKMARKET}: {e}")
    
    tax_note = f" (incl. {int(PROFIT_TAX_RATE*100)}% windfall tax on profit)" if profit_tax > 0 else ""
    success_text = (
        f"<b>「 SALE SUCCESS ✅ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<blockquote><i>Liquidation sequence resolved successfully.</i></blockquote>\n\n"
        f"Sold <b>{amount}x {sym}</b> shares.\n"
        f"💰 <b>Net Deposited:</b> <b>{net_payout} 💠</b> (commission processed{tax_note})."
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⤶", callback_data=f"sm_p_{uid}", style=ButtonStyle.DANGER)]])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer(f"✅ Sold {amount}x {sym}!", show_alert=True)


# ==========================================================================
# MINI APP WEB API  (/api/market)  —  backs market.html
# ==========================================================================
# Endpoints used by market.html:
#   GET  /api/market/state        -> full state snapshot
#   POST /api/market/buy   {symbol, amount}  -> {state, message}
#   POST /api/market/sell  {symbol, amount}  -> {state, message}
# Every request carries the Telegram Mini App initData in the
# X-Telegram-Init-Data header; it is verified server-side, so the user id is
# never taken from the client body.
import json
import hmac
import hashlib
from urllib.parse import parse_qsl
from fastapi import APIRouter, HTTPException, Header
from pydantic import BaseModel

market_api = APIRouter(prefix="/api/market", tags=["Market"])


def _verify_init_data(init_data: str, max_age: int = 86400):
    """Returns the Telegram user dict if Mini App initData is genuine and fresh, else None."""
    try:
        pairs = dict(parse_qsl(init_data or "", keep_blank_values=True))
        recv_hash = pairs.pop("hash", None)
        if not recv_hash:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", config.bot.token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, recv_hash):
            return None
        if time.time() - int(pairs.get("auth_date", "0")) > max_age:
            return None
        return json.loads(pairs.get("user", "{}"))
    except Exception:
        return None


def _auth_user(init_data: str) -> dict:
    tg_user = _verify_init_data(init_data)
    if not tg_user or not tg_user.get("id"):
        raise HTTPException(status_code=401, detail="Open this page from the bot in Telegram.")
    return tg_user


def _build_market_state(db: dict, uid: str) -> dict:
    market = db.get("market", {})
    udata = db["users"].get(uid, {})

    stocks = []
    prices = {}
    for sym, info in STOCKS.items():
        entry = market.get(sym, {})
        price = entry.get("current_price", info["base_price"])
        hist = list(entry.get("history") or [price])
        prev = hist[0] if hist and hist[0] > 0 else (price or 1)
        prices[sym] = price
        stocks.append({
            "sym": sym,
            "name": info["name"],
            "price": price,
            "prev": prev,
            "vol": info["volatility"],
            "hist": hist,
            "frozen": is_frozen(entry),
        })

    positions = []
    total_value = 0
    total_pl = 0
    for sym, pos in (udata.get("stocks") or {}).items():
        shares = pos.get("shares", 0)
        if shares <= 0 or sym not in STOCKS:
            continue
        avg = pos.get("avg_price", prices[sym])
        value = prices[sym] * shares
        pl = int((prices[sym] - avg) * shares)
        total_value += value
        total_pl += pl
        positions.append({"sym": sym, "shares": shares, "avg": avg, "value": value, "pl": pl})

    tracker = _touch_user_stock_daily(udata) if udata else {"profit": 0, "prev_day_profit": 0}
    today = config.get_shop_rotation_seed()
    dsb = udata.get("daily_stock_bought", {"date": "", "amount": 0})
    bought_today = dsb.get("amount", 0) if dsb.get("date") == today else 0
    ads_watched = _market_ad_watched(udata) if udata else 0

    return {
        "open": is_trading_open(db),
        "stocks": stocks,
        "user": {
            "id": uid,
            "name": udata.get("name", "Trader"),
            "username": udata.get("username"),
            "shards": udata.get("nexus_shards", 0),
            "banned": is_stock_banned(db, uid),
            "positions": positions,
            "total_value": total_value,
            "total_pl": total_pl,
            "today_profit": tracker.get("profit", 0),
            "prev_profit": tracker.get("prev_day_profit", 0),
            "bought_today": bought_today,
            "cards": len(udata.get("cards") or {}),
            "ads_watched": ads_watched,
            "ads_max": AD_MAX_PER_DAY,
            "ad_bonus": AD_BONUS_SHARES,
        },
        "cfg": {
            "limit": config.DAILY_STOCK_BUY_LIMIT + ads_watched * AD_BONUS_SHARES,
            "fee": config.MARKET_FEE_PCT,
            "tax_rate": PROFIT_TAX_RATE,
            "tax_mult": PROFIT_TAX_THRESHOLD,
        },
    }


def _web_ctx(init_data: str):
    tg_user = _auth_user(init_data)
    uid = str(tg_user["id"])
    if is_ghost_banned(int(uid)) or is_shadow_banned(int(uid)):
        raise HTTPException(status_code=403, detail="You are currently restricted.")
    db = ensure_user(uid, tg_user.get("first_name", "Trader"), tg_user.get("username"))
    # keep username fresh for the profile screen
    db["users"][uid]["username"] = tg_user.get("username")
    return db, uid, tg_user


class TradeRequest(BaseModel):
    symbol: str
    amount: int


def _check_trade_common(db: dict, uid: str, sym: str, amount: int):
    if sym not in STOCKS:
        raise HTTPException(status_code=400, detail="Unknown stock.")
    if amount < 1 or amount > 100000:
        raise HTTPException(status_code=400, detail="Invalid amount.")
    if is_stock_banned(db, uid):
        raise HTTPException(status_code=403, detail="You are restricted from the Stock Market.")
    if not is_trading_open(db):
        raise HTTPException(status_code=400, detail="Market is closed on Saturday and Sunday.")
    if is_frozen(db.get("market", {}).get(sym, {})):
        raise HTTPException(
            status_code=400,
            detail=f"{sym} is halted for {freeze_time_left_str(db['market'][sym])} after a crash.",
        )


@market_api.get("/state")
async def market_web_state(x_telegram_init_data: str = Header(default="")):
    db, uid, _ = _web_ctx(x_telegram_init_data)
    state = _build_market_state(db, uid)
    save_db()  # persists the daily-profit rollover done by _touch_user_stock_daily
    return state


@market_api.post("/buy")
async def market_web_buy(req: TradeRequest, x_telegram_init_data: str = Header(default="")):
    db, uid, tg_user = _web_ctx(x_telegram_init_data)
    sym, amount = req.symbol.upper(), req.amount
    _check_trade_common(db, uid, sym, amount)

    udata = db["users"][uid]
    today = config.get_shop_rotation_seed()
    dsb = udata.setdefault("daily_stock_bought", {"date": "", "amount": 0})
    if dsb.get("date") != today:
        dsb["date"] = today
        dsb["amount"] = 0
    current = dsb.get("amount", 0)
    limit_now = _daily_limit(udata)
    if current + amount > limit_now:
        raise HTTPException(
            status_code=400,
            detail=f"Daily limit: {max(0, limit_now - current)} shares left today. Watch an ad for more.",
        )

    market_entry = db.setdefault("market", {}).setdefault(
        sym, {"current_price": STOCKS[sym]["base_price"], "history": [STOCKS[sym]["base_price"]], "flow": 0}
    )
    price = market_entry.get("current_price", STOCKS[sym]["base_price"])
    base_cost = price * amount
    fee = int(base_cost * config.MARKET_FEE_PCT)
    total_cost = base_cost + fee

    if udata.get("nexus_shards", 0) < total_cost:
        raise HTTPException(status_code=400, detail=f"Not enough Shards. You need {total_cost}.")

    udata["nexus_shards"] -= total_cost
    user_stocks = udata.setdefault("stocks", {})
    pos = user_stocks.setdefault(sym, {"shares": 0, "avg_price": 0.0})
    new_shares = pos["shares"] + amount
    pos["avg_price"] = ((pos["shares"] * pos["avg_price"]) + base_cost) / new_shares
    pos["shares"] = new_shares

    market_entry["flow"] = market_entry.get("flow", 0) + amount
    dsb["amount"] = current + amount

    mstats = db.setdefault("market_stats", {})
    mstats["total_buy_orders"] = mstats.get("total_buy_orders", 0) + 1
    mstats["total_shares_bought"] = mstats.get("total_shares_bought", 0) + amount
    mstats["total_shards_spent"] = mstats.get("total_shards_spent", 0) + total_cost
    mstats["total_fees_collected"] = mstats.get("total_fees_collected", 0) + fee
    daily = _touch_market_daily(db)
    daily["buy_orders"] += 1
    daily["shares_bought"] += amount
    daily["shards_spent"] += total_cost
    daily["fees_collected"] += fee
    daily.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["bought"] += amount
    mstats.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["bought"] += amount
    save_db()

    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=(f"{_html_esc(tg_user.get('first_name', 'User'))} (<code>{uid}</code>) <b>Purchased</b> "
                  f"[ {sym} x{amount} ] for <b>{base_cost} shards</b> (Web)"),
            message_thread_id=config.LOG_THREAD_STOCKMARKET,
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        print(f"[LOG] web buy log failed: {e}")

    return {"state": _build_market_state(db, uid), "message": f"Bought {amount}x {sym} for {total_cost}"}


@market_api.post("/sell")
async def market_web_sell(req: TradeRequest, x_telegram_init_data: str = Header(default="")):
    db, uid, tg_user = _web_ctx(x_telegram_init_data)
    sym, amount = req.symbol.upper(), req.amount
    _check_trade_common(db, uid, sym, amount)

    udata = db["users"][uid]
    user_stocks = udata.get("stocks", {})
    owned = user_stocks.get(sym, {}).get("shares", 0)
    if owned < amount:
        raise HTTPException(status_code=400, detail=f"You only own {owned} shares of {sym}.")

    price = db.get("market", {}).get(sym, {}).get("current_price", STOCKS[sym]["base_price"])
    avg_price = user_stocks[sym].get("avg_price", price)
    gross = price * amount
    fee = int(gross * config.MARKET_FEE_PCT)
    cost_basis = avg_price * amount
    profit = gross - cost_basis
    profit_tax = 0
    if avg_price > 0 and price >= avg_price * PROFIT_TAX_THRESHOLD and profit > 0:
        profit_tax = int(profit * PROFIT_TAX_RATE)
    net = gross - fee - profit_tax

    udata["nexus_shards"] = udata.get("nexus_shards", 0) + net
    user_stocks[sym]["shares"] -= amount
    if user_stocks[sym]["shares"] <= 0:
        del user_stocks[sym]

    tracker = _touch_user_stock_daily(udata)
    tracker["profit"] += int(net - cost_basis)

    market_entry = db.setdefault("market", {}).setdefault(
        sym, {"current_price": STOCKS[sym]["base_price"], "history": [STOCKS[sym]["base_price"]], "flow": 0}
    )
    market_entry["flow"] = market_entry.get("flow", 0) - amount

    mstats = db.setdefault("market_stats", {})
    mstats["total_sell_orders"] = mstats.get("total_sell_orders", 0) + 1
    mstats["total_shares_sold"] = mstats.get("total_shares_sold", 0) + amount
    mstats["total_shards_generated"] = mstats.get("total_shards_generated", 0) + net
    mstats["total_fees_collected"] = mstats.get("total_fees_collected", 0) + fee
    mstats["total_windfall_tax_collected"] = mstats.get("total_windfall_tax_collected", 0) + profit_tax
    daily = _touch_market_daily(db)
    daily["sell_orders"] += 1
    daily["shares_sold"] += amount
    daily["shards_generated"] += net
    daily["fees_collected"] += fee
    daily["windfall_tax_collected"] += profit_tax
    daily.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["sold"] += amount
    mstats.setdefault("by_symbol", {}).setdefault(sym, {"bought": 0, "sold": 0})["sold"] += amount
    save_db()

    log_action(db, uid, {
        "type": "market_sell", "amount": net, "symbol": sym, "shares": amount,
        "profit": int(profit), "chat_id": "web", "chat_title": "Web App",
    })

    profit_int = int(profit)
    pl_label = f"(Profit: {profit_int})" if profit_int >= 0 else f"(Loss: {abs(profit_int)})"
    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=(f"{_html_esc(tg_user.get('first_name', 'User'))} (<code>{uid}</code>) <b>Sold</b> "
                  f"[ {sym} x{amount} ] for <b>{gross} shards</b> {pl_label} (Web)"),
            message_thread_id=config.LOG_THREAD_STOCKMARKET,
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        print(f"[LOG] web sell log failed: {e}")

    return {"state": _build_market_state(db, uid), "message": f"Sold {amount}x {sym} for {net}"}


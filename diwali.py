"""
diwali.py — Diwali 🪔 event for Anime Nexus (login event only)
==============================================================
Imports ONLY from config (never from deck.py / handlers.py) so both of
those files can import this one without a circular import.

What it adds
  • Login event              — ONE 7-night event, claimed in diwali.html by watching ads (Adsgram):
                               night 1 = 1 ad -> 1,000 shards ... night 7 = 4 ads -> random Diwali card +
                               3,000 shards (see LOGIN_EVENT). Catch-up is OFF until an admin turns it on with /stcatchup.
  • Diwali edition cards     — any global card with "🪔" in its name, or event == "diwali". Flex / inline
                               captions get the "This is a diwali (🪔) edition card !" line.
  • Player commands          — /diwali (event clock + Mini App button), /dwlogin (calendar + tonight's ads),
                               /dwhelp
  • Web API                  — get_router() returns a FastAPI router used by diwali.html:
                               POST /diwali/state | /diwali/login | GET /diwali/ads/reward (Adsgram postback)
                               mount once:  app.include_router(diwali.get_router(), prefix="/api")
  • Admin commands (owner + admins only)
        /stdw on [days]          start the login event (or resume if paused)
        /stdw login on|off [d]   turn the 7-night login event on / off
        /stcatchup on|off        catch-up for missed nights (OFF until an admin turns it on)
        /stdw extend <days>      add days to the running event
        /stdw decrease [days]    remove days from the running event (default 1)
        /stdw pause              freeze the event; remaining time is kept
        /stdw status             state, day number, login switch, card counts
        /stdw off                end the event now
        /stdw fixlogin           restore wiped login nights + forgive missed nights
        /stdw setlogin <user_id> <nights>   set one player's login night
        /dcard on <db-id>        mark an existing card as a Diwali card
        /dcard off <db-id>       remove the mark
        /dcard list              list all Diwali cards
        /dwstats                 ads, login progress per night, card counts
  • Diwali cards can be sold, bought, traded and gifted, but can't be burned (see dw_locked()).
  • Marking: upload the card as usual (/add_card), then /dcard on <db-id>.

Hooks (small edits in deck.py / handlers.py):
  diwali_flex_line(global_card)        -> caption suffix
  maybe_diwali_drop(db, pool, rarity)  -> no-op: drops are NOT boosted
  award_seize_candies(db, user, card)  -> no-op (returns 0)
  quest_progress(...)                  -> no-op
  dw_locked(db, card_id) / dw_lock_text(action) -> blocks burn only
  importing this module registers the commands on main_router.
"""
import hashlib
import hmac
import json
import random
import re
import time
from urllib.parse import parse_qsl
from datetime import datetime, timedelta, timezone
from html import escape as _esc

from aiogram import F
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject
from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup, Message

from config import (
    bot, main_router, ADMIN_IDS, SUPREME_OWNER_ID, ensure_user, load_db, save_db,
    format_rarity, is_ghost_banned, is_shadow_banned,
)

# ==========================================
# SETTINGS
# ==========================================
DW_EMOJI = "🪔"
DW_EVENT_KEY = "diwali"
DIVINE_RARITY = "Divine ❄️"      # the Divine rarity counted in /dwstats and /dcard list
DEFAULT_EVENT_DAYS = 9          # event length in UTC days (day 1 = the day it is started)

# The ONE login event: 7 nights, each claimed in diwali.html after watching `ads` rewarded ads.
#   "shards": Nexus Shards   "card": random NON-Diwali card of that rarity
#   "dwcard": random Diwali card (from the Diwali pool; locked series are fine)
LOGIN_EVENT = (
    {"ads": 1, "shards": 1000},
    {"ads": 1, "card": "Basic 🃏"},
    {"ads": 2, "shards": 1500},
    {"ads": 2, "card": "Elite ⚓"},
    {"ads": 2, "shards": 2000},
    {"ads": 3, "card": "Divine ❄️"},
    {"ads": 4, "shards": 3000, "dwcard": ("Divine ❄️",)},
)
# Adsgram reward postback (create a rewarded block in the Adsgram dashboard and set its reward URL to):
#   https://<your-worker>/api/diwali/ads/reward?userid=[userId]&secret=<DW_AD_SECRET>   (&key=... also works)
DW_AD_SECRET = "gUz6e7bs0-TrdtHVtx7EAM63mMpfvQsc"   # same secret as ADSGRAM_REWARD_SECRET in deck.py
# Catch-up window: when this many event days (or fewer) are left, or the event is past night 7, a player can
# watch the ads of ALL missed nights together and claim them in one go (no reset to night 1).
LOGIN_CATCHUP_DAYS_LEFT = 2

# Mini App (diwali.html)
DW_WEBAPP_URL = ""               # https URL where diwali.html is hosted (optional)
DW_MINIAPP_LINK = "https://t.me/Animenx_bot/Diwali"   # direct Mini App link (works in groups and private chats)
DW_REQUIRE_INITDATA = True       # verify Telegram initData on every web API call

# ==========================================
# HELPERS (importable from deck.py / handlers.py)
# ==========================================
def is_diwali_card(global_card: dict) -> bool:
    if not isinstance(global_card, dict):
        return False
    return global_card.get("event") == DW_EVENT_KEY or DW_EMOJI in str(global_card.get("name", ""))


def diwali_flex_line(global_card: dict) -> str:
    """Caption suffix for flex/inline captions ('' for normal cards)."""
    if is_diwali_card(global_card):
        return f"\n\n<b><i>This is a diwali ({DW_EMOJI}) edition card !</i></b>"
    return ""


def _state(db: dict) -> dict:
    return db.setdefault("settings", {}).setdefault(DW_EVENT_KEY, {})


def event_seconds_left(db: dict) -> int:
    st = _state(db)
    ends = st.get("ends_at", 0)
    if not st.get("active") or not ends:
        return 0
    left = int(ends - time.time())
    if left <= 0:
        st["active"] = False
        st.pop("ends_at", None)
        save_db()
        return 0
    return left


def event_active(db: dict) -> bool:
    return event_seconds_left(db) > 0


def dw_locked(db: dict, card_id) -> bool:
    """True if this card is a Diwali card (can't be burned; sell/buy/trade/gift are allowed)."""
    return is_diwali_card(db.get("global_cards", {}).get(card_id))


def dw_lock_text(action: str) -> str:
    return f"{DW_EMOJI} <b>Diwali cards cannot be {action}.</b>"


def event_day(db: dict):
    """(current day number, total days) of the running event, or None. Paused time doesn't count."""
    st = _state(db)
    sd, total = st.get("start_date"), st.get("days")
    if not (sd and total):
        return None
    try:
        d0 = datetime.strptime(sd, "%Y-%m-%d").replace(tzinfo=timezone.utc).timestamp()
    except ValueError:
        return None
    ref = st.get("paused_at") or time.time()
    n = int((ref - d0 - st.get("paused_total", 0)) // 86400) + 1
    return max(1, min(n, int(total))), int(total)


def _today() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def quest_progress(user_id, key: str, amount: int = 1, db: dict | None = None) -> None:
    """No-op hook. Daily quests were removed; this stays only so existing calls in deck.py / handlers.py don't break."""
    return None


def _diwali_pool(db: dict, rarity: str | None = None) -> dict:
    out = {}
    for cid, c in db.get("global_cards", {}).items():
        if not is_diwali_card(c):
            continue
        if rarity and format_rarity(c.get("rarity", "")) != rarity:
            continue
        out[cid] = c
    return out


def maybe_diwali_drop(db: dict, pool: dict, target_rarity: str) -> dict:
    """Kept so the hook in trigger_drop keeps working. Drops are NOT boosted any more:
    the pool is returned unchanged."""
    return pool


def _fmt_left(sec: int) -> str:
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m = r // 60
    return f"{d}d {h}h {m}m" if d else f"{h}h {m}m"


def _ev_on(db: dict, uid=None) -> bool:
    """True while the Diwali event is running."""
    return event_active(db)


def _add_shards(user: dict, n: int) -> None:
    """Give Nexus Shards."""
    user["nexus_shards"] = user.get("nexus_shards", 0) + int(n)


def _feature_on(db: dict, key: str, uid=None) -> bool:
    """Event running AND the part switched on. The owner can always use both parts while the event runs."""
    if not event_active(db):
        return False
    if uid is not None and str(uid) == str(SUPREME_OWNER_ID):
        return True
    return bool(_state(db).get(key, True))


def catchup_enabled(db: dict) -> bool:
    """Catch-up for missed nights. OFF by default; admins switch it with /stcatchup on|off."""
    return bool(_state(db).get("catchup_on", False))


def login_enabled(db: dict, uid=None) -> bool:
    """Login part on (/stdw login on|off); the owner bypasses the switch."""
    return _feature_on(db, "login_on", uid)


def _is_admin(message: Message) -> bool:
    """The owner and the admins can use the admin commands."""
    uid = message.from_user.id
    return uid == SUPREME_OWNER_ID or uid in ADMIN_IDS


# ==========================================
# ADMIN COMMANDS
# ==========================================
def _dw_status_text(db: dict) -> str:
    st = _state(db)
    left = event_seconds_left(db)
    dn = event_day(db)
    if st.get("paused_at"):
        rem = max(0, int(st.get("ends_at", 0) - st["paused_at"]))
        state = f"PAUSED — {_fmt_left(rem)} left when resumed"
    elif left:
        state = f"ON — {_fmt_left(left)} left" + (f" (Day {dn[0]}/{dn[1]})" if dn else "")
    else:
        state = "OFF"
    pool = _diwali_pool(db)
    divines = sum(1 for c in pool.values() if format_rarity(c.get("rarity", "")) == DIVINE_RARITY)
    sw = "ON" if st.get("login_on", True) else "OFF"
    return (f"<b>Diwali event:</b> {state}\n"
            f"<b>Login:</b> {sw}  •  <b>Catch-up:</b> {'ON' if catchup_enabled(db) else 'OFF'}\n"
            f"<b>Diwali cards:</b> {len(pool)}  (Divine: {divines})")


def _plain(text: str) -> str:
    """Text without emojis (admin replies are plain text)."""
    return re.sub(r"[\U0001F300-\U0001FAFF\u2600-\u27BF\ufe0f]", "", str(text)).strip()


def _btn(text: str, style: str | None = None, **kw) -> InlineKeyboardButton:
    """Inline button with an optional Telegram colour style ("primary" | "success" | "danger").
    Falls back to a plain button if this aiogram version rejects the style field."""
    if style:
        try:
            return InlineKeyboardButton(text=text, style=style, **kw)
        except Exception:
            pass
    return InlineKeyboardButton(text=text, **kw)


_IMG_FILE_IDS: dict = {}          # image url -> Telegram file_id cached after the first successful upload


async def _reply_image(message: Message, url: str, cap: str, kb: InlineKeyboardMarkup) -> None:
    """Reply with a photo + caption (cached file_id first); text only if the image is unavailable."""
    for src in [s for s in (_IMG_FILE_IDS.get(url), url) if s]:
        try:
            sent = await message.reply_photo(photo=src, caption=cap, reply_markup=kb, parse_mode=ParseMode.HTML)
            if sent.photo and src == url:
                _IMG_FILE_IDS[url] = sent.photo[-1].file_id
            return
        except Exception as e:
            print(f"[diwali] photo failed ({src[:30]}...): {e}")
            if src == _IMG_FILE_IDS.get(url):
                _IMG_FILE_IDS.pop(url, None)
    await message.reply(cap, reply_markup=kb, parse_mode=ParseMode.HTML)


def _miniapp_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
        text="Open Diwali Mini App", url=DW_MINIAPP_LINK)]])


def _start_text(days: int, last_day: str) -> str:
    live = ["<code>/dwlogin</code> 7-night login event", "<code>/diwali</code>"]
    return (f"<b>Diwali event started</b>! <b>{days}</b> days — today is Day 1, "
            f"last day is <b>{last_day}</b> (UTC).\n"
            f"Players: " + ", ".join(live) + ".\n\n"
            f"Mini app: {DW_MINIAPP_LINK}")


_DW_USAGE = ("<b>Usage:</b>\n"
             "<code>/stdw on [days]</code> — start the login event (or resume if paused)\n"
             "<code>/stdw login on|off [days]</code>\n"
             "<code>/stcatchup on|off</code> — catch-up for missed nights (OFF by default)\n"
             "<code>/stdw fixlogin</code> — restore wiped login nights + forgive missed nights\n"
             "<code>/stdw setlogin &lt;user_id&gt; &lt;nights&gt;</code> — set one player's login night\n"
             "<code>/stdw pause</code> | <code>extend &lt;days&gt;</code> | <code>decrease [days]</code> | <code>status</code> | <code>off</code>\n"
             "<code>/dcard on|off DB-XXXXXX</code> | <code>/dcard list</code> — Diwali cards")


def _fix_login_all(db: dict) -> tuple:
    """Restore login progress that a reset wiped, and un-stick players whose missed nights would reset them.
    Returns (restored from snapshot, forgiven)."""
    eid = _state(db).get("event_id", 0)
    today = _today()
    yest = (datetime.now(timezone.utc) - timedelta(days=1)).strftime("%Y-%m-%d")
    total, restored, forgiven = len(LOGIN_EVENT), 0, 0
    for u in db.get("users", {}).values():
        if not isinstance(u, dict):
            continue
        cur = u.get("dw_login")
        cur_n = int(cur.get("streak", 0) or 0) if isinstance(cur, dict) and cur.get("event") == eid else 0
        prev = u.get("dw_login_prev")
        prev_n = int(prev.get("streak", 0) or 0) if isinstance(prev, dict) and time.time() - float(prev.get("at", 0)) < 14 * 86400 else 0
        if prev_n > cur_n:
            u["dw_login"] = {"event": eid, "streak": min(prev_n, total), "last": yest}
            u.pop("dw_login_prev", None)
            restored += 1
        elif 0 < cur_n < total and cur.get("last") and cur["last"] != today and _gap(cur["last"], today) > 1:
            cur["last"] = yest                    # would show "missed a night": forgive it
            forgiven += 1
    save_db()
    return restored, forgiven


@main_router.message(Command("stcatchup"))
async def stcatchup_cmd(message: Message, command: CommandObject):
    """/stcatchup on|off — owner + admins. Catch-up lets players claim missed nights; it never starts by itself."""
    if not _is_admin(message):
        return
    sw = ((command.args or "").split() or [""])[0].lower()
    db = load_db()
    if sw not in ("on", "off"):
        await message.reply(f"Usage: <code>/stcatchup on|off</code>\n"
                            f"Catch-up is now <b>{'ON' if catchup_enabled(db) else 'OFF'}</b>.", parse_mode=ParseMode.HTML)
        return
    _state(db)["catchup_on"] = (sw == "on")
    save_db()
    await message.reply(f"<b>Catch-up is now {sw.upper()}.</b>\n"
                        f"{_dw_status_text(db)}", parse_mode=ParseMode.HTML)


@main_router.message(Command("stdw"))
async def stdw_cmd(message: Message, command: CommandObject):
    """/stdw on [days] | login on|off [days] | pause | extend <days> | decrease [days] | status | off
    Owner + admins only."""
    if not _is_admin(message):
        return
    parts = (command.args or "").split()
    sub = parts[0].lower() if parts else "status"
    db = load_db()
    st = _state(db)

    if sub == "status":
        await message.reply(f"{_dw_status_text(db)}\n\nMini app: {DW_MINIAPP_LINK}",
                            reply_markup=_miniapp_kb(), parse_mode=ParseMode.HTML)
        return

    if sub == "pause":
        _ok, msg = _ev_pause(db)
        await message.reply(msg, parse_mode=ParseMode.HTML)
        return

    if sub in ("off", "stop", "end"):
        _ok, msg = _ev_stop(db)
        await message.reply(msg, parse_mode=ParseMode.HTML)
        return

    if sub == "extend":
        n = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0
        if n <= 0:
            await message.reply("Usage: <code>/stdw extend &lt;days&gt;</code>", parse_mode=ParseMode.HTML)
            return
        _ok, msg = _ev_extend(db, n)
        await message.reply(f"{msg}\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
        return

    if sub in ("decrease", "decr", "reduce", "shorten"):
        n = 1                                                      # /stdw decrease  ==  /stdw decrease 1
        if len(parts) > 1:
            if not parts[1].isdigit() or int(parts[1]) <= 0:
                await message.reply("Usage: <code>/stdw decrease [days]</code>  (e.g. <code>/stdw decrease 1</code>)",
                                    parse_mode=ParseMode.HTML)
                return
            n = int(parts[1])
        _ok, msg = _ev_decrease(db, n)
        await message.reply(f"{msg}\n{_dw_status_text(db)}" if _ok else msg, parse_mode=ParseMode.HTML)
        return

    # ---- login repair ----
    if sub == "fixlogin":
        n_rest, n_resc = _fix_login_all(db)
        await message.reply(f"<b>Login repaired.</b>\nRestored from snapshot: <b>{n_rest}</b>\n"
                            f"Un-stuck (missed nights forgiven): <b>{n_resc}</b>", parse_mode=ParseMode.HTML)
        return

    if sub == "setlogin":
        if len(parts) < 3 or not parts[1].isdigit() or not parts[2].isdigit() or not 0 <= int(parts[2]) <= len(LOGIN_EVENT):
            await message.reply(f"Usage: <code>/stdw setlogin &lt;user_id&gt; &lt;nights 0-{len(LOGIN_EVENT)}&gt;</code>",
                                parse_mode=ParseMode.HTML)
            return
        u = db.get("users", {}).get(parts[1])
        if not u:
            await message.reply("Unknown user.")
            return
        yest = (datetime.now(timezone.utc) - timedelta(days=1)).strftime("%Y-%m-%d")
        u["dw_login"] = {"event": st.get("event_id", 0), "streak": int(parts[2]), "last": yest}
        save_db()
        await message.reply(f"User <code>{parts[1]}</code> set to <b>{parts[2]}</b> night(s) — can claim tonight.",
                            parse_mode=ParseMode.HTML)
        return

    # ---- login: switch the login event on or off ----
    if sub == "login":
        sw = parts[1].lower() if len(parts) > 1 else ""
        if sw not in ("on", "off"):
            await message.reply("Usage: <code>/stdw login on|off [days]</code>", parse_mode=ParseMode.HTML)
            return
        name = "Login event"
        running = bool(event_active(db) or st.get("paused_at"))
        if sw == "off":
            if not running:
                await message.reply(f"The event isn't running, nothing to turn off.", parse_mode=ParseMode.HTML)
                return
            st["login_on"] = False
            save_db()
            await message.reply(f"<b>{name} is now OFF.</b> Players can't use it until you turn it on again.\n"
                                f"{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        if st.get("paused_at"):                                   # resume, then switch it on
            _ok, msg = _ev_resume(db)
            st["login_on"] = True
            save_db()
            await message.reply(f"{msg}\n<b>{name} is ON.</b>\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        if event_active(db):
            if st.get("login_on", True):
                await message.reply(f"{name} is already ON.\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
                return
            st["login_on"] = True
            save_db()
            await message.reply(f"<b>{name} is now ON.</b>\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        days = DEFAULT_EVENT_DAYS                                  # no event yet: start it
        if len(parts) > 2 and parts[2].isdigit():
            days = max(1, min(60, int(parts[2])))
        _day0, last_day = _ev_start(db, days)
        await message.reply(_start_text(days, last_day), reply_markup=_miniapp_kb(), parse_mode=ParseMode.HTML)
        return

    if sub == "on":
        if st.get("paused_at"):                                   # resume
            _ok, msg = _ev_resume(db)
            await message.reply(f"{msg}\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        if event_active(db):
            await message.reply(f"Already running.\n{_dw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        days = DEFAULT_EVENT_DAYS
        if len(parts) > 1 and parts[1].isdigit():
            days = max(1, min(60, int(parts[1])))
        _day0, last_day = _ev_start(db, days)
        await message.reply(_start_text(days, last_day),
                            reply_markup=_miniapp_kb(), parse_mode=ParseMode.HTML)
        return

    await message.reply(_DW_USAGE, parse_mode=ParseMode.HTML)


DW_MAIN_IMAGE = "https://i.ibb.co/4ntSc3np/35c544bf5612b07a8dda4ddbbdc2749d.jpg"


def _diwali_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[_btn(f"Open Diwali {DW_EMOJI} App", "danger", url=DW_MINIAPP_LINK)]])


def _diwali_text(db: dict, u: dict, uid) -> str:
    """The /diwali card. Bold only (the whole text is one bold block)."""
    st = _state(db)
    left, dn = event_seconds_left(db), event_day(db)
    if st.get("paused_at"):
        day, tl = (f"Day {dn[0]}/{dn[1]}" if dn else "Paused"), "Paused"
    elif left:
        day = f"Day {dn[0]}/{dn[1]}" if dn else "Running"
        tl = f"{_fmt_left(left)} left"
    else:
        day, tl = "Not running", "Event ended"
    login_on = login_enabled(db)
    lines = [
        f"「 {DW_EMOJI} DIWALI 」", "━━━━━━━━━━━━━━━━━",
        f"[ Login Event ] : {day if login_on else 'Switched off'}",
        f"[ Login Event Time left ] : {tl if login_on else '-'}",
    ]
    if login_on and left:
        lines.append(f"[ Nights claimed ] : {int(_login(db, u).get('streak', 0) or 0)}/{len(LOGIN_EVENT)}")
    return ("<b>" + "\n".join(lines) + "</b>\n\n"
            "<blockquote><b>Open the Mini App to claim your nightly login reward</b></blockquote>")


@main_router.message(Command("diwali"))
async def diwali_cmd(message: Message):
    """/diwali — for EVERYONE: event clock, nights claimed + the Mini App button."""
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    await _reply_image(message, DW_MAIN_IMAGE, _diwali_text(db, db["users"][user_id], uid_int), _diwali_kb())


@main_router.message(Command("dwcommands", "dwhelp"))
async def dwcommands_cmd(message: Message):
    """Command list for players (admin commands are not listed)."""
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        return
    lines = [
        f"「 {DW_EMOJI} DIWALI COMMANDS 」", "━━━━━━━━━━━━━━━━━",
        "/diwali - event clock and the Mini App button",
        "/dwlogin - 7-night login event (claim in the mini app)",
        "/dwhelp - this list",
    ]
    await message.reply("<b>" + "\n".join(lines) + "</b>", parse_mode=ParseMode.HTML)


def _dw_stats_text(db: dict) -> str:
    """Event-wide numbers for /dwstats. Bold only."""
    eid = _state(db).get("event_id", 0)
    total = len(LOGIN_EVENT)
    players = ads_total = ads_today = login_users = login_done = nights = 0
    reached = [0] * total
    today = _today()
    for u in (db.get("users", {}) or {}).values():
        if not isinstance(u, dict) or not any(u.get(k) for k in DW_USER_KEYS):
            continue
        players += 1
        ads_total += int(u.get("dw_ads_total", 0) or 0)
        d = u.get("dw_ads_day")
        if isinstance(d, dict) and d.get("date") == today:
            ads_today += int(d.get("n", 0) or 0)
        lg = u.get("dw_login")
        s = int(lg.get("streak", 0) or 0) if isinstance(lg, dict) and lg.get("event") == eid else 0
        if s > 0:
            login_users += 1
            nights += s
            for i in range(min(s, total)):
                reached[i] += 1
            if s >= total:
                login_done += 1
    left, dn = event_seconds_left(db), event_day(db)
    if _state(db).get("paused_at"):
        ev = "Paused"
    elif left:
        ev = (f"Day {dn[0]}/{dn[1]} · " if dn else "") + f"{_fmt_left(left)} left"
    else:
        ev = "Not running"
    pool = _diwali_pool(db)
    divines = sum(1 for c in pool.values() if format_rarity(c.get("rarity", "")) == DIVINE_RARITY)
    lines = [
        f"「 DIWALI STATS 」", "━━━━━━━━━━━━━━━━━",
        f"[ Event ] : {ev}",
        f"[ Login switch ] : {'ON' if _state(db).get('login_on', True) else 'OFF'}",
        f"[ Players ] : {players:,}",
        "",
        f"[ Total Ads Watched ] : {ads_total:,}",
        f"[ Ads Watched Today ] : {ads_today:,}",
        "",
        f"[ Login Event ] : {login_users:,} started · {login_done:,} completed all {total} nights · {nights:,} nights claimed",
    ]
    lines += [f"- Reached night {i + 1} : {n:,}" for i, n in enumerate(reached)]
    lines += ["", f"[ Diwali Cards ] : {len(pool)}  (Divine: {divines})"]
    return "<b>" + "\n".join(lines) + "</b>"


@main_router.message(Command("dwstats"))
async def dwstats_cmd(message: Message):
    """/dwstats — owner + admins: ads, login progress per night and card counts."""
    if not _is_admin(message):
        return
    await message.reply(_dw_stats_text(load_db()), parse_mode=ParseMode.HTML)


@main_router.message(Command("dcard"))
async def dcard_cmd(message: Message, command: CommandObject):
    """/dcard on <db-id> | off <db-id> | list — manage Diwali cards."""
    if not _is_admin(message):
        return
    parts = (command.args or "").split()
    sub = parts[0].lower() if parts else ""
    db = load_db()
    gc = db.get("global_cards", {})

    if sub == "list":
        cards = sorted(((cid, c) for cid, c in gc.items() if is_diwali_card(c)),
                       key=lambda kv: (str(kv[1].get("rarity", "")), str(kv[1].get("name", "")).lower()))
        if not cards:
            await message.reply(f"No Diwali cards yet.\nMark one with <code>/dcard on DB-XXXXXX</code>.",
                                parse_mode=ParseMode.HTML)
            return
        divines = sum(1 for _, c in cards if format_rarity(c.get("rarity", "")) == DIVINE_RARITY)
        chunks, cur = [], f"<b>「 DIWALI CARDS 」</b> — {len(cards)} total, {divines} Divine\n━━━━━━━━━━━━━━━━━\n"
        for cid, c in cards:
            line = f"<code>{_esc(str(cid))}</code> — {_esc(str(c.get('name', '?')))} [{_plain(format_rarity(c.get('rarity', '')))}]\n"
            if len(cur) + len(line) > 3800:
                chunks.append(cur)
                cur = ""
            cur += line
        chunks.append(cur)
        for chunk in chunks:
            await message.reply(chunk, parse_mode=ParseMode.HTML)
        return

    if sub in ("on", "off") and len(parts) >= 2:
        cid = parts[1].strip().upper()
        card = gc.get(cid)
        if not card:
            await message.reply(f"Card <code>{_esc(cid)}</code> not found.", parse_mode=ParseMode.HTML)
            return
        name = _esc(str(card.get("name", cid)))
        if sub == "on":
            if is_diwali_card(card):
                await message.reply(f"<b>{name}</b> is already a Diwali card.", parse_mode=ParseMode.HTML)
                return
            card["event"] = DW_EVENT_KEY
            save_db()
            owners = sum(1 for u in db.get("users", {}).values()
                         if (u.get("cards", {}).get(cid) or {}).get("amount", 0) > 0)
            note = (f"\n<b>{owners}</b> player(s) already own it and can no longer burn it."
                    if owners else "")
            await message.reply(
                f"<b>{name}</b> [{_plain(format_rarity(card.get('rarity', '')))}] is now a Diwali card.\n"
                f"<i>Tradable and giftable, but cannot be burned.</i>{note}",
                parse_mode=ParseMode.HTML)
        else:
            if card.get("event") != DW_EVENT_KEY and DW_EMOJI not in str(card.get("name", "")):
                await message.reply(f"<b>{name}</b> isn't a Diwali card.", parse_mode=ParseMode.HTML)
                return
            card.pop("event", None)
            save_db()
            extra = (f"\nThe name still contains the diya emoji, so it still counts as Diwali — "
                     f"rename it with /edit_card too." if DW_EMOJI in str(card.get("name", "")) else "")
            await message.reply(f"Diwali mark removed from <b>{name}</b>.{extra}", parse_mode=ParseMode.HTML)
        return

    await message.reply(
        "<b>Usage:</b>\n<code>/dcard on DB-XXXXXX</code> — mark as Diwali card\n"
        "<code>/dcard off DB-XXXXXX</code> — remove the mark\n<code>/dcard list</code> — all Diwali cards",
        parse_mode=ParseMode.HTML)


# ==========================================
# PLAYER DATA KEYS + CARD HELPERS
# ==========================================
# Every Diwali field stored on a player (all keys start with "dw_").
DW_USER_KEYS = ("dw_login", "dw_login_ads", "dw_ads_total", "dw_ads_day")


def award_seize_candies(db: dict, user: dict, global_card: dict) -> int:
    """No-op hook, kept so the call in seize_cmd keeps working."""
    return 0


def _grant_card(user: dict, cid: str, card: dict) -> None:
    cards = user.setdefault("cards", {})
    entry = cards.setdefault(cid, {
        "name": card.get("name", "Card"),
        "rarity": card.get("rarity", "Basic 🃏"),
        "amount": 0,
    })
    entry["amount"] = entry.get("amount", 0) + 1


def _locked_series(db: dict) -> set:
    """Anime series locked with /lock_drop (settings['locked_animes']), lower-cased."""
    return {str(a).lower().strip() for a in db.get("settings", {}).get("locked_animes", []) or []}


def _pick_card(db: dict, rarities, diwali: bool):
    """Random global card in one of `rarities`.
      diwali=True  -> ONLY cards marked Diwali (is_diwali_card). The series lock is ignored,
                         because Diwali series are normally kept locked so they never drop.
      diwali=False -> ONLY non-Diwali cards from UNLOCKED series (not in /lock_drop)."""
    if isinstance(rarities, str):
        rarities = (rarities,)
    locked = set() if diwali else _locked_series(db)
    pool = {
        cid: c for cid, c in db.get("global_cards", {}).items()
        if format_rarity(c.get("rarity", "")) in rarities
        and is_diwali_card(c) == diwali
        and str(c.get("anime", "")).lower().strip() not in locked
    }
    if not pool:
        return None, None
    cid = random.choice(list(pool))
    return cid, pool[cid]


# ==========================================
# THE 7-NIGHT LOGIN EVENT (ads -> shards / cards): /dwlogin shows it, diwali.html claims it
# ==========================================
def _gap(a: str, b: str) -> int:
    f = "%Y-%m-%d"
    return (datetime.strptime(b, f) - datetime.strptime(a, f)).days


def _login(db: dict, user: dict) -> dict:
    """Per-event login record: {'event': id, 'streak': nights claimed in a row, 'last': date}."""
    eid = _state(db).get("event_id", 0)
    h = user.get("dw_login")
    if not isinstance(h, dict) or h.get("event") != eid:
        _snapshot_login(user, h)                 # keep the old progress so /stdw fixlogin can restore it
        h = {"event": eid, "streak": 0, "last": None}
        user["dw_login"] = h
    return h


def _snapshot_login(user: dict, h) -> None:
    """Remember a login record that is about to be reset (event id changed / streak broken)."""
    if isinstance(h, dict) and int(h.get("streak", 0) or 0) > 0:
        prev = user.get("dw_login_prev")
        if not isinstance(prev, dict) or int(prev.get("streak", 0) or 0) <= int(h.get("streak", 0)):
            user["dw_login_prev"] = {"streak": int(h["streak"]), "last": h.get("last"), "at": time.time()}


def _catchup_open(db: dict, user: dict) -> bool:
    """Catch-up opens for a player when they can no longer finish all nights at one night per day:
    nights still to claim > event days still available to them. It closes again by itself once they
    are back on pace, so they only catch up as much as they need. Nights stay sequential."""
    if not catchup_enabled(db):
        return False
    dn = event_day(db) if event_active(db) else None
    if not dn:
        return False
    day, total = dn
    h = _login(db, user)
    nights_left = len(LOGIN_EVENT) - int(h.get("streak", 0) or 0)
    if nights_left <= 0:
        return False
    days_left = total - day + (0 if h.get("last") == _today() else 1)   # today only counts if not claimed yet
    return nights_left > days_left


def _afford(streak: int, seen: int) -> tuple:
    """(how many nights the `seen` ads pay for, ads those nights cost), counting from night streak+1."""
    k = cost = 0
    for d in LOGIN_EVENT[streak:]:
        if cost + d["ads"] > seen:
            break
        cost += d["ads"]
        k += 1
    return k, cost


def _login_view(db: dict, user: dict):
    """(nights claimed in the current run, can claim tonight?, streak just broke?, catch-up?)
    catch-up = exactly ONE night was missed: tonight completes the missed night AND tonight together."""
    h = _login(db, user)
    today, last, streak = _today(), h.get("last"), int(h.get("streak", 0))
    if streak >= len(LOGIN_EVENT):
        return streak, False, False, False      # finished all nights: nothing more to claim or watch this event
    if _catchup_open(db, user):
        return streak, True, False, False       # catch-up window: keep progress, claim missed nights together
    broken = catchup = False
    if last and last != today:
        if catchup_enabled(db) and streak > 0 and _gap(last, today) == 2 and streak + 1 < len(LOGIN_EVENT):
            catchup = True                      # missed one night: claim it together with tonight
        # missed more than one night: progress is kept (no reset), claim tonight's night as normal
    return streak, last != today, broken, catchup


def login_completed(db: dict, user: dict) -> bool:
    """True once the player has claimed all nights of the login event (no more ads / claims)."""
    return int(_login(db, user).get("streak", 0)) >= len(LOGIN_EVENT)


def _nights_due(streak: int, catchup: bool, bulk: bool = False) -> tuple:
    """The LOGIN_EVENT nights that tonight's claim pays out (2 when catching up a missed night;
    every remaining night in the final catch-up window)."""
    if bulk:
        return LOGIN_EVENT[streak:streak + 1]     # catch-up is sequential: one night at a time, in order
    return LOGIN_EVENT[streak:streak + (2 if catchup else 1)]


def _ads_needed(streak: int, catchup: bool, bulk: bool = False) -> int:
    nights = _nights_due(streak, catchup, bulk)
    return sum(d["ads"] for d in nights) if nights else LOGIN_EVENT[-1]["ads"]


def _ads_today(user: dict) -> int:
    a = user.get("dw_login_ads")
    return int(a.get("n", 0)) if isinstance(a, dict) and a.get("date") == _today() else 0


def record_ad(db: dict, user: dict, uid=None) -> int:
    """Count one confirmed rewarded ad toward tonight's login reward. Called from the Adsgram
    reward postback only (never trust the client). Returns the ads counted tonight."""
    user["dw_ads_total"] = int(user.get("dw_ads_total", 0) or 0) + 1      # lifetime confirmed ads (/dwstats)
    d = user.get("dw_ads_day")
    if not isinstance(d, dict) or d.get("date") != _today():
        d = {"date": _today(), "n": 0}
    d["n"] += 1
    user["dw_ads_day"] = d
    save_db()
    if not login_enabled(db, uid):
        return 0
    streak, can, _broken, catchup = _login_view(db, user)
    if not can:
        return _ads_today(user)
    n = min(_ads_needed(streak, catchup, _catchup_open(db, user)), _ads_today(user) + 1)
    user["dw_login_ads"] = {"date": _today(), "n": n}
    save_db()
    return n


def _reward_text(day: dict) -> str:
    parts = []
    if day.get("shards"):
        parts.append(f"{day['shards']:,} Nexus Shards 💠")
    if day.get("card"):
        parts.append(f"1 random {day['card']} card")
    if day.get("dwcard"):
        parts.append(f"1 random Diwali {DW_EMOJI} card")
    return " + ".join(parts)


def claim_login(db: dict, user: dict, uid=None):
    """Claim tonight's reward once enough ads were counted. If exactly one night was missed,
    the missed night and tonight are paid together (ads of both nights are needed).
    Returns (ok, {'day','nights','catchup','shards','cards':[{'name','rarity'}]} | {'error'})."""
    if not event_active(db):
        return False, {"error": "The Diwali event isn't running right now."}
    if not login_enabled(db, uid):
        return False, {"error": "The login event is switched off right now."}
    if login_completed(db, user):
        return False, {"error": "You already completed all 7 nights. Nothing more to claim!"}
    streak, can, _broken, catchup = _login_view(db, user)
    if not can:
        return False, {"error": "Already claimed tonight — come back after 00:00 UTC."}
    seen = _ads_today(user)
    bulk = _catchup_open(db, user)
    if bulk:
        nights = LOGIN_EVENT[streak:streak + 1]  # sequential: ONE night per claim (night 1, then 2, then 3...)
        used = nights[0]["ads"]
        if seen < used:
            return False, {"error": f"Watch {used} ad(s) first ({seen}/{used})."}
        catchup = False
    else:
        nights = _nights_due(streak, catchup)
        if not nights:
            return False, {"error": "Nothing to claim right now."}
        used = need = _ads_needed(streak, catchup)
        if seen < need:
            return False, {"error": f"Watch {need} ad(s) first ({seen}/{need})."}

    # Pick the cards BEFORE granting anything, so an empty pool never costs the player.
    picks = []
    for day in nights:
        if day.get("card"):
            picks.append(_pick_card(db, day["card"], diwali=False))
        if day.get("dwcard"):
            picks.append(_pick_card(db, day["dwcard"], diwali=True))
    if any(c is None for _cid, c in picks):
        return False, {"error": "That reward is out of stock right now. Try again later — your ads are kept."}

    shards = sum(int(d.get("shards", 0)) for d in nights)
    if shards:
        _add_shards(user, shards)
    cards = []
    for cid, c in picks:
        _grant_card(user, cid, c)
        cards.append({"name": str(c.get("name", "Card")), "rarity": format_rarity(c.get("rarity", ""))})
    h = _login(db, user)
    if _broken:
        _snapshot_login(user, h)                 # streak was reset by the missed-night rule: keep the old one
    h["streak"], h["last"] = streak + len(nights), _today()
    user["dw_login_ads"] = {"date": _today(), "n": max(0, seen - used) if bulk else 0}
    save_db()
    return True, {"day": streak + len(nights), "nights": [streak + 1 + i for i in range(len(nights))],
                  "catchup": bool(catchup), "shards": shards, "cards": cards}


def _login_text(db: dict, user: dict) -> str:
    """The /dwlogin card. Bold only (the whole text is one bold block)."""
    streak, can, broken, catchup = _login_view(db, user)
    bulk = can and _catchup_open(db, user)
    total = len(LOGIN_EVENT)
    rows = []
    for i, d in enumerate(LOGIN_EVENT):
        mark = "Completed" if i < streak else "Incomplete"
        rows.append(f" - [{mark}] Night {i + 1} —  {_reward_text(d)}")
    if streak >= total:
        cur = f"[Current]: Night {total} (complete)"
    elif not can:
        cur = f"[Current]: Night {streak} (complete)"
    elif bulk:
        cur = f"[Current]: Night {streak + 1} (catch-up, one night at a time)"
    elif catchup:
        cur = f"[Current]: Nights {streak + 1} + {streak + 2} (incomplete)"
    else:
        cur = f"[Current]: Night {streak + 1} (incomplete)"
    lines = [f"「 {DW_EMOJI} 7-NIGHT LOGIN EVENT 」", "━━━━━━━━━━━━━━━━━"] + rows + ["", cur]
    if streak < total and can:
        need = _ads_needed(streak, catchup, bulk)
        lines.append(f"[Ads]: {min(_ads_today(user), need)}/{need} watched")
        if bulk:
            lines.append("The event is ending: claim the missed nights one by one, in order.")
    if broken:
        lines += ["", "You missed a night, so the event restarted at night 1."]
    return "<b>" + "\n".join(lines) + "</b>"


DW_LOGIN_IMAGE = "https://i.ibb.co/4ntSc3np/35c544bf5612b07a8dda4ddbbdc2749d.jpg"


@main_router.message(Command("dwlogin"))
async def dwlogin_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    if not _ev_on(db, uid_int):
        await message.reply(f"{DW_EMOJI} The Diwali event isn't running right now.", parse_mode=ParseMode.HTML)
        return
    if not login_enabled(db, uid_int):
        await message.reply("🌙 <b>The login event is switched off right now.</b> Check back later.",
                            parse_mode=ParseMode.HTML)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[[_btn(f"Diwali {DW_EMOJI}", "danger", url=DW_MINIAPP_LINK)]])
    await _reply_image(message, DW_LOGIN_IMAGE, _login_text(db, db["users"][user_id]), kb)


# ==========================================
# EVENT CONTROL HELPERS (used by /stdw)
# ==========================================
def _ev_start(db: dict, days: int):
    st, now = _state(db), time.time()
    day0 = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
    st["active"] = True
    st["event_id"] = int(now)                 # new id => everyone's login progress starts fresh
    st["start_date"] = day0.strftime("%Y-%m-%d")
    st["days"] = days
    st["login_on"] = True
    st["catchup_on"] = False                  # catch-up starts OFF; admin turns it on with /stcatchup on
    st["paused_total"] = 0
    st["ends_at"] = (day0 + timedelta(days=days)).timestamp()   # end of the last UTC day
    st.pop("paused_at", None)
    save_db()
    return day0, (day0 + timedelta(days=days - 1)).strftime("%Y-%m-%d")


def _ev_pause(db: dict):
    st = _state(db)
    if not st.get("active"):
        return False, f"The event isn't running, nothing to pause."
    st["active"] = False
    st["paused_at"] = time.time()
    save_db()
    return True, ("<b>Event paused.</b> The login event is frozen and the remaining time is kept.\n"
                  "Use <code>/stdw on</code> to resume.")


def _ev_resume(db: dict):
    st, now = _state(db), time.time()
    if not st.get("paused_at"):
        return False, "The event isn't paused."
    dur = now - st.pop("paused_at")
    st["ends_at"] = st.get("ends_at", now) + dur
    st["paused_total"] = st.get("paused_total", 0) + dur
    st["active"] = True
    save_db()
    return True, "<b>Event resumed.</b>"


def _ev_stop(db: dict):
    st = _state(db)
    st["active"] = False
    st.pop("paused_at", None)
    save_db()
    return True, "Diwali event ended."


def _ev_extend(db: dict, n: int):
    st = _state(db)
    if not (st.get("paused_at") or event_active(db)):
        return False, "The event is over — start a new one with /stdw on."
    n = max(1, min(30, int(n)))
    st["ends_at"] = st.get("ends_at", time.time()) + n * 86400
    st["days"] = int(st.get("days", 0) or 0) + n
    save_db()
    return True, f"Event extended by <b>{n}</b> day(s)."


def _ev_decrease(db: dict, n: int):
    """Remove n whole UTC days from the end of the running (or paused) event."""
    st = _state(db)
    paused = st.get("paused_at")
    if not (paused or event_active(db)):
        return False, "The event isn't running — nothing to shorten."
    n = max(1, min(30, int(n)))
    total = int(st.get("days", 0) or 0)
    ref = paused or time.time()                                  # paused: time is frozen at the pause moment
    new_end = st.get("ends_at", ref) - n * 86400
    if total - n < 1 or new_end <= ref:
        return False, ("Can't remove that many days — the event would end right away.\n"
                       "Use <code>/stdw off</code> to end it now.")
    st["ends_at"] = new_end
    st["days"] = total - n
    save_db()
    return True, f"Event shortened by <b>{n}</b> day(s)."


# ==========================================
# WEB API for diwali.html (FastAPI router, same style as /api/deck and /api/store)
# ==========================================
def _verify_init_data(init_data: str):
    """Validate Telegram WebApp initData. Returns the Telegram user dict, or None."""
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        got = pairs.pop("hash", "")
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", bot.token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got) or time.time() - int(pairs.get("auth_date", 0)) > 86400:
            return None
        return json.loads(pairs["user"])
    except Exception:
        return None


def _web_view(db: dict, user: dict, uid=None) -> dict:
    """Everything diwali.html needs to draw itself (login event only)."""
    lon = login_enabled(db, uid)
    streak, can, broken, catchup = _login_view(db, user)
    bulk = bool(can and lon and _catchup_open(db, user))
    need = _ads_needed(streak, catchup, bulk)
    claimable = min(1, _afford(streak, _ads_today(user))[0]) if bulk else 0
    dn, active = event_day(db), event_active(db)
    left = event_seconds_left(db)
    return {
        "event": {"active": active, "day": dn[0] if dn else 0, "total": dn[1] if dn else 0,
                  "seconds_left": left},
        "shards": int(user.get("nexus_shards", 0) or 0),
        "features": {"login": lon},
        "login": {"streak": streak, "completed": streak >= len(LOGIN_EVENT), "can_claim": bool(can and lon), "broken": broken, "catchup": bool(catchup),
                  "ads_needed": need, "bulk": bulk, "claimable": claimable,
                  "ads_watched": min(_ads_today(user), need) if (can and lon) else 0},
    }


def get_router(prefix: str = "/diwali"):
    """FastAPI router for diwali.html. Mount it once at startup:
           app.include_router(diwali.get_router(), prefix="/api")
       -> POST /api/diwali/state | /api/diwali/login
       Body: {"user_id": 123, "init_data": "<Telegram.WebApp.initData>"}
       Errors are HTTPException(detail=...), like the other mini-app endpoints."""
    from fastapi import APIRouter, HTTPException
    from pydantic import BaseModel

    class Req(BaseModel):
        user_id: int
        init_data: str = ""

    router = APIRouter(prefix=prefix, tags=["diwali"])

    def ctx(req: Req):
        if DW_REQUIRE_INITDATA:
            tg = _verify_init_data(req.init_data)
            if not tg or int(tg.get("id", 0)) != req.user_id:
                raise HTTPException(401, "Open this page from the bot.")
        if is_ghost_banned(req.user_id) or is_shadow_banned(req.user_id):
            raise HTTPException(403, "Not available.")
        db = load_db()
        user = db.get("users", {}).get(str(req.user_id))
        if not user:
            raise HTTPException(404, "Start the bot first, then open this page again.")
        return db, user

    @router.get("/ping")
    async def ping():
        """Open <your-worker>/api/diwali/ping in a browser: {"ok": true} means the router is mounted."""
        return {"ok": True, "event_active": event_active(load_db())}

    @router.get("/ads/reward")
    async def ad_reward(userid: int = 0, secret: str = "", key: str = ""):
        """Adsgram reward postback: counts one confirmed ad toward tonight's login reward."""
        if DW_AD_SECRET and not hmac.compare_digest(secret or key, DW_AD_SECRET):
            raise HTTPException(403, "Bad secret.")
        db = load_db()
        user = db.get("users", {}).get(str(userid))
        if not user:
            raise HTTPException(404, "Unknown user.")
        return {"ok": True, "watched": record_ad(db, user, userid)}

    @router.post("/state")
    async def state(req: Req):
        db, user = ctx(req)
        view = _web_view(db, user, req.user_id)
        save_db()                      # persists a freshly created login record
        return {"ok": True, "view": view}

    @router.post("/login")
    async def login(req: Req):
        db, user = ctx(req)
        ok, info = claim_login(db, user, req.user_id)
        if not ok:
            raise HTTPException(400, info["error"])
        return {"ok": True, **info, "view": _web_view(db, user, req.user_id)}

    return router


# ==========================================
# OLD NAMES (so deck.py / handlers.py keep working until you switch their imports to the diwali_* / dw_* names)
# Delete this block once those files import the new names.
# ==========================================
is_halloween_card = is_diwali_card
halloween_flex_line = diwali_flex_line
maybe_halloween_drop = maybe_diwali_drop
hw_locked = dw_locked
hw_lock_text = dw_lock_text

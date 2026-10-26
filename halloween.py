"""
halloween.py — Halloween 🎃 event for Anime Nexus
=================================================
Imports ONLY from config (never from deck.py / handlers.py) so both of
those files can import this one without a circular import.

What it adds
  • Candies 🍬               — event currency. Earned from the daily quests (/haunt)
                               and /treat (candies) + /trick (shards).
  • Halloween edition cards  — any global card with "🎃" in its name, or
                               event == "halloween". Flex / inline captions get the
                               "This is a halloween (🎃) edition card !" line.
  • Login event              — ONE 7-night event, claimed in halloween.html by watching ads
                               (Adsgram): night 1 = 1 ad -> 1,000 shards ... night 7 = 3 ads ->
                               random Halloween card + 3,000 shards (see LOGIN_EVENT).
                               Missed exactly ONE night? You can catch up: the next time you log in you
                               complete the missed night AND tonight together (ads of both nights).
                               /hwlogin shows the calendar and tonight's ad progress.
  • /haunt                   — 5 daily quests (auto-assigned to everyone at 00:00 UTC) + haunt-day progress (candy income for /hwstore).
  • /treat                   — COMMUNITY command (group chats). Reply to a player's message with /treat to
                               give them a random bag of 1-2 candies 🍬🍭🍫🍪🍩🍰 (2 is rare, see
                               TREAT_DOUBLE_CHANCE). Each giver can use it 3 times per UTC day. Limits: no self-treats, no bots, a receiver can get 3 treats per UTC
                               day, and the same person can't be treated twice by one giver within 24h.
                               🍬 is the main currency; 🍭🍫🍪🍩🍰 convert to 🍬 at /candies (candies -> shards only in /hwstore).
  • /trick                   — COMMUNITY command (group chats), twice a day (12h interval): Pumpkin Patch game, pick 1 of 5 pumpkins;
                               2 ghosts (nothing), 2 Nexus Shards 💠, 1 rare candy 1-3 🍬. /treat and /trick have separate limits. Nothing is ever taken away.
                               (/trickortreat just explains the two commands.)
  • /hwstore, /candies       — spend candies. The Mystery Halloween Card is the last item.
  • /hwcommands (/hwhelp)    — command list (players; owner + admins also see the admin commands)
  • /halloween               — for EVERYONE: total candies + Mini App button (admin controls are /sthw)
  • Web API                  — get_router() returns a FastAPI router used by halloween.html:
                               POST /halloween/state | /halloween/login | /halloween/buy
                               mount once:  app.include_router(halloween.get_router(), prefix="/api")
  • /halloween_lbd (/hwlbd)  — leaderboard with the event image; tabs: Top Candies / Treats Given /
                               Treats Received / Haunt Days / Login Nights.
  • Admin controls  /sthw    (owner + admins only; /halloween is the player command)
        /sthw on [days]          start everything (login + haunt) — or resume if paused
        /sthw login on|off [d]   turn the 7-night login event on / off on its own
        /sthw haunt on|off [d]   turn /haunt quests + the Quests tab on / off on its own
                                      ("on" with no event running starts the event with ONLY that part)
        /sthw extend <days>      add days to the running event
        /sthw decrease [days]    remove days from the running event (default 1)
        /sthw pause              freeze the event; remaining time is kept
        /sthw status             state, day number, login/haunt switches, card counts
        /sthw off                end the event now
        /hcard on <db-id>             mark an existing card as a Halloween card
        /hcard off <db-id>            remove the mark
        /hcard list                   list all Halloween cards
        /hwtest <userid> on|off       test mode: that player can use EVERY Halloween command anytime
                                      (event off, parts off, private chat). "off" resets their data.
        /hwtest list                  show current test users
        /hwtest clear_all             end test mode for everyone + reset all their Halloween data
                                      (also works as a reply to the player instead of <userid>)
  • Halloween cards are locked: they can't be sold in the Offline Store, gifted,
    traded or burned (see hw_locked()).
  • Marking: upload the card as usual (/add_card), then /hcard on <db-id>.

Hooks (small edits in deck.py / handlers.py):
  halloween_flex_line(global_card)        -> caption suffix
  maybe_halloween_drop(db, pool, rarity)  -> kept as a no-op: drops are NOT boosted any more
  award_seize_candies(db, user, card)     -> kept as a no-op (returns 0): /seize gives no candies
  hw_locked(db, card_id) / hw_lock_text(action) -> block gift/trade/burn/sell
  quest_progress(user_id, key, amount=1, db=None)  -> bump a daily quest
      keys: shards, versus_play, versus_win, guess, scramble, seize, mines,
            airdrop, roll, throw, burn, trade, store_buy
  importing this module registers the commands on main_router.
"""
import asyncio
import hashlib
import hmac
import json
import random
import time
from urllib.parse import parse_qsl
from datetime import datetime, timedelta, timezone
from html import escape as _esc

from aiogram import F
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject
from aiogram.types import CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Message, WebAppInfo

from config import (
    bot, main_router, ADMIN_IDS, SUPREME_OWNER_ID, ensure_user, load_db, save_db,
    format_rarity, is_ghost_banned, is_shadow_banned,
)

# ==========================================
# SETTINGS
# ==========================================
HW_EMOJI = "🎃"
HW_EVENT_KEY = "halloween"
DEFAULT_EVENT_DAYS = 9          # event length in UTC days (day 1 = the day it is started)

CANDY = "🍬"

# Candy types: (emoji, name, value in 🍬, drop weight).
#   🍬 Candy is the MAIN currency: the store only spends 🍬. A 🍬 piece is worth exactly 1 🍬 and goes straight to the balance.
#   🍭🍫🍪🍩🍰 are collectible items kept in the player's candy bag; they can be converted to 🍬 at /candies.
#   Turning 🍬 into Nexus Shards is only possible in the store (/hwstore exchange item).
# Average piece ~ 6 🍬 once converted, so a /treat bag (1-2 pieces) is worth ~7 🍬 (quests add ~300/day).
CANDY_TYPES = [
    ("🍬", "Candy",     1, 40),
    ("🍭", "Lollipop",  6, 25),
    ("🍫", "Chocolate", 8, 16),
    ("🍪", "Cookie",    10, 10),
    ("🍩", "Donut",     20, 6),
    ("🍰", "Cake",      30, 3),
]

# The ONE login event: 7 nights, each claimed in halloween.html after watching `ads` rewarded ads.
#   "shards": Nexus Shards   "card": random NON-Halloween card of that rarity
#   "hwcard": random Halloween card (Basic/Elite only, so the store's Divine stays special)
LOGIN_EVENT = (
    {"ads": 1, "shards": 1000},
    {"ads": 1, "card": "Basic 🃏"},
    {"ads": 2, "shards": 1500},
    {"ads": 2, "card": "Elite ⚓"},
    {"ads": 2, "shards": 2000},
    {"ads": 3, "card": "Divine ❄️"},
    {"ads": 3, "shards": 3000, "hwcard": ("Basic 🃏", "Elite ⚓")},
)
# Adsgram reward postback (create a rewarded block in the Adsgram dashboard and set its reward URL to):
#   https://<your-worker>/api/halloween/ads/reward?userid=[userId]&secret=<HW_AD_SECRET>   (&key=... also works)
HW_AD_SECRET = "gUz6e7bs0-TrdtHVtx7EAM63mMpfvQsc"   # same secret as ADSGRAM_REWARD_SECRET in deck.py

# /treat (reply to a player, 3 uses per giver per day) and /trick (once per UTC day) — community (group chat) commands
TOT_COMMUNITY_ONLY = True        # False = also allow them in private chats
TREAT_WINDOW_HOURS = 12          # /treat limits reset every N hours (12h windows from 00:00 UTC)
TREAT_DAILY_USES = 3             # /treat: uses per giver per window
TREAT_RECEIVE_DAILY_MAX = 3      # /treat: max treats one player can RECEIVE per window
TREAT_SAME_USER_HOURS = 12       # /treat: a giver can't treat the same person again within N hours
TREAT_DOUBLE_CHANCE = 0.15       # /treat: chance (0-1) that the bag holds 2 candies instead of 1 (each rolled separately)
TRICK_SHARD_RANGE = (200, 500)   # /trick: shards when you win, rounded to steps of 50
TRICK_SPOOKS = 2                 # /trick game board: pumpkins that hide a ghost (nothing)
TRICK_SHARD_PUMPKINS = 2         # ...pumpkins that hide Nexus Shards
TRICK_CANDY_PUMPKINS = 1         # ...pumpkins that hide the rare candy 🍬
TRICK_CANDY_RANGE = (1, 3)       # rare candy: 1-3 🍬 only
TRICK_DAILY_USES = 2             # /trick: games per UTC day
TRICK_INTERVAL_HOURS = 12        # /trick: wait between two games
COLLECTOR_BONUS = 100            # one-time bonus candies for collecting every candy type at least once

# Mini App (halloween.html)
HW_WEBAPP_URL = ""               # https URL where halloween.html is hosted (optional)
HW_MINIAPP_LINK = "https://t.me/Animenx_bot/Halloween"   # direct Mini App link (works in groups and private chats)
HW_REQUIRE_INITDATA = True       # verify Telegram initData on every web API call

# Pricing is tuned to the quest income: a full-clear day pays ~300 candies (5 quests ~210 + 100 bonus).
#   Divine 1,800 = 6 full days, Mystery Halloween 2,100 = 7 full days (max 1 per player).
# Store: key -> (label, price in candies, per-user limit, kind, value)
#   kind: "shards" | "card" (value = rarity or None) | "hwcard" (value = rarity tuple)
STORE_ITEMS = {
    "sh500":  ("💠 500 Nexus Shards (exchange)",      100,  5, "shards", 500),                 # candies -> shards
    "elite":  ("⚓ Random Elite Card",                 450,  3, "card",   "Elite ⚓"),                  # unlocked-series, non-Halloween only
    "divine": ("❄️ Random Divine Card",               1800,  1, "card",   "Divine ❄️"),          # non-Halloween; ~6 full quest days
    "hwcard": ("🎁 Mystery Halloween Card (🎃)",      2100,  1, "hwcard", ("Basic 🃏", "Elite ⚓")),   # ~7 full quest days; max 1; always last
}
# Items that stay locked until the player has enough haunt days (see /haunt).
STORE_REQ_HAUNT_DAYS = {}

TREAT_LINES = [
    "A full-size candy bar, straight from the bowl.",
    "Someone left the candy bowl unattended.",
    "A sweet, just for you.",
    "Fresh from the trick-or-treat route.",
]
TRICK_LINES = [
    "The pumpkin patch is quiet... too quiet.",
    "Something rustles between the vines.",
    "The moon is out. Choose carefully.",
]
TRICK_WIN_LINES = [
    "The pumpkin glows and shards spill out!",
    "A bat swoops past and drops something shiny.",
    "Lucky pick. The patch was feeling generous.",
]
TRICK_LOSE_LINES = [
    "A ghost jumps out! Nothing this time.",
    "Empty. The pumpkin just laughs at you.",
    "Boo! The ghost keeps the shards.",
]


# ==========================================
# HELPERS (importable from deck.py / handlers.py)
# ==========================================
def is_halloween_card(global_card: dict) -> bool:
    if not isinstance(global_card, dict):
        return False
    return global_card.get("event") == HW_EVENT_KEY or HW_EMOJI in str(global_card.get("name", ""))


def halloween_flex_line(global_card: dict) -> str:
    """Caption suffix for flex/inline captions ('' for normal cards)."""
    if is_halloween_card(global_card):
        return f"\n\n<b><i>This is a halloween ({HW_EMOJI}) edition card !</i></b>"
    return ""


def _state(db: dict) -> dict:
    return db.setdefault("settings", {}).setdefault(HW_EVENT_KEY, {})


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


def hw_locked(db: dict, card_id) -> bool:
    """True if this card is a Halloween card (can't be sold offline, gifted, traded or burned)."""
    return is_halloween_card(db.get("global_cards", {}).get(card_id))


def hw_lock_text(action: str) -> str:
    return f"{HW_EMOJI} <b>Halloween cards cannot be {action}.</b>"


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


def haunt_day(db: dict):
    """(day, total) for the HAUNT part. It counts from the day haunt was switched on, so a haunt
    turned on a day after login starts at Day 1 (and ends together with the event)."""
    dn = event_day(db)
    if not dn:
        return None
    off = int(_state(db).get("haunt_offset", 0) or 0)
    total = max(1, dn[1] - off)
    return max(1, min(dn[0] - off, total)), total


def _mark_haunt_start(db: dict) -> None:
    """Remember which event day haunt was switched on (0 = from the first day)."""
    dn = event_day(db)
    _state(db)["haunt_offset"] = (dn[0] - 1) if dn else 0


def _halloween_pool(db: dict, rarity: str | None = None) -> dict:
    out = {}
    for cid, c in db.get("global_cards", {}).items():
        if not is_halloween_card(c):
            continue
        if rarity and format_rarity(c.get("rarity", "")) != rarity:
            continue
        out[cid] = c
    return out


def maybe_halloween_drop(db: dict, pool: dict, target_rarity: str) -> dict:
    """Kept so the hook in trigger_drop keeps working. Drops are NOT boosted any more:
    the pool is returned unchanged."""
    return pool


def _fmt_left(sec: int) -> str:
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m = r // 60
    return f"{d}d {h}h {m}m" if d else f"{h}h {m}m"


def is_test_user(db: dict, uid) -> bool:
    """True if /hwtest put this player in test mode (can use every Halloween command anytime)."""
    if uid is None:
        return False
    u = db.get("users", {}).get(str(uid))
    return bool(isinstance(u, dict) and u.get("hw_test"))


def _tester_clock(user: dict):
    """(day, total, seconds_left) of a /hwtest tester's own event run, which starts the moment
    /hwtest <id> on is used. Only used while no real event is running."""
    total = DEFAULT_EVENT_DAYS
    el = max(0, time.time() - float(user.get("hw_test_start") or time.time()))
    return min(int(el // 86400) + 1, total), total, max(0, int(total * 86400 - el))


def _ev_on(db: dict, uid=None) -> bool:
    """Event running, or this player is a /hwtest tester (testers ignore the event/part switches)."""
    return event_active(db) or is_test_user(db, uid)


def _add_shards(user: dict, n: int) -> None:
    """Give Nexus Shards; for testers the amount is logged so /hwtest off can take it back."""
    user["nexus_shards"] = user.get("nexus_shards", 0) + int(n)
    if user.get("hw_test"):
        g = user.setdefault("hw_test_grants", {})
        g["shards"] = int(g.get("shards", 0)) + int(n)


def _feature_on(db: dict, key: str, uid=None) -> bool:
    """Event running AND the part switched on. The owner can always use both parts while the event runs.
    /hwtest testers can use both parts at any time."""
    if is_test_user(db, uid):
        return True
    if not event_active(db):
        return False
    if uid is not None and str(uid) == str(SUPREME_OWNER_ID):
        return True
    return bool(_state(db).get(key, True))


def login_enabled(db: dict, uid=None) -> bool:
    """Login part on (/sthw login on|off); the owner bypasses the switch."""
    return _feature_on(db, "login_on", uid)


def haunt_enabled(db: dict, uid=None) -> bool:
    """Haunt part (quests) on (/sthw haunt on|off); the owner bypasses the switch."""
    return _feature_on(db, "haunt_on", uid)


def tot_enabled(db: dict, uid=None) -> bool:
    """/treat + /trick are INDEPENDENT of the event, haunt and login switches: they work for everyone
    unless an admin turns them off with /sthw tot off. /hwtest testers can always use them."""
    if is_test_user(db, uid):
        return True
    return bool(_state(db).get("tot_on", True))


def _is_admin(message: Message) -> bool:
    """The owner and the admins can use the admin commands."""
    uid = message.from_user.id
    return uid == SUPREME_OWNER_ID or uid in ADMIN_IDS


# ==========================================
# ADMIN COMMANDS
# ==========================================
def _hw_status_text(db: dict) -> str:
    st = _state(db)
    left = event_seconds_left(db)
    dn = event_day(db)
    if st.get("paused_at"):
        rem = max(0, int(st.get("ends_at", 0) - st["paused_at"]))
        state = f"⏸ PAUSED — {_fmt_left(rem)} left when resumed"
    elif left:
        state = f"▶️ ON — {_fmt_left(left)} left" + (f" (Day {dn[0]}/{dn[1]})" if dn else "")
    else:
        state = "⏹ OFF"
    pool = _halloween_pool(db)
    divines = sum(1 for c in pool.values() if format_rarity(c.get("rarity", "")) == HAUNT_REWARD_RARITY)
    sw = lambda k: "ON" if st.get(k, True) else "OFF"
    return (f"{HW_EMOJI} <b>Halloween event:</b> {state}\n"
            f"🌙 <b>Login:</b> {sw('login_on')}  •  🕯 <b>Haunt:</b> {sw('haunt_on')}  •  🍬 <b>Treat/Trick:</b> {sw('tot_on')}\n"
            f"<b>Halloween cards:</b> {len(pool)}  (Divine: {divines})\n"
            f"🧪 <b>Test users:</b> {sum(1 for u in db.get('users', {}).values() if isinstance(u, dict) and u.get('hw_test'))}")


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
            print(f"[halloween] photo failed ({src[:30]}...): {e}")
            if src == _IMG_FILE_IDS.get(url):
                _IMG_FILE_IDS.pop(url, None)
    await message.reply(cap, reply_markup=kb, parse_mode=ParseMode.HTML)


async def _edit_card(cq: CallbackQuery, cap: str, kb: InlineKeyboardMarkup) -> None:
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=cap, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(cap, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass   # "message is not modified"


async def _swap_card(cq: CallbackQuery, url: str, cap: str, kb: InlineKeyboardMarkup) -> None:
    """Edit the SAME message: new picture + caption + buttons (text-only edit if the message has no photo)."""
    if cq.message.photo:
        for src in [x for x in (_IMG_FILE_IDS.get(url), url) if x]:
            try:
                res = await cq.message.edit_media(
                    media=InputMediaPhoto(media=src, caption=cap, parse_mode=ParseMode.HTML), reply_markup=kb)
                if src == url and getattr(res, "photo", None):
                    _IMG_FILE_IDS[url] = res.photo[-1].file_id
                return
            except Exception as e:
                if "not modified" in str(e).lower():
                    return
                print(f"[halloween] edit_media failed ({src[:30]}...): {e}")
                if src == _IMG_FILE_IDS.get(url):
                    _IMG_FILE_IDS.pop(url, None)
    await _edit_card(cq, cap, kb)


def _from_home(cq: CallbackQuery) -> bool:
    """True if this message was opened from the /halloween card (it carries a Back-to-/halloween button)."""
    mk = cq.message.reply_markup
    for row in (mk.inline_keyboard if mk else []):
        for b in row:
            cd = b.callback_data or ""
            if cd.startswith("hwgo_back_") or cd.endswith("_backh"):
                return True
    return False


def _home_row(owner: str) -> list:
    return [_btn("Back", callback_data=f"hwgo_back_{owner}")]


def _miniapp_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
        text=f"{HW_EMOJI} Open Halloween Mini App", url=HW_MINIAPP_LINK)]])


def _start_text(days: int, last_day: str, login: bool, haunt: bool) -> str:
    live = []
    if login:
        live.append("<code>/hwlogin</code> 7-night login event")
    if haunt:
        live.append("<code>/haunt</code> daily quests")
    live += ["<code>/halloween</code>", "<code>/treat</code> + <code>/trick</code> (group)", "<code>/hwstore</code>",
             "<code>/halloween_lbd</code> leaderboard"]
    what = ("login + haunt" if login and haunt else "login only" if login else "haunt only")
    tail = (f"Clear your daily quests to earn candies: ~6 days for a Divine, ~7 days for a Halloween card.\n\n"
            if haunt else "\n")
    return (f"🎃 <b>Halloween event started</b> ({what})! <b>{days}</b> days — today is Day 1, "
            f"last day is <b>{last_day}</b> (UTC).\n"
            f"Players: " + ", ".join(live) + ".\n" + tail +
            f"{HW_EMOJI} Mini app: {HW_MINIAPP_LINK}")


_HW_USAGE = ("<b>Usage:</b>\n"
             "<code>/sthw on [days]</code> — start login + haunt\n"
             "<code>/sthw login on|off [days]</code>\n"
             "<code>/sthw haunt on|off [days]</code>\n"
             "<code>/sthw tot on|off</code> — /treat + /trick (work even when the event/haunt is off)\n"
             "<code>/sthw pause</code> | <code>extend &lt;days&gt;</code> | <code>decrease [days]</code> | <code>status</code> | <code>off</code>")


@main_router.message(Command("sthw"))
async def sthw_cmd(message: Message, command: CommandObject):
    """/sthw on [days] | login on|off [days] | haunt on|off [days] | pause | extend <days> | decrease [days] | status | off
    Owner + admins only."""
    if not _is_admin(message):
        return
    parts = (command.args or "").split()
    sub = parts[0].lower() if parts else "status"
    db = load_db()
    st = _state(db)

    if sub == "status":
        await message.reply(f"{_hw_status_text(db)}\n\n{HW_EMOJI} Mini app: {HW_MINIAPP_LINK}\n"
                            f"Leaderboard: /halloween_lbd",
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
            await message.reply("Usage: <code>/sthw extend &lt;days&gt;</code>", parse_mode=ParseMode.HTML)
            return
        _ok, msg = _ev_extend(db, n)
        await message.reply(f"{msg}\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
        return

    if sub in ("decrease", "decr", "reduce", "shorten"):
        n = 1                                                      # /sthw decrease  ==  /sthw decrease 1
        if len(parts) > 1:
            if not parts[1].isdigit() or int(parts[1]) <= 0:
                await message.reply("Usage: <code>/sthw decrease [days]</code>  (e.g. <code>/sthw decrease 1</code>)",
                                    parse_mode=ParseMode.HTML)
                return
            n = int(parts[1])
        _ok, msg = _ev_decrease(db, n)
        await message.reply(f"{msg}\n{_hw_status_text(db)}" if _ok else msg, parse_mode=ParseMode.HTML)
        return

    # ---- tot: /treat + /trick on or off (independent of the event) ----
    if sub in ("tot", "treat", "trick"):
        sw = parts[1].lower() if len(parts) > 1 else ""
        if sw not in ("on", "off"):
            await message.reply("Usage: <code>/sthw tot on|off</code>  (/treat + /trick)", parse_mode=ParseMode.HTML)
            return
        st["tot_on"] = (sw == "on")
        save_db()
        await message.reply(f"{'✅' if sw == 'on' else '⏹'} <b>/treat + /trick are now {sw.upper()}.</b>\n"
                            f"{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
        return

    # ---- login / haunt: switch ONE part on or off ----
    if sub in ("login", "haunt"):
        sw = parts[1].lower() if len(parts) > 1 else ""
        if sw not in ("on", "off"):
            await message.reply(f"Usage: <code>/sthw {sub} on|off [days]</code>", parse_mode=ParseMode.HTML)
            return
        key = f"{sub}_on"
        name = "🌙 Login event" if sub == "login" else "🕯 Haunt (quests)"
        running = bool(event_active(db) or st.get("paused_at"))

        if sw == "off":
            if not running:
                await message.reply(f"{HW_EMOJI} The event isn't running, nothing to turn off.", parse_mode=ParseMode.HTML)
                return
            st[key] = False
            save_db()
            await message.reply(f"⏹ <b>{name} is now OFF.</b> Players can't use it until you turn it on again.\n"
                                f"{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
            return

        if st.get("paused_at"):                                   # resume, then switch the part on
            _ok, msg = _ev_resume(db)
            if sub == "haunt" and not st.get("haunt_on", True):
                _mark_haunt_start(db)
            st[key] = True
            save_db()
            if sub == "haunt":
                assign_quests_all(db)
            await message.reply(f"{msg}\n✅ <b>{name} is ON.</b>\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        if event_active(db):
            if st.get(key, True):
                await message.reply(f"{name} is already ON.\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
                return
            if sub == "haunt":
                _mark_haunt_start(db)
            st[key] = True
            save_db()
            if sub == "haunt":
                assign_quests_all(db)
            await message.reply(f"✅ <b>{name} is now ON.</b>\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        days = DEFAULT_EVENT_DAYS                                  # no event yet: start it with ONLY this part
        if len(parts) > 2 and parts[2].isdigit():
            days = max(1, min(60, int(parts[2])))
        _day0, last_day = _ev_start(db, days, login=(sub == "login"), haunt=(sub == "haunt"))
        ensure_midnight_task()
        if sub == "haunt":
            assign_quests_all(db)
        await message.reply(_start_text(days, last_day, sub == "login", sub == "haunt"),
                            reply_markup=_miniapp_kb(), parse_mode=ParseMode.HTML)
        return

    if sub == "on":
        if st.get("paused_at"):                                   # resume
            _ok, msg = _ev_resume(db)
            await message.reply(f"{msg}\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        if event_active(db):
            await message.reply(f"{HW_EMOJI} Already running.\n{_hw_status_text(db)}", parse_mode=ParseMode.HTML)
            return
        days = DEFAULT_EVENT_DAYS
        if len(parts) > 1 and parts[1].isdigit():
            days = max(1, min(60, int(parts[1])))
        _day0, last_day = _ev_start(db, days)
        ensure_midnight_task()
        assign_quests_all(db)
        await message.reply(_start_text(days, last_day, True, True),
                            reply_markup=_miniapp_kb(), parse_mode=ParseMode.HTML)
        return

    await message.reply(_HW_USAGE, parse_mode=ParseMode.HTML)


HW_MAIN_IMAGE = "https://i.ibb.co/G6y6w48/Craft-joy-from-shadows-and-let-laughter-guide-your-haunted-journey.jpg"


def _halloween_kb(owner: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [_btn("Haunt", "primary", callback_data=f"hwgo_haunt_{owner}"),
         _btn("Candies", "success", callback_data=f"hwgo_candies_{owner}")],
        [_btn(f"Open Halloween {HW_EMOJI} App", "danger", url=HW_MINIAPP_LINK)],
    ])


def _halloween_text(db: dict, u: dict, uid) -> str:
    """The /halloween card. Bold only (the whole text is one bold block)."""
    st = _state(db)
    left, dn = event_seconds_left(db), event_day(db)
    if st.get("paused_at"):
        day, tl = (f"Day {dn[0]}/{dn[1]}" if dn else "Paused"), "Paused"
    elif left:
        day = f"Day {dn[0]}/{dn[1]}" if dn else "Running"
        tl = f"{_fmt_left(left)} left"
    elif u.get("hw_test"):
        td, tt, tl_s = _tester_clock(u)
        day, tl = f"Day {td}/{tt}", f"{_fmt_left(tl_s)} left"
    else:
        day, tl = "Not running", "Event ended"
    # Show the REAL switch state. The owner bypass is for using a part, not for displaying it as running.
    chk = uid if u.get("hw_test") else None
    login_on, haunt_on = login_enabled(db, chk), haunt_enabled(db, chk)
    hd = haunt_day(db)
    haunt_day_txt = f"Day {hd[0]}/{hd[1]}" if (hd and (left or st.get("paused_at")) and not u.get("hw_test")) else day
    lines = [
        f"「 {HW_EMOJI} HALLOWEEN 」", "━━━━━━━━━━━━━━━━━",
        f"[ Login Event ] : {day if login_on else 'Switched off'}",
        f"[ Login Event Time left ] : {tl if login_on else '-'}",
        f"[ Total candies {CANDY} ] : {candies_of(u):,}",
        "",
        f"[ Haunt Event ] : {haunt_day_txt if haunt_on else 'Switched off'}",
        f"[ Haunt Event Time left ] : {tl if haunt_on else '-'}",
    ]
    return ("<b>" + "\n".join(lines) + "</b>\n\n"
            "<blockquote><b>Open the Mini App for the login calendar, quests and the candy store</b></blockquote>")


@main_router.message(Command("halloween"))
async def halloween_cmd(message: Message):
    """/halloween — for EVERYONE: event clock, total candies, Haunt / Candies buttons + the Mini App."""
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    u = db["users"][user_id]
    await _reply_image(message, HW_MAIN_IMAGE, _halloween_text(db, u, uid_int), _halloween_kb(user_id))


@main_router.callback_query(F.data.startswith("hwgo_"))
async def hwgo_cb(cq: CallbackQuery):
    """/halloween buttons: Haunt / Candies / Back all edit the SAME message (no new messages)."""
    _, which, owner = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("Open your own with /halloween.", show_alert=True)
        return
    uid_int = cq.from_user.id
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    user = db["users"][owner]
    if which == "back":
        await _swap_card(cq, HW_MAIN_IMAGE, _halloween_text(db, user, uid_int), _halloween_kb(owner))
        await cq.answer()
        return
    if which == "candies":
        await _swap_card(cq, HW_CANDIES_IMAGE, candies_text(user), candies_kb(owner, True))
        await cq.answer()
        return
    if not _ev_on(db, uid_int):
        await cq.answer("The Halloween event isn't running right now.", show_alert=True)
        return
    if not haunt_enabled(db, uid_int):
        await cq.answer("Haunt is switched off right now.", show_alert=True)
        return
    ensure_midnight_task()
    _roll_quests(user)
    _haunt(db, user)
    save_db()
    await _swap_card(cq, HW_HAUNT_IMAGE, _haunt_text(db, user, uid_int), _haunt_kb(user, owner, True))
    await cq.answer()


@main_router.message(Command("hwcommands", "hwhelp"))
async def hwcommands_cmd(message: Message):
    """Command list, the same for everyone (admin commands are not listed)."""
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        return
    lines = [
        f"「 {HW_EMOJI} HALLOWEEN COMMANDS 」", "━━━━━━━━━━━━━━━━━",
        "[ PLAYERS ]",
        "/halloween - event clock, candies, Haunt and Candies buttons",
        "/hwlogin - 7-night login event (claim in the mini app)",
        "/haunt - your 5 daily quests",
        f"/treat - reply to a player to give them 1-2 candies ({TREAT_DAILY_USES} per {TREAT_WINDOW_HOURS}h)",
        f"/trick - Pumpkin Patch game ({TRICK_DAILY_USES}/day, {TRICK_INTERVAL_HOURS}h apart)",
        "/candies - your candy bag and converter",
        "/hwstore - candy store",
        "/hwlbd - leaderboard",
        "/trickortreat - how /treat and /trick work",
        "/hwhelp - this list",
    ]
    await message.reply("<b>" + "\n".join(lines) + "</b>", parse_mode=ParseMode.HTML)


def _hw_stats_text(db: dict) -> str:
    """Event-wide numbers for /hwstats. Test users are left out. Bold only."""
    eid = _state(db).get("event_id", 0)
    players = ads_total = ads_today = 0
    balance = earned = spent = bag = 0
    bought_n: dict = {k: 0 for k in STORE_ITEMS}
    buyers: dict = {k: 0 for k in STORE_ITEMS}
    login_users = login_done = nights = haunt_users = haunt_days = collectors = 0
    t_given = t_givers = t_recv = 0
    trick_plays = trick_wins = trick_users = 0
    tests = 0
    today = _today()
    for u in (db.get("users", {}) or {}).values():
        if not isinstance(u, dict):
            continue
        if u.get("hw_test"):
            tests += 1
            continue
        if not any(u.get(k) for k in HW_USER_KEYS):
            continue
        players += 1
        ads_total += int(u.get("hw_ads_total", 0) or 0)
        d = u.get("hw_ads_day")
        if isinstance(d, dict) and d.get("date") == today:
            ads_today += int(d.get("n", 0) or 0)
        balance += candies_of(u)
        earned += _earned_of(u)
        spent += _spent_of(u)
        bag += stock_value(u)
        if u.get("hw_collector"):
            collectors += 1
        for k, n in (u.get("hw_bought", {}) or {}).items():
            if k in bought_n and int(n or 0) > 0:
                bought_n[k] += int(n)
                buyers[k] += 1
        lg = u.get("hw_login")
        if isinstance(lg, dict) and lg.get("event") == eid and int(lg.get("streak", 0) or 0) > 0:
            login_users += 1
            nights += int(lg["streak"])
            if int(lg["streak"]) >= len(LOGIN_EVENT):
                login_done += 1
        h = u.get("hw_haunt")
        if isinstance(h, dict) and h.get("event") == eid and h.get("days"):
            haunt_users += 1
            haunt_days += len(h["days"])
        g = int(u.get("hw_treat_given", 0) or 0)
        t_given += g
        t_givers += 1 if g else 0
        t_recv += 1 if int(u.get("hw_treat_got", 0) or 0) else 0
        tc = int(u.get("hw_trick_count", 0) or 0)
        trick_plays += tc
        trick_users += 1 if tc else 0
        trick_wins += int(u.get("hw_trick_wins", 0) or 0)

    left, dn = event_seconds_left(db), event_day(db)
    if _state(db).get("paused_at"):
        ev = "Paused"
    elif left:
        ev = (f"Day {dn[0]}/{dn[1]} · " if dn else "") + f"{_fmt_left(left)} left"
    else:
        ev = "Not running"
    items_total = sum(bought_n.values())
    lines = [
        f"「 {HW_EMOJI} HALLOWEEN STATS 」", "━━━━━━━━━━━━━━━━━",
        f"[ Event ] : {ev}",
        f"[ Players ] : {players:,}" + (f"  (+{tests} test)" if tests else ""),
        "",
        f"[ Total Ads Watched ] : {ads_total:,}",
        f"[ Ads Watched Today ] : {ads_today:,}",
        "",
        f"[ Total Candies in Economy ] : {balance:,} {CANDY}",
        f"[ Candies Earned (all time) ] : {earned:,} {CANDY}",
        f"[ Candies Spent in Store ] : {spent:,} {CANDY}",
        f"[ Candy Bags (unconverted) ] : {bag:,} {CANDY}",
        f"[ Candy Collectors ] : {collectors:,}",
        "",
        f"[ Items Bought from Store ] : {items_total:,}",
    ]
    for k, v in STORE_ITEMS.items():
        lines.append(f"- {_esc(v[0])} : {bought_n[k]:,} bought · {buyers[k]:,} buyers · {bought_n[k] * v[1]:,} {CANDY}")
    lines += [
        "",
        f"[ Login Event ] : {login_users:,} started · {login_done:,} completed all {len(LOGIN_EVENT)} nights · {nights:,} nights claimed",
        f"[ Haunt ] : {haunt_users:,} players · {haunt_days:,} haunt days",
        f"[ Treats ] : {t_given:,} given · {t_givers:,} givers · {t_recv:,} receivers",
        f"[ Tricks ] : {trick_plays:,} played · {trick_users:,} players · {trick_wins:,} wins"
        + (f" ({trick_wins * 100 // trick_plays}%)" if trick_plays else ""),
        "",
        "[ NOTE ] : Ad counts start from the day /hwstats was added.",
    ]
    return "<b>" + "\n".join(lines) + "</b>"


@main_router.message(Command("hwstats"))
async def hwstats_cmd(message: Message):
    """/hwstats — owner + admins: ads, candy economy, store sales and every other event number."""
    if not _is_admin(message):
        return
    await message.reply(_hw_stats_text(load_db()), parse_mode=ParseMode.HTML)


@main_router.message(Command("hcard"))
async def hcard_cmd(message: Message, command: CommandObject):
    """/hcard on <db-id> | off <db-id> | list — manage Halloween cards."""
    if not _is_admin(message):
        return
    parts = (command.args or "").split()
    sub = parts[0].lower() if parts else ""
    db = load_db()
    gc = db.get("global_cards", {})

    if sub == "list":
        cards = sorted(((cid, c) for cid, c in gc.items() if is_halloween_card(c)),
                       key=lambda kv: (str(kv[1].get("rarity", "")), str(kv[1].get("name", "")).lower()))
        if not cards:
            await message.reply(f"{HW_EMOJI} No Halloween cards yet.\nMark one with <code>/hcard on DB-XXXXXX</code>.",
                                parse_mode=ParseMode.HTML)
            return
        divines = sum(1 for _, c in cards if format_rarity(c.get("rarity", "")) == HAUNT_REWARD_RARITY)
        chunks, cur = [], f"<b>「 {HW_EMOJI} HALLOWEEN CARDS 」</b> — {len(cards)} total, {divines} Divine\n━━━━━━━━━━━━━━━━━\n"
        for cid, c in cards:
            line = f"<code>{_esc(str(cid))}</code> — {_esc(str(c.get('name', '?')))} [{format_rarity(c.get('rarity', ''))}]\n"
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
            if is_halloween_card(card):
                await message.reply(f"{HW_EMOJI} <b>{name}</b> is already a Halloween card.", parse_mode=ParseMode.HTML)
                return
            card["event"] = HW_EVENT_KEY
            save_db()
            owners = sum(1 for u in db.get("users", {}).values()
                         if (u.get("cards", {}).get(cid) or {}).get("amount", 0) > 0)
            note = (f"\n⚠️ <b>{owners}</b> player(s) already own it and can no longer sell, gift, trade or burn it."
                    if owners else "")
            await message.reply(
                f"{HW_EMOJI} <b>{name}</b> [{format_rarity(card.get('rarity', ''))}] is now a Halloween card.\n"
                f"<i>Locked: no Offline Store sale, gift, trade or burn.</i>{note}",
                parse_mode=ParseMode.HTML)
        else:
            if card.get("event") != HW_EVENT_KEY and HW_EMOJI not in str(card.get("name", "")):
                await message.reply(f"<b>{name}</b> isn't a Halloween card.", parse_mode=ParseMode.HTML)
                return
            card.pop("event", None)
            save_db()
            extra = (f"\n⚠️ The name still contains {HW_EMOJI}, so it still counts as Halloween — "
                     f"rename it with /edit_card too." if HW_EMOJI in str(card.get("name", "")) else "")
            await message.reply(f"✅ Halloween mark removed from <b>{name}</b>.{extra}", parse_mode=ParseMode.HTML)
        return

    await message.reply(
        "<b>Usage:</b>\n<code>/hcard on DB-XXXXXX</code> — mark as Halloween card\n"
        "<code>/hcard off DB-XXXXXX</code> — remove the mark\n<code>/hcard list</code> — all Halloween cards",
        parse_mode=ParseMode.HTML)


# ==========================================
# TEST MODE: /hwtest <userid> on|off  |  /hwtest list  |  /hwtest clear_all   (owner + admins)
# ==========================================
# Every Halloween field stored on a player. Ending test mode wipes all of them.
HW_USER_KEYS = (
    "hw_candies", "hw_candies_earned", "hw_candy_stock", "hw_candy_box", "hw_collector",
    "hw_quests", "hw_haunt", "hw_login", "hw_login_ads", "hw_bought",
    "hw_treat_day", "hw_treat_to", "hw_treat_recv", "hw_treat_given", "hw_treat_got",
    "hw_trick_date", "hw_trick_count", "hw_trick_wins", "hw_trick_game", "hw_trick_day", "hw_trick_last", "hw_ads_total", "hw_ads_day",
)


def _reset_test_user(user: dict) -> None:
    """Leave test mode and wipe the player's Halloween data. Shards and cards that Halloween gave
    them while testing are taken back; anything they had before stays untouched."""
    grants = user.get("hw_test_grants") or {}
    sh = int(grants.get("shards", 0) or 0)
    if sh:
        user["nexus_shards"] = max(0, int(user.get("nexus_shards", 0) or 0) - sh)
    cards = user.get("cards", {})
    for cid, n in (grants.get("cards") or {}).items():
        entry = cards.get(cid)
        if entry:
            entry["amount"] = int(entry.get("amount", 0) or 0) - int(n)
            if entry["amount"] <= 0:
                cards.pop(cid, None)
    for k in HW_USER_KEYS + ("hw_test", "hw_test_grants", "hw_test_start"):
        user.pop(k, None)


@main_router.message(Command("hwtest"))
async def hwtest_cmd(message: Message, command: CommandObject):
    """/hwtest <userid> on|off | list | clear_all  — testers can use every Halloween command at any
    time (event off, parts off, private chats). off / clear_all reset their Halloween data."""
    if not _is_admin(message):
        return
    parts = (command.args or "").split()
    db = load_db()
    users = db.get("users", {})
    usage = ("<b>Usage:</b>\n<code>/hwtest &lt;userid&gt; on</code> — test mode for a player (or reply to them)\n"
             "<code>/hwtest &lt;userid&gt; off</code> — end test mode + reset their Halloween data\n"
             "<code>/hwtest list</code> — current testers\n"
             "<code>/hwtest clear_all</code> — end test mode for everyone + reset all their data")
    sub = parts[0].lower() if parts else ""

    if sub == "list":
        testers = [(uid, u) for uid, u in users.items() if isinstance(u, dict) and u.get("hw_test")]
        if not testers:
            await message.reply("🧪 No test users.", parse_mode=ParseMode.HTML)
            return
        lines = [f"<b>🧪 Test users ({len(testers)})</b>"]
        for uid, u in testers[:40]:
            lines.append(f"• {_uname(u)} — <code>{_esc(str(uid))}</code> — {candies_of(u):,} {CANDY}")
        if len(testers) > 40:
            lines.append(f"<i>…and {len(testers) - 40} more</i>")
        await message.reply("\n".join(lines), parse_mode=ParseMode.HTML)
        return

    if sub == "clear_all":
        n = 0
        for u in users.values():
            if isinstance(u, dict) and u.get("hw_test"):
                _reset_test_user(u)
                n += 1
        save_db()
        await message.reply(f"🧹 Test mode ended for <b>{n}</b> user(s); their Halloween data was reset.",
                            parse_mode=ParseMode.HTML)
        return

    # <userid> on|off   (or: reply to a player + on|off)
    if len(parts) >= 2 and parts[0].lstrip("-").isdigit():
        uid, action = parts[0], parts[1].lower()
    elif len(parts) == 1 and message.reply_to_message and message.reply_to_message.from_user:
        uid, action = str(message.reply_to_message.from_user.id), parts[0].lower()
    else:
        await message.reply(usage, parse_mode=ParseMode.HTML)
        return
    if action not in ("on", "off"):
        await message.reply(usage, parse_mode=ParseMode.HTML)
        return
    u = users.get(uid)
    if not isinstance(u, dict):
        await message.reply(f"User <code>{_esc(uid)}</code> not found. They must have started the bot.",
                            parse_mode=ParseMode.HTML)
        return
    name = _uname(u)
    if action == "on":
        if u.get("hw_test"):
            await message.reply(f"🧪 <b>{name}</b> is already a test user.", parse_mode=ParseMode.HTML)
            return
        u["hw_test"] = True
        u["hw_test_start"] = time.time()
        _roll_quests(u)                    # their event + today's quests start right now
        _haunt(db, u)
        save_db()
        await message.reply(f"🧪 <b>{name}</b> (<code>{_esc(uid)}</code>) is now a <b>test user</b>: their Halloween "
                            f"event (Day 1/{DEFAULT_EVENT_DAYS}) and today's quests started, and every Halloween "
                            f"command works for them even when the event is off.\n"
                            f"<code>/hwtest {_esc(uid)} off</code> resets their Halloween data.",
                            parse_mode=ParseMode.HTML)
        return
    if not u.get("hw_test"):
        await message.reply(f"<b>{name}</b> isn't a test user.", parse_mode=ParseMode.HTML)
        return
    _reset_test_user(u)
    save_db()
    await message.reply(f"🧹 <b>{name}</b> (<code>{_esc(uid)}</code>): test mode ended and Halloween data reset.",
                        parse_mode=ParseMode.HTML)


# ==========================================
# CANDY + CARD HELPERS
# ==========================================
def candies_of(user: dict) -> int:
    return int(user.get("hw_candies", 0) or 0)


def roll_candy_bag(user: dict) -> tuple:
    """Roll a treat bag of 1 (usually) or 2 (rarely) candies. Returns (pieces, direct_candies, collector_bonus).
    🍬 pieces add straight to the balance; other types go into user['hw_candy_stock'] (convertible).
    user['hw_candy_box'] is the lifetime 'found' log used for the Candy Collector bonus."""
    weights = [t[3] for t in CANDY_TYPES]
    k = 2 if random.random() < TREAT_DOUBLE_CHANCE else 1      # 1 candy, rarely 2
    picks = random.choices(CANDY_TYPES, weights=weights, k=k)
    pieces = [(e, n, v) for e, n, v, _ in picks]
    box = user.setdefault("hw_candy_box", {})
    stock = user.setdefault("hw_candy_stock", {})
    direct = 0
    for e, _, v in pieces:
        box[e] = box.get(e, 0) + 1
        if e == CANDY:
            direct += v
        else:
            stock[e] = stock.get(e, 0) + 1
    bonus = 0
    if not user.get("hw_collector") and all(box.get(t[0], 0) > 0 for t in CANDY_TYPES):
        user["hw_collector"] = True
        bonus = COLLECTOR_BONUS
    add_candies(user, direct + bonus)
    return pieces, direct, bonus


def _candy_value(emoji: str) -> int:
    return next((t[2] for t in CANDY_TYPES if t[0] == emoji), 0)


def stock_value(user: dict) -> int:
    return sum(_candy_value(e) * n for e, n in (user.get("hw_candy_stock", {}) or {}).items())


CANDY_LABELS = {"🍭": "Lollipop", "🍫": "Choco Bars", "🍪": "Cookies", "🍩": "Donuts", "🍰": "Pastry"}
# Same names as /candies, singular form for "+ 1 ..." reward lines
CANDY_LABELS_ONE = {CANDY: "Candy", "🍭": "Lollipop", "🍫": "Choco Bar", "🍪": "Cookie", "🍩": "Donut", "🍰": "Pastry"}
CANDY_LABELS_MANY = {CANDY: "Candies", **CANDY_LABELS}


def _reward_name(emoji: str, n: int) -> str:
    return (CANDY_LABELS_ONE if n == 1 else CANDY_LABELS_MANY).get(emoji, "Candy")


def _bag(user: dict) -> list:
    """[(emoji, label, count, value each in 🍬)] for the convertible treats the player holds."""
    stock = user.get("hw_candy_stock", {}) or {}
    return [(e, CANDY_LABELS.get(e, nm), int(stock.get(e, 0) or 0), v)
            for e, nm, v, _w in CANDY_TYPES[1:] if int(stock.get(e, 0) or 0) > 0]


def candies_text(user: dict) -> str:
    """The /candies card. Bold only."""
    stock = user.get("hw_candy_stock", {}) or {}
    lines = [f"Total Candy : {candies_of(user)} candies {CANDY}", "", "Current Treats -"]
    for e, nm, _v, _w in CANDY_TYPES[1:]:
        lines.append(f"[{e} {CANDY_LABELS.get(e, nm)} ] - {int(stock.get(e, 0) or 0)}")
    lines += ["", f"[NOTE] : Candy {CANDY} is used to buy items from ( /hwstore )"]
    return "<b>" + "\n".join(lines) + "</b>"


def candies_kb(owner: str, home: bool = False) -> InlineKeyboardMarkup:
    rows = [[_btn("Convert", "primary", callback_data=f"hwcm_{owner}_open{'h' if home else ''}")]]
    if home:
        rows.append(_home_row(owner))
    return InlineKeyboardMarkup(inline_keyboard=rows)


def convert_text(user: dict, result: str = "") -> str:
    """The convert screen: every treat with its value in 🍬. Bold only."""
    bag = _bag(user)
    lines = [f"「 {HW_EMOJI} CONVERT 」", "━━━━━━━━━━━━━━━━━", ""]
    if bag:
        for e, nm, n, v in bag:
            lines += [f"[{e} {nm} ] - x{n}",
                      f"[VALUE] - {v} {CANDY} each",
                      f"[EXCHANGE] - {n * v} {CANDY}", ""]
        tot = sum(n * v for _e, _nm, n, v in bag)
        lines.append(f"[TOTAL] : {tot} {CANDY}")
    else:
        lines.append("[BAG] : Empty. Collect treats with /treat to convert them here.")
    lines += [f"[BALANCE] : {candies_of(user)} {CANDY}",
              "", "[NOTE] : Converting is instant and cannot be undone.",
              "[NOTE] : Candy to Shards is only available in ( /hwstore )"]
    if result:
        lines += ["", f"[DONE] : {result}"]
    return "<b>" + "\n".join(lines) + "</b>"


def convert_kb(owner: str, user: dict, home: bool = False) -> InlineKeyboardMarkup:
    rows, bag = [], _bag(user)
    for i, (e, _nm, n, v) in enumerate(CANDY_TYPES):
        if i == 0:
            continue
        hit = next((b for b in bag if b[0] == e), None)
        if not hit:
            continue
        n, v = hit[2], hit[3]
        rows.append([_btn(f"{e}×{n} → {n * v}{CANDY}", "success", callback_data=f"hwcv_{owner}_{i}_c")])
    if bag:
        val = sum(n * v for _e, _nm, n, v in bag)
        rows.append([_btn(f"All → {val}{CANDY}", "success", callback_data=f"hwcv_{owner}_a_c")])
    rows.append([_btn("Back", callback_data=f"hwcm_{owner}_back{'h' if home else ''}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _spent_of(user: dict) -> int:
    """Candies spent in the store (derived from purchases, so it works for old accounts too)."""
    bought = user.get("hw_bought", {}) or {}
    return sum(int(bought.get(k, 0) or 0) * v[1] for k, v in STORE_ITEMS.items())


def _earned_of(user: dict) -> int:
    """Lifetime candies earned this event (leaderboard stat). Accounts from before tracking = balance + spent."""
    if "hw_candies_earned" in user:
        return int(user["hw_candies_earned"] or 0)
    return candies_of(user) + _spent_of(user)


def add_candies(user: dict, n: int) -> None:
    n = int(n)
    user["hw_candies_earned"] = _earned_of(user) + max(0, n)   # read BEFORE the balance changes
    user["hw_candies"] = candies_of(user) + n


def award_seize_candies(db: dict, user: dict, global_card: dict) -> int:
    """Kept so the hook in seize_cmd keeps working. /seize gives no candies any more
    (the 'seize' quest still counts through quest_progress)."""
    return 0


def _grant_card(user: dict, cid: str, card: dict) -> None:
    cards = user.setdefault("cards", {})
    entry = cards.setdefault(cid, {
        "name": card.get("name", "Card"),
        "rarity": card.get("rarity", "Basic 🃏"),
        "amount": 0,
    })
    entry["amount"] = entry.get("amount", 0) + 1
    if user.get("hw_test"):
        g = user.setdefault("hw_test_grants", {}).setdefault("cards", {})
        g[cid] = int(g.get(cid, 0)) + 1


def _locked_series(db: dict) -> set:
    """Anime series locked with /lock_drop (settings['locked_animes']), lower-cased."""
    return {str(a).lower().strip() for a in db.get("settings", {}).get("locked_animes", []) or []}


def _pick_card(db: dict, rarities, halloween: bool):
    """Random global card in one of `rarities`.
      halloween=True  -> ONLY cards marked Halloween (is_halloween_card). The series lock is ignored,
                         because Halloween series are normally kept locked so they never drop.
      halloween=False -> ONLY non-Halloween cards from UNLOCKED series (not in /lock_drop)."""
    if isinstance(rarities, str):
        rarities = (rarities,)
    locked = set() if halloween else _locked_series(db)
    pool = {
        cid: c for cid, c in db.get("global_cards", {}).items()
        if format_rarity(c.get("rarity", "")) in rarities
        and is_halloween_card(c) == halloween
        and str(c.get("anime", "")).lower().strip() not in locked
    }
    if not pool:
        return None, None
    cid = random.choice(list(pool))
    return cid, pool[cid]


# ==========================================
# PLAYER COMMANDS: /treat (candies for a replied-to player) and /trick (shards)
# ==========================================
async def _tot_guard(message: Message, date_key: str, cmd: str, done_text: str):
    """Shared checks for /treat and /trick. Returns (db, user, user_id, today) or None (already replied)."""
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return None
    if TOT_COMMUNITY_ONLY and message.chat.type not in ("group", "supergroup") and not is_test_user(load_db(), uid_int):
        await message.reply(f"{HW_EMOJI} <code>/{cmd}</code> is a <b>community command</b> — "
                            f"use it in the group chat.", parse_mode=ParseMode.HTML)
        return None
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    if not tot_enabled(db, user_id):
        await message.reply(f"{HW_EMOJI} <code>/{cmd}</code> is turned off right now.", parse_mode=ParseMode.HTML)
        return None
    user = db["users"][user_id]
    today = _today()
    if date_key and user.get(date_key) == today:
        await message.reply(done_text, parse_mode=ParseMode.HTML)
        return None
    return db, user, user_id, today


def _treat_window() -> str:
    """Id of the current /treat limit window (resets every TREAT_WINDOW_HOURS, aligned to 00:00 UTC)."""
    return str(int(time.time() // (TREAT_WINDOW_HOURS * 3600)))


def _treat_reset_in() -> int:
    span = TREAT_WINDOW_HOURS * 3600
    return int(span - time.time() % span)


def _mention(u) -> str:
    return f'<a href="tg://user?id={u.id}">{_esc(u.first_name or "Player")}</a>'


@main_router.message(Command("treat"))
async def treat_cmd(message: Message):
    """Reply to a player's message with /treat to give them one random candy.
    Giver: TREAT_DAILY_USES per 12h window. Receiver: up to TREAT_RECEIVE_DAILY_MAX per 12h window."""
    giver_tg = message.from_user
    if is_ghost_banned(giver_tg.id) or is_shadow_banned(giver_tg.id):
        return
    if message.chat.type not in ("group", "supergroup"):
        await message.reply("<b>/treat</b> works in group chats. Reply to someone's message with /treat.",
                            parse_mode=ParseMode.HTML)
        return
    target = message.reply_to_message.from_user if message.reply_to_message else None
    if not target:
        await message.reply("Reply to a player's message with <b>/treat</b> to give them candies.",
                            parse_mode=ParseMode.HTML)
        return
    if target.is_bot:
        await message.reply("Bots don't eat candy.", parse_mode=ParseMode.HTML)
        return
    if target.id == giver_tg.id:
        await message.reply("You can't treat yourself. Reply to someone else.", parse_mode=ParseMode.HTML)
        return
    if is_ghost_banned(target.id) or is_shadow_banned(target.id):
        return

    gid, tid = str(giver_tg.id), str(target.id)
    db = ensure_user(gid, giver_tg.first_name, giver_tg.username)
    if not (tot_enabled(db, gid) or is_test_user(db, tid)):
        await message.reply("/treat is turned off right now.", parse_mode=ParseMode.HTML)
        return
    giver = db["users"][gid]
    now = time.time()

    # giver daily limit
    gd = giver.get("hw_treat_day")
    if not isinstance(gd, dict) or gd.get("date") != _treat_window():
        gd = {"date": _treat_window(), "n": 0}
    if gd["n"] >= TREAT_DAILY_USES:
        await message.reply(f"You've used all {TREAT_DAILY_USES} treats for now. They refill in "
                            f"<b>{_fmt_left(_treat_reset_in())}</b>.", parse_mode=ParseMode.HTML)
        return
    # same person twice
    recent = {k: v for k, v in (giver.get("hw_treat_to", {}) or {}).items()
              if now - float(v) < TREAT_SAME_USER_HOURS * 3600}
    if tid in recent:
        left = int(TREAT_SAME_USER_HOURS * 3600 - (now - float(recent[tid])))
        await message.reply(f"You already treated {_mention(target)}. Try someone else, "
                            f"or wait <b>{_fmt_left(left)}</b>.", parse_mode=ParseMode.HTML)
        return

    db = ensure_user(tid, target.first_name, target.username)
    receiver = db["users"][tid]
    giver = db["users"][gid]
    win = _treat_window()
    rec = receiver.get("hw_treat_recv")
    if not isinstance(rec, dict) or rec.get("date") != win:
        rec = {"date": win, "n": 0}
    if rec["n"] >= TREAT_RECEIVE_DAILY_MAX:
        await message.reply(f"{_mention(target)} has had enough treats for now. Try again in {_fmt_left(_treat_reset_in())}.",
                            parse_mode=ParseMode.HTML)
        return

    pieces, direct, bonus = roll_candy_bag(receiver)
    rec["n"] += 1
    receiver["hw_treat_recv"] = rec
    recent[tid] = now
    giver["hw_treat_to"] = recent
    gd["n"] += 1
    giver["hw_treat_day"] = gd
    giver["hw_treat_given"] = int(giver.get("hw_treat_given", 0) or 0) + 1
    receiver["hw_treat_got"] = int(receiver.get("hw_treat_got", 0) or 0) + 1
    save_db()

    # reward lines: one per candy type, named like in /candies
    got = {}
    for e, _, _ in pieces:
        got[e] = got.get(e, 0) + 1
    lines = [
        f"<b>Treat for {_mention(target)}</b>",
        f"<blockquote><i>{random.choice(TREAT_LINES)}</i></blockquote>",
        f"~ {_mention(giver_tg)}",
        "",
        "<b>[ REWARD ] : </b>",
    ]
    for e, n in got.items():
        lines.append(f"+ {n} {_reward_name(e, n)} {e}")
    if bonus:
        lines.append(f"+ {bonus} Collector Bonus {CANDY}")
    await message.reply("\n".join(lines), parse_mode=ParseMode.HTML)


_TRICK_ICON = {"g": "👻", "s": "💠", "c": CANDY}


def _trick_text(game: dict, who: str, result: str = "") -> str:
    """The /trick Pumpkin Patch card. Bold only."""
    lines = ["「 👻 PUMPKIN PATCH 」", "━━━━━━━━━━━━━━━━━"]
    if not result:
        lines += [f"Pick a pumpkin {who}"]
    else:
        lines += [who, "", result]
    return "<b>" + "\n".join(lines) + "</b>\n<blockquote><i>" + _esc(game["quote"]) + "</i></blockquote>"


def _trick_kb(owner: str, game: dict) -> InlineKeyboardMarkup:
    done = bool(game.get("done"))
    row, rows = [], []
    for i, c in enumerate(game["cells"]):
        if done:
            e = _TRICK_ICON.get(c, "👻")
            row.append(_btn(f"[ {e} ]" if i == game.get("pick") else e,
                            "danger" if c == "g" else "success", callback_data=f"hwtk_{owner}_x"))
        else:
            row.append(_btn("🎃", "primary", callback_data=f"hwtk_{owner}_{i}"))
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return InlineKeyboardMarkup(inline_keyboard=rows)


@main_router.message(Command("trick"))
async def trick_cmd(message: Message):
    g = await _tot_guard(message, None, "trick", "")
    if not g:
        return
    db, user, user_id, today = g
    game = user.get("hw_trick_game")
    pending = isinstance(game, dict) and not game.get("done")
    if not pending:
        now = time.time()
        day = user.get("hw_trick_day")
        if not isinstance(day, dict) or day.get("date") != today:
            day = {"date": today, "n": 0}
        cd_left = int(float(user.get("hw_trick_last", 0) or 0) + TRICK_INTERVAL_HOURS * 3600 - now)
        if day["n"] >= TRICK_DAILY_USES:
            left = max(int(86400 - now % 86400), cd_left)
            await message.reply(f"<b>{HW_EMOJI} You've used all {TRICK_DAILY_USES} tricks today. "
                                f"Next one in {_fmt_left(left)}.</b>", parse_mode=ParseMode.HTML)
            return
        if cd_left > 0:
            await message.reply(f"<b>{HW_EMOJI} The patch is resting. Next trick in {_fmt_left(cd_left)}.</b>",
                                parse_mode=ParseMode.HTML)
            return
        cells = ["g"] * TRICK_SPOOKS + ["s"] * TRICK_SHARD_PUMPKINS + ["c"] * TRICK_CANDY_PUMPKINS
        random.shuffle(cells)
        lo, hi = TRICK_SHARD_RANGE
        game = {"date": today, "cells": cells,
                "shards": random.randint(lo // 50, hi // 50) * 50,
                "candy": random.randint(*TRICK_CANDY_RANGE),
                "quote": random.choice(TRICK_LINES), "done": False}
        user["hw_trick_game"] = game
        save_db()
    await message.reply(_trick_text(game, _mention(message.from_user)),
                        reply_markup=_trick_kb(user_id, game), parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("hwtk_"))
async def hwtk_cb(cq: CallbackQuery):
    _, owner, pick = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your pumpkin patch. Use /trick.", show_alert=True)
        return
    if pick == "x":
        await cq.answer()
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    user = db["users"][owner]
    if not tot_enabled(db, owner):
        await cq.answer("/trick is turned off right now.", show_alert=True)
        return
    game = user.get("hw_trick_game")
    if not isinstance(game, dict) or game.get("done"):
        await cq.answer("This game is over. Use /trick for a new one.", show_alert=True)
        try:
            await cq.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
        return
    try:
        idx = int(pick)
        kind = game["cells"][idx]
    except (ValueError, IndexError):
        await cq.answer("Unknown pumpkin.", show_alert=True)
        return
    today = _today()
    game["done"], game["pick"] = True, idx
    day = user.get("hw_trick_day")
    if not isinstance(day, dict) or day.get("date") != today:
        day = {"date": today, "n": 0}
    day["n"] += 1
    user["hw_trick_day"] = day
    user["hw_trick_date"] = today
    user["hw_trick_last"] = time.time()
    user["hw_trick_count"] = int(user.get("hw_trick_count", 0) or 0) + 1
    if kind == "s":
        _add_shards(user, int(game["shards"]))
        user["hw_trick_wins"] = int(user.get("hw_trick_wins", 0) or 0) + 1
        result = (f"[ REWARD ] : + {game['shards']} Nexus Shards 💠\n"
                  f"[ SHARDS ] : {int(user.get('nexus_shards', 0) or 0):,} 💠")
        quote, toast = random.choice(TRICK_WIN_LINES), f"+{game['shards']} shards!"
    elif kind == "c":
        add_candies(user, int(game["candy"]))
        user["hw_trick_wins"] = int(user.get("hw_trick_wins", 0) or 0) + 1
        result = (f"[ REWARD ] : + {game['candy']} Rare Candy {CANDY}\n"
                  f"[ CANDIES ] : {candies_of(user):,} {CANDY}")
        quote, toast = "A rare candy, hidden deep in the vines.", f"+{game['candy']} rare candy!"
    else:
        result = "[ REWARD ] : None. A ghost 👻 was hiding here."
        quote, toast = random.choice(TRICK_LOSE_LINES), "A ghost! Nothing this time."
    game["quote"] = quote
    save_db()
    await _edit_card(cq, _trick_text(game, _mention(cq.from_user), result), _trick_kb(owner, game))
    await cq.answer(toast)


@main_router.message(Command("trickortreat"))
async def trickortreat_info_cmd(message: Message):
    if is_ghost_banned(message.from_user.id) or is_shadow_banned(message.from_user.id):
        return
    await message.reply(
        f"<b>「 {HW_EMOJI} TRICK OR TREAT 」\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"[ /treat ] {CANDY}\n"
        f"Reply to a player to give them 1-2 candies.\n"
        f"[ LIMIT ] : {TREAT_DAILY_USES} times every {TREAT_WINDOW_HOURS}h\n\n"
        f"[ /trick ] 👻\n"
        f"Pick a pumpkin: shards 💠, a rare candy {CANDY} or a ghost.\n"
        f"[ LIMIT ] : {TRICK_DAILY_USES} times a day, {TRICK_INTERVAL_HOURS}h apart\n\n"
        f"[ NOTE ] : Both work in the group chat. Convert treats at /candies.</b>",
        parse_mode=ParseMode.HTML)


HW_CANDIES_IMAGE = "https://i.ibb.co/Ys20hDM/Download-premium-image-of-Spooky-Halloween-night-background-by-Wan-about-halloween-tree-night-sky-h.jpg"


@main_router.message(Command("candies"))
async def candies_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    u = db["users"][user_id]
    await _reply_image(message, HW_CANDIES_IMAGE, candies_text(u), candies_kb(user_id))


# ==========================================
# CANDY STORE: /hwstore
# ==========================================
def _store_gate(db: dict, user: dict, key: str):
    """Reason text if this store item is still locked for the player, else None."""
    need = STORE_REQ_HAUNT_DAYS.get(key)
    if need:
        have = len(_haunt(db, user)["days"])
        if have < need:
            return f"Locked — finish {need} haunt days first ({have}/{need}). See /haunt."
    return None


HW_STORE_IMAGE = "https://i.ibb.co/cXN5pKVm/Trick-or-Treat-Cute-Halloween-Desktop-Wallpaper.jpg"

# Clean, emoji-free names for the store UI (STORE_ITEMS labels stay untouched for the web API).
STORE_NAMES = {
    "sh500":  "500 Nexus Shards",
    "elite":  "Random Elite Card",
    "divine": "Random Divine Card",
    "hwcard": "Mystery Halloween Card",
}
STORE_BTN_NAMES = {
    "sh500":  "500 Shards",
    "elite":  "Elite Card",
    "divine": "Divine Card",
    "hwcard": "Halloween Card",
}


def _store_name(key: str) -> str:
    item = STORE_ITEMS.get(key)
    return STORE_NAMES.get(key) or (item[0] if item else key)


def _store_text(db: dict, user: dict, note: str = "") -> str:
    """The /hwstore card. Bold only on the title and item names."""
    bought = user.get("hw_bought", {})
    lines = [f"<b>「 {HW_EMOJI} CANDY STORE 」</b>", "━━━━━━━━━━━━━━━━━"]
    for n, (key, (_label, price, limit, _k, _v)) in enumerate(STORE_ITEMS.items(), 1):
        have = bought.get(key, 0)
        if have >= limit:
            status = "Sold out"
        elif _store_gate(db, user, key):
            status = "Locked"
        else:
            status = f"{have}/{limit} bought"
        lines += [f"<b>[ {n}. {_store_name(key)} ]</b>", f"Price : {price:,} {CANDY}  |  {status}", ""]
    if note:
        lines += [note, ""]
    lines.append(f"• Your Candies : {candies_of(user):,} {CANDY}")
    return ("\n".join(lines) + "\n\n<blockquote>[ NOTE ] : Earn candies from /haunt quests and /treat. "
            "The Mystery Halloween Card is limited to 1 per player</blockquote>")


def _store_kb(user_id: str) -> InlineKeyboardMarkup:
    nums = [_btn(str(n), "primary", callback_data=f"hwbuy_{user_id}_{key}")
            for n, key in enumerate(STORE_ITEMS, 1)]
    return InlineKeyboardMarkup(inline_keyboard=[
        nums,
        [_btn("Close", "danger", callback_data=f"hwclose_{user_id}")],
    ])


def _purchase(db: dict, user: dict, key: str):
    """Validate, charge and grant one store item (used by the bot and the web API).
    Returns (error_text | None, result dict)."""
    item = STORE_ITEMS.get(key)
    if not item:
        return "Item not found.", None
    if not (event_active(db) or user.get("hw_test")):
        return "The store is closed.", None
    label, price, limit, kind, value = item
    bought = user.setdefault("hw_bought", {})
    if bought.get(key, 0) >= limit:
        return "You've reached the limit for this item.", None
    gate = _store_gate(db, user, key)
    if gate:
        return gate, None
    if candies_of(user) < price:
        return f"Not enough candies — you need {price - candies_of(user)} more.", None

    # Work out the prize BEFORE charging, so an empty pool never eats candies.
    card_id, card = None, None
    if kind == "shards":
        prize, name, rarity = f"+{value} Nexus Shards", f"{value} Nexus Shards", ""
    else:
        card_id, card = _pick_card(db, value, halloween=(kind == "hwcard"))
        if not card:
            return "That item is out of stock right now — you weren't charged.", None
        name, rarity = str(card.get("name", "Card")), format_rarity(card.get("rarity", ""))
        prize = f"{_esc(name)} [{rarity}]"

    user["hw_candies"] = candies_of(user) - price
    bought[key] = bought.get(key, 0) + 1
    if kind == "shards":
        _add_shards(user, value)
    else:
        _grant_card(user, card_id, card)
    save_db()
    return None, {"label": label, "prize": prize, "card": card, "card_id": card_id,
                  "name": name, "rarity": rarity, "shards": value if kind == "shards" else 0}


@main_router.message(Command("hwstore"))
async def hwstore_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    if not _ev_on(db, user_id):
        await message.reply("<b>The Halloween store is closed right now.</b>", parse_mode=ParseMode.HTML)
        return
    await _reply_image(message, HW_STORE_IMAGE, _store_text(db, db["users"][user_id]), _store_kb(user_id))


@main_router.callback_query(F.data.startswith("hwcv_"))
async def hwcv_cb(cq: CallbackQuery):
    """Convert candy items from the bag into 🍬 (shards: store only)."""
    _, owner, which, to = cq.data.split("_", 3)
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    if not _ev_on(db, owner):
        await cq.answer("The event isn't running right now.", show_alert=True)
        return
    if to != "c":
        await cq.answer("Candy to Shards is only available in the store (/hwstore).", show_alert=True)
        return
    user = db["users"][owner]
    stock = user.setdefault("hw_candy_stock", {})
    if which == "a":
        targets = [t[0] for t in CANDY_TYPES[1:]]
    else:
        try:
            targets = [CANDY_TYPES[int(which)][0]]
        except (ValueError, IndexError):
            await cq.answer("Unknown candy.", show_alert=True)
            return
        if targets[0] == CANDY:
            await cq.answer("🍬 is the main currency — nothing to convert.", show_alert=True)
            return
    value, taken = 0, []
    for e in targets:
        n = int(stock.get(e, 0) or 0)
        if n > 0:
            value += n * _candy_value(e)
            taken.append(f"{e}×{n}")
            stock[e] = 0
    if value <= 0:
        await cq.answer("Nothing to convert.", show_alert=True)
        return
    add_candies(user, value)
    msg = f"{' '.join(taken)} converted to +{value} {CANDY}"
    save_db()
    try:
        await _edit_card(cq, convert_text(user, msg), convert_kb(owner, user, _from_home(cq)))
    except Exception:
        pass
    await cq.answer(msg)


@main_router.callback_query(F.data.startswith("hwcm_"))
async def hwcm_cb(cq: CallbackQuery):
    """/candies <-> convert screen."""
    _, owner, view = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    user = db["users"][owner]
    home = view.endswith("h")
    if (view[:-1] if home else view) == "open":
        text, kb = convert_text(user), convert_kb(owner, user, home)
    else:
        text, kb = candies_text(user), candies_kb(owner, home)
    try:
        await _edit_card(cq, text, kb)
    except Exception:
        pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("hwclose_"))
async def hwclose_cb(cq: CallbackQuery):
    if str(cq.from_user.id) != cq.data.split("_", 1)[1]:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    try:
        await cq.message.delete()
    except Exception:
        pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("hwbuy_"))
async def hwbuy_cb(cq: CallbackQuery):
    """Step 1: tapped an item -> confirmation screen."""
    _, owner, key = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    item = STORE_ITEMS.get(key)
    if not item:
        await cq.answer("Item not found.", show_alert=True)
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    if not _ev_on(db, owner):
        await cq.answer("The store is closed.", show_alert=True)
        return
    label, price, limit, *_ = item
    user = db["users"][owner]
    if user.get("hw_bought", {}).get(key, 0) >= limit:
        await cq.answer("You've reached the limit for this item.", show_alert=True)
        return
    gate = _store_gate(db, user, key)
    if gate:
        await cq.answer(gate, show_alert=True)
        return
    if candies_of(user) < price:
        await cq.answer(f"Not enough candies — you need {price - candies_of(user)} more.", show_alert=True)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [_btn(f"Buy for {price:,}", "success", callback_data=f"hwok_{owner}_{key}")],
        [_btn("Back", "danger", callback_data=f"hwback_{owner}")],
    ])
    text = (f"<b>「 {HW_EMOJI} CONFIRM PURCHASE 」</b>\n━━━━━━━━━━━━━━━━━\n"
            f"<b>[ {_store_name(key)} ]</b>\n"
            f"Price : {price:,} {CANDY}\n"
            f"Balance : {candies_of(user):,} {CANDY}\n"
            f"After purchase : {candies_of(user) - price:,} {CANDY}")
    await _edit_card(cq, text, kb)
    await cq.answer()


@main_router.callback_query(F.data.startswith("hwback_"))
async def hwback_cb(cq: CallbackQuery):
    owner = cq.data.split("_", 1)[1]
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    await _edit_card(cq, _store_text(db, db["users"][owner]), _store_kb(owner))
    await cq.answer()


@main_router.callback_query(F.data.startswith("hwok_"))
async def hwok_cb(cq: CallbackQuery):
    """Step 2: confirmed -> re-validate, charge, grant."""
    _, owner, key = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("This isn't your menu.", show_alert=True)
        return
    item = STORE_ITEMS.get(key)
    if not item:
        await cq.answer("Item not found.", show_alert=True)
        return
    db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
    if not _ev_on(db, owner):
        await cq.answer("The store is closed.", show_alert=True)
        return

    user = db["users"][owner]
    err, res = _purchase(db, user, key)
    if err:
        await cq.answer(err, show_alert=True)
        return
    prize_text, card = res["prize"], res["card"]

    text = (f"<b>「 {HW_EMOJI} PURCHASE COMPLETE 」</b>\n━━━━━━━━━━━━━━━━━\n"
            f"<b>[ {_store_name(key)} ]</b>\n"
            f"You got : <b>{prize_text}</b>\n"
            f"Remaining : {candies_of(user):,} {CANDY}")
    kb = InlineKeyboardMarkup(inline_keyboard=[[_btn("Back to store", "primary", callback_data=f"hwback_{owner}")]])
    if card and card.get("file_id"):
        try:
            await cq.message.reply_photo(photo=card["file_id"], caption=text, parse_mode=ParseMode.HTML)
            await _edit_card(cq, _store_text(db, user), _store_kb(owner))
            await cq.answer("Purchased!")
            return
        except Exception:
            pass
    await _edit_card(cq, text, kb)
    await cq.answer("Purchased!")


# ==========================================
# DAILY QUESTS
# ==========================================
DAILY_QUEST_COUNT = 5            # quests handed out per player per UTC day
ALL_DONE_BONUS = 100             # extra candies for finishing every quest of the day
QUEST_NOTIFY = True              # DM the player when a quest completes (best effort)

# Haunt = the event-long goal. A "haunt day" counts when the player finishes at least
# HAUNT_DAY_MIN_QUESTS of that day's quests; HAUNT_DAYS_REQUIRED such days unlock the
# Halloween Divine in /hwstore (STORE_REQ_HAUNT_DAYS).
HAUNT_DAYS_REQUIRED = 7
HAUNT_DAY_MIN_QUESTS = DAILY_QUEST_COUNT      # default: all of the day's quests
HAUNT_REWARD_RARITY = "Divine ❄️"             # the Halloween Divine sold in /hwstore

# key -> (text, (min, max) target, step, candy reward)
QUESTS = {
    "shards":      ("Earn {t} shards",                                 (1000, 2000), 100, 60),
    "versus_play": ("Play {t} versus matches",                         (4, 6),         1, 40),
    "guess":       ("Correctly guess {t} cards",                       (10, 20),       1, 50),
    "scramble":    ("Play {t} Scramble games",                         (10, 20),       1, 50),
    "seize":       ("Seize {t} cards",                                 (2, 4),         1, 30),
    "mines":       ("Play {t} Mines games",                            (2, 5),         1, 30),
    "airdrop":     ("Claim your airdrop",                              (1, 1),         1, 40),
    "roll":        ("Use /roll {t} times",                             (11, 15),       1, 40),
    "throw":       ("Use /throw {t} times",                            (12, 18),       1, 40),
    "burn":        ("Burn {t} cards",                                  (2, 5),         1, 30),
    "trade":       ("Complete {t} trades",                             (2, 4),         1, 50),
    "versus_win":  ("Win {t} versus matches",                          (2, 4),         1, 50),
    "store_buy":   ("Buy {t} cards from the online or offline store",  (1, 3),         1, 40),
}


def _today() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def _roll_quests(user: dict) -> dict:
    """Return today's quest set for this user, creating it on first use."""
    q = user.get("hw_quests")
    if isinstance(q, dict) and q.get("date") == _today():
        return q
    items = []
    for key in random.sample(list(QUESTS), min(DAILY_QUEST_COUNT, len(QUESTS))):
        _text, (lo, hi), step, reward = QUESTS[key]
        target = random.randint(lo // step, hi // step) * step
        items.append({"k": key, "t": target, "p": 0, "r": reward, "done": False, "claimed": False})
    q = {"date": _today(), "items": items, "bonus": False}
    user["hw_quests"] = q
    return q


async def _send_quiet(uid: str, text: str) -> None:
    try:
        await bot.send_message(chat_id=int(uid), text=text, parse_mode=ParseMode.HTML)
    except Exception:
        pass


def _notify(uid: str, text: str) -> None:
    if not QUEST_NOTIFY:
        return
    try:
        asyncio.get_running_loop().create_task(_send_quiet(uid, text))
    except RuntimeError:
        pass   # not inside the event loop


def _it_claimed(it: dict) -> bool:
    """Reward already paid? Quests finished before the claim system existed have no 'claimed' key
    and were paid automatically, so a done quest without the key counts as claimed."""
    return bool(it.get("claimed", it.get("done", False)))


def _bonus_ready(q: dict) -> bool:
    return bool(q["items"]) and all(i["done"] for i in q["items"]) and not q.get("bonus")


def claim_quest_rewards(user: dict) -> tuple:
    """Pay every finished-but-unclaimed quest of today. Returns (candies paid, quests claimed)."""
    q = _roll_quests(user)
    total = n = 0
    for it in q["items"]:
        if it["done"] and not _it_claimed(it):
            it["claimed"] = True
            total += int(it["r"])
            n += 1
    if total:
        add_candies(user, total)
        save_db()
    return total, n


def claim_bonus(user: dict) -> int:
    """Pay today's all-quests bonus if it's ready. Returns the candies paid (0 if not ready)."""
    q = _roll_quests(user)
    if not _bonus_ready(q):
        return 0
    q["bonus"] = True
    add_candies(user, ALL_DONE_BONUS)
    save_db()
    return ALL_DONE_BONUS


def _haunt(db: dict, user: dict) -> dict:
    """Per-event haunt record: {'event': id, 'days': [dates]}."""
    eid = _state(db).get("event_id", 0)
    h = user.get("hw_haunt")
    if not isinstance(h, dict) or h.get("event") != eid:
        h = {"event": eid, "days": []}
        user["hw_haunt"] = h
    return h


def quest_progress(user_id, key: str, amount: int = 1, db: dict | None = None) -> None:
    """Add `amount` to today's quest `key` for this user (no-op if the event is off,
    the user doesn't have that quest today, or it's already done). Safe to call anywhere."""
    try:
        db = db or load_db()
        if not haunt_enabled(db, user_id) or amount <= 0:
            return
        uid = str(user_id)
        user = db.get("users", {}).get(uid)
        if not user:
            return
        q = _roll_quests(user)
        changed, notes = False, []
        for it in q["items"]:
            if it["k"] != key or it["done"]:
                continue
            it["p"] = min(it["t"], it["p"] + int(amount))
            changed = True
            if it["p"] >= it["t"]:
                it["done"] = True
                it["claimed"] = False                      # paid when the player taps Claim Reward in /haunt
                text = QUESTS[key][0].format(t=it["t"])
                notes.append(f"[ Quest complete ]: {_esc(text)}\n\n- {it['r']} candies {CANDY} are ready to claim !")
        if changed and sum(1 for i in q["items"] if i["done"]) >= HAUNT_DAY_MIN_QUESTS:
            h = _haunt(db, user)
            if q["date"] not in h["days"]:
                h["days"].append(q["date"])
                notes.append(f"[ Haunt day complete ]: {len(h['days'])}/{HAUNT_DAYS_REQUIRED} days")
        if changed and _bonus_ready(q):
            notes.append(f"[ All daily quests done ]\n\n- {ALL_DONE_BONUS} candies {CANDY} bonus is ready to claim !")
        if changed:
            save_db()
        if notes:
            _notify(uid, f"<b>「 {HW_EMOJI} HALLOWEEN QUEST 」\n━━━━━━━━━━━━━━━━━\n" + "\n\n".join(notes) + "</b>")
    except Exception as e:   # a quest bug must never break /roll, /seize, etc.
        print(f"[halloween] quest_progress error: {e}")


def assign_quests_all(db: dict) -> int:
    """Hand today's quests to EVERY player (skips banned). Returns how many got a new set."""
    n = 0
    for uid, u in db.get("users", {}).items():
        if not isinstance(u, dict):
            continue
        try:
            if is_ghost_banned(int(uid)) or is_shadow_banned(int(uid)):
                continue
        except ValueError:
            continue
        before = (u.get("hw_quests") or {}).get("date") if isinstance(u.get("hw_quests"), dict) else None
        _roll_quests(u)
        _haunt(db, u)
        if before != _today():
            n += 1
    if n:
        save_db()
    return n


_midnight_task = None


async def _midnight_loop():
    """Every 00:00 UTC: if haunt is on, assign the new day's quests to everyone."""
    while True:
        now = time.time()
        await asyncio.sleep(86400 - (now % 86400) + 3)
        try:
            db = load_db()
            if haunt_enabled(db):
                print(f"[halloween] midnight: assigned quests to {assign_quests_all(db)} player(s)")
        except Exception as e:
            print(f"[halloween] midnight assign error: {e}")


def ensure_midnight_task() -> None:
    global _midnight_task
    if _midnight_task and not _midnight_task.done():
        return
    try:
        _midnight_task = asyncio.get_running_loop().create_task(_midnight_loop())
    except RuntimeError:
        pass


@main_router.startup()
async def _hw_startup():
    ensure_midnight_task()
    try:
        db = load_db()
        if haunt_enabled(db):
            assign_quests_all(db)      # catch up after a restart
    except Exception as e:
        print(f"[halloween] startup assign error: {e}")


def _bar(p: int, t: int, width: int = 8) -> str:
    filled = 0 if t <= 0 else int(width * min(p, t) / t)
    return "▰" * filled + "▱" * (width - filled)


HW_HAUNT_IMAGE = "https://i.ibb.co/Xr5dWn7S/vol-2-haruo-design.jpg"


def _haunt_text(db: dict, user: dict, uid_int) -> str:
    """The /haunt card. Bold only (the whole text is one bold block)."""
    q = _roll_quests(user)
    dn = haunt_day(db)
    if not dn and not event_active(db) and user.get("hw_test"):
        dn = _tester_clock(user)[:2]
    head = f"「 {HW_EMOJI} HAUNT 」" + (f" —  Day [ {dn[0]}/{dn[1]} ]" if dn else "")
    lines = [head, "━━━━━━━━━━━━━━━━━"]
    for it in q["items"]:
        text = _esc(QUESTS[it["k"]][0].format(t=it["t"]))
        lines += [f"[QUEST] {text}",
                  f"[REWARD] —  {it['r']} {CANDY}",
                  f"[PROGRESS] {_bar(it['p'], it['t'])} {it['p']}/{it['t']}"]
        if it["done"]:
            lines.append("[STATUS] — Claimed ✅" if _it_claimed(it) else "[STATUS] — Ready to claim 🎁")
        lines.append("")
    done = sum(1 for i in q["items"] if i["done"])
    lines.append(f"[TODAY] : [ {done} / {len(q['items'])} ] Done")
    if q.get("bonus"):
        lines.append(f"[BONUS] : Claimed [{ALL_DONE_BONUS} Candy {CANDY}] ✅")
    elif _bonus_ready(q):
        lines.append(f"[BONUS] : Ready to claim [{ALL_DONE_BONUS} Candy {CANDY}] 🎁")
    else:
        lines.append(f"[BONUS] : Complete {len(q['items'])} Quest To get [{ALL_DONE_BONUS} Candy {CANDY}]")
    return "<b>" + "\n".join(lines) + "</b>"


def _haunt_kb(user: dict, owner: str, home: bool = False) -> InlineKeyboardMarkup:
    q = _roll_quests(user)
    rows = [[_btn(f"Open {HW_EMOJI} App", "primary", url=HW_MINIAPP_LINK)]]
    if any(not _it_claimed(i) for i in q["items"]):               # hidden once every reward is claimed
        rows.append([_btn("Claim Reward", "success", callback_data=f"hwq_reward_{owner}")])
    if _bonus_ready(q):
        rows.append([_btn("Claim Bonus", "success", callback_data=f"hwq_bonus_{owner}")])
    rows.append([_btn("Refresh", "primary", callback_data=f"hwq_refresh_{owner}")])
    if home:
        rows.append(_home_row(owner))
    return InlineKeyboardMarkup(inline_keyboard=rows)


@main_router.message(Command("haunt"))
async def haunt_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    ensure_midnight_task()
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    if not _ev_on(db, uid_int):
        await message.reply(f"{HW_EMOJI} The Halloween event isn't running right now.", parse_mode=ParseMode.HTML)
        return
    if not haunt_enabled(db, uid_int):
        await message.reply(f"🕯 <b>Haunt is switched off right now.</b> Quests are paused until an admin turns it on.",
                            parse_mode=ParseMode.HTML)
        return
    user = db["users"][user_id]
    _roll_quests(user)
    _haunt(db, user)
    save_db()
    await _reply_image(message, HW_HAUNT_IMAGE, _haunt_text(db, user, uid_int), _haunt_kb(user, user_id))


@main_router.callback_query(F.data.startswith("hwq_"))
async def hwq_cb(cq: CallbackQuery):
    _, kind, owner = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("Open your own quests with /haunt.", show_alert=True)
        return
    db = load_db()
    user = db.get("users", {}).get(owner)
    if not user or not _ev_on(db, owner) or not haunt_enabled(db, int(owner)):
        await cq.answer("Haunt isn't running right now.", show_alert=True)
        return
    if kind == "refresh":
        got, msg = 1, "Refreshed ✅"
        save_db()
    elif kind == "bonus":
        got = claim_bonus(user)
        msg = f"Bonus claimed! +{got} {CANDY}" if got else "No bonus to claim yet."
    else:
        got, n = claim_quest_rewards(user)
        msg = f"Claimed {n} quest reward(s): +{got} {CANDY}" if got else "Nothing to claim yet. Finish a quest first."
    await _edit_card(cq, _haunt_text(db, user, int(owner)), _haunt_kb(user, owner, _from_home(cq)))
    await cq.answer(msg, show_alert=not got)


# ==========================================
# THE 7-NIGHT LOGIN EVENT (ads -> shards / cards): /hwlogin shows it, halloween.html claims it
# ==========================================
def _gap(a: str, b: str) -> int:
    f = "%Y-%m-%d"
    return (datetime.strptime(b, f) - datetime.strptime(a, f)).days


def _login(db: dict, user: dict) -> dict:
    """Per-event login record: {'event': id, 'streak': nights claimed in a row, 'last': date}."""
    eid = _state(db).get("event_id", 0)
    h = user.get("hw_login")
    if not isinstance(h, dict) or h.get("event") != eid:
        h = {"event": eid, "streak": 0, "last": None}
        user["hw_login"] = h
    return h


def _login_view(db: dict, user: dict):
    """(nights claimed in the current run, can claim tonight?, streak just broke?, catch-up?)
    catch-up = exactly ONE night was missed: tonight completes the missed night AND tonight together."""
    h = _login(db, user)
    today, last, streak = _today(), h.get("last"), int(h.get("streak", 0))
    if streak >= len(LOGIN_EVENT):
        return streak, False, False, False      # finished all nights: nothing more to claim or watch this event
    broken = catchup = False
    if last and last != today:
        if streak > 0 and _gap(last, today) > 1:
            if _gap(last, today) == 2 and streak + 1 < len(LOGIN_EVENT):
                catchup = True                  # missed one night: claim it together with tonight
            else:
                streak, broken = 0, True        # missed more: back to night 1
    return streak, last != today, broken, catchup


def login_completed(db: dict, user: dict) -> bool:
    """True once the player has claimed all nights of the login event (no more ads / claims)."""
    return int(_login(db, user).get("streak", 0)) >= len(LOGIN_EVENT)


def _nights_due(streak: int, catchup: bool) -> tuple:
    """The LOGIN_EVENT nights that tonight's claim pays out (2 when catching up a missed night)."""
    return LOGIN_EVENT[streak:streak + (2 if catchup else 1)]


def _ads_needed(streak: int, catchup: bool) -> int:
    nights = _nights_due(streak, catchup)
    return sum(d["ads"] for d in nights) if nights else LOGIN_EVENT[-1]["ads"]


def _ads_today(user: dict) -> int:
    a = user.get("hw_login_ads")
    return int(a.get("n", 0)) if isinstance(a, dict) and a.get("date") == _today() else 0


def record_ad(db: dict, user: dict, uid=None) -> int:
    """Count one confirmed rewarded ad toward tonight's login reward. Called from the Adsgram
    reward postback only (never trust the client). Returns the ads counted tonight."""
    user["hw_ads_total"] = int(user.get("hw_ads_total", 0) or 0) + 1      # lifetime confirmed ads (/hwstats)
    d = user.get("hw_ads_day")
    if not isinstance(d, dict) or d.get("date") != _today():
        d = {"date": _today(), "n": 0}
    d["n"] += 1
    user["hw_ads_day"] = d
    save_db()
    if not login_enabled(db, uid):
        return 0
    streak, can, _broken, catchup = _login_view(db, user)
    if not can:
        return _ads_today(user)
    n = min(_ads_needed(streak, catchup), _ads_today(user) + 1)
    user["hw_login_ads"] = {"date": _today(), "n": n}
    save_db()
    return n


def _reward_text(day: dict) -> str:
    parts = []
    if day.get("shards"):
        parts.append(f"{day['shards']:,} Nexus Shards 💠")
    if day.get("card"):
        parts.append(f"1 random {day['card']} card")
    if day.get("hwcard"):
        parts.append(f"1 random Halloween {HW_EMOJI} card")
    return " + ".join(parts)


def claim_login(db: dict, user: dict, uid=None):
    """Claim tonight's reward once enough ads were counted. If exactly one night was missed,
    the missed night and tonight are paid together (ads of both nights are needed).
    Returns (ok, {'day','nights','catchup','shards','cards':[{'name','rarity'}]} | {'error'})."""
    if not (event_active(db) or user.get("hw_test")):
        return False, {"error": "The Halloween event isn't running right now."}
    if not login_enabled(db, uid):
        return False, {"error": "The login event is switched off right now."}
    if login_completed(db, user):
        return False, {"error": "You already completed all 7 nights. Nothing more to claim!"}
    streak, can, _broken, catchup = _login_view(db, user)
    if not can:
        return False, {"error": "Already claimed tonight — come back after 00:00 UTC."}
    nights = _nights_due(streak, catchup)
    if not nights:
        return False, {"error": "Nothing to claim right now."}
    need = _ads_needed(streak, catchup)
    seen = _ads_today(user)
    if seen < need:
        return False, {"error": f"Watch {need} ad(s) first ({seen}/{need})."}

    # Pick the cards BEFORE granting anything, so an empty pool never costs the player.
    picks = []
    for day in nights:
        if day.get("card"):
            picks.append(_pick_card(db, day["card"], halloween=False))
        if day.get("hwcard"):
            picks.append(_pick_card(db, day["hwcard"], halloween=True))
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
    h["streak"], h["last"] = streak + len(nights), _today()
    user["hw_login_ads"] = {"date": _today(), "n": 0}
    save_db()
    return True, {"day": streak + len(nights), "nights": [streak + 1 + i for i in range(len(nights))],
                  "catchup": bool(catchup), "shards": shards, "cards": cards}


def _login_text(db: dict, user: dict) -> str:
    """The /hwlogin card. Bold only (the whole text is one bold block)."""
    streak, can, broken, catchup = _login_view(db, user)
    total = len(LOGIN_EVENT)
    rows = []
    for i, d in enumerate(LOGIN_EVENT):
        mark = "Completed" if i < streak else "Incomplete"
        rows.append(f" - [{mark}] Night {i + 1} —  {_reward_text(d)}")
    if streak >= total:
        cur = f"[Current]: Night {total} (complete)"
    elif not can:
        cur = f"[Current]: Night {streak} (complete)"
    elif catchup:
        cur = f"[Current]: Nights {streak + 1} + {streak + 2} (incomplete)"
    else:
        cur = f"[Current]: Night {streak + 1} (incomplete)"
    lines = [f"「 {HW_EMOJI} 7-NIGHT LOGIN EVENT 」", "━━━━━━━━━━━━━━━━━"] + rows + ["", cur]
    if streak < total and can:
        need = _ads_needed(streak, catchup)
        lines.append(f"[Ads]: {min(_ads_today(user), need)}/{need} watched")
    if broken:
        lines += ["", "You missed a night, so the event restarted at night 1."]
    return "<b>" + "\n".join(lines) + "</b>"


HW_LOGIN_IMAGE = "https://i.ibb.co/V01FqSZY/4c2fb04e-70f1-44b2-a9b9-bccfbd3a22fb.jpg"   # same image as the leaderboard


@main_router.message(Command("hwlogin"))
async def hwlogin_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    if not _ev_on(db, uid_int):
        await message.reply(f"{HW_EMOJI} The Halloween event isn't running right now.", parse_mode=ParseMode.HTML)
        return
    if not login_enabled(db, uid_int):
        await message.reply("🌙 <b>The login event is switched off right now.</b> Check back later.",
                            parse_mode=ParseMode.HTML)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[[_btn(f"Halloween {HW_EMOJI}", "danger", url=HW_MINIAPP_LINK)]])
    await _reply_image(message, HW_LOGIN_IMAGE, _login_text(db, db["users"][user_id]), kb)


# ==========================================
# LEADERBOARD: /halloween_lbd (with the event image)
# ==========================================
HW_LBD_IMAGE = "https://i.ibb.co/V01FqSZY/4c2fb04e-70f1-44b2-a9b9-bccfbd3a22fb.jpg"
LBD_TOP = 10                     # rows shown per board
_lbd_file_id = None              # Telegram file_id cached after the first successful upload


def _ro_haunt_days(eid, u: dict) -> int:
    h = u.get("hw_haunt")
    return len(h.get("days", [])) if isinstance(h, dict) and h.get("event") == eid else 0


def _ro_login_nights(eid, u: dict) -> int:
    h = u.get("hw_login")
    return int(h.get("streak", 0) or 0) if isinstance(h, dict) and h.get("event") == eid else 0


# key -> (title, value fn(event_id, user), unit)
LBD_BOARDS = {
    "candies": (f"{CANDY} Top Candies",        lambda eid, u: _earned_of(u),                          CANDY),
    "given":   ("💝 Most Treats Given",        lambda eid, u: int(u.get("hw_treat_given", 0) or 0),   "treats"),
    "got":     ("🎁 Most Treats Received",     lambda eid, u: int(u.get("hw_treat_got", 0) or 0),     "treats"),
    "haunt":   ("🕯 Haunt Days",               _ro_haunt_days,                                        "days"),
    "login":   ("🌙 Login Nights",             _ro_login_nights,                                      "nights"),
}


def _uname(u: dict) -> str:
    n = u.get("name") or u.get("first_name") or u.get("username") or "Player"
    return _esc(str(n)[:18])


def _lbd_rows(db: dict, key: str) -> list:
    eid = _state(db).get("event_id", 0)
    fn = LBD_BOARDS[key][1]
    rows = []
    for uid, u in db.get("users", {}).items():
        if not isinstance(u, dict):
            continue
        try:
            if is_ghost_banned(int(uid)) or is_shadow_banned(int(uid)):
                continue
        except ValueError:
            continue
        if u.get("hw_test"):          # /hwtest testers are not ranked
            continue
        v = fn(eid, u)
        if v > 0:
            rows.append((uid, v, _uname(u)))
    rows.sort(key=lambda r: (-r[1], r[2].lower()))
    return rows


def _lbd_caption(db: dict, key: str, viewer_id: str) -> str:
    title, _fn, unit = LBD_BOARDS[key]
    rows = _lbd_rows(db, key)
    lines = [f"<b>「 {HW_EMOJI} HALLOWEEN LEADERBOARD 」</b>", f"<b>{title}</b>", "━━━━━━━━━━━━━━━━━"]
    if not rows:
        lines.append("<i>Nobody on the board yet.</i>")
    medals = ("🥇", "🥈", "🥉")
    for i, (uid, v, name) in enumerate(rows[:LBD_TOP]):
        lead = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{lead} {name} — <b>{v:,}</b> {unit}" + ("  ← you" if uid == viewer_id else ""))
    pos = next((i for i, r in enumerate(rows) if r[0] == viewer_id), None)
    if pos is None:
        lines.append("\n<i>You aren't ranked on this board yet.</i>")
    elif pos >= LBD_TOP:
        lines.append(f"…\n<b>#{pos + 1}</b> You — <b>{rows[pos][1]:,}</b> {unit}")
    if key == "candies":
        lines.append(f"\n<i>Ranked by candies earned all event (spending in the store doesn't lower your rank).</i>")
    return "\n".join(lines)


LBD_BTN_NAMES = {"candies": "Candies", "given": "Given", "got": "Received", "haunt": "Haunt", "login": "Login"}


def _lbd_kb(current: str, owner: str) -> InlineKeyboardMarkup:
    """3 rows, short names, no emojis. The open board is green, the others blue."""
    btns = [_btn(LBD_BTN_NAMES.get(k, k.title()), "success" if k == current else "primary",
                 callback_data=f"hwlb_{k}_{owner}")
            for k in LBD_BOARDS]
    return InlineKeyboardMarkup(inline_keyboard=[btns[0:2], btns[2:4], btns[4:]])


@main_router.message(Command("halloween_lbd", "hwlbd"))
async def halloween_lbd_cmd(message: Message):
    global _lbd_file_id
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        return
    owner = str(uid)
    db = load_db()
    cap, kb = _lbd_caption(db, "candies", owner), _lbd_kb("candies", owner)
    for src in [s for s in (_lbd_file_id, HW_LBD_IMAGE) if s]:
        try:
            sent = await message.reply_photo(photo=src, caption=cap, reply_markup=kb, parse_mode=ParseMode.HTML)
            if sent.photo and src == HW_LBD_IMAGE:
                _lbd_file_id = sent.photo[-1].file_id
            return
        except Exception as e:
            print(f"[halloween] leaderboard photo failed ({src[:30]}...): {e}")
            if src == _lbd_file_id:
                _lbd_file_id = None
    await message.reply(cap, reply_markup=kb, parse_mode=ParseMode.HTML)   # image unavailable: text only


@main_router.callback_query(F.data.startswith("hwlb_"))
async def hwlb_cb(cq: CallbackQuery):
    _, key, owner = cq.data.split("_", 2)
    if str(cq.from_user.id) != owner:
        await cq.answer("Open your own board with /halloween_lbd.", show_alert=True)
        return
    if key not in LBD_BOARDS:
        await cq.answer("Unknown board.", show_alert=True)
        return
    db = load_db()
    cap, kb = _lbd_caption(db, key, owner), _lbd_kb(key, owner)
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=cap, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(cap, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass   # "message is not modified"
    await cq.answer()


# ==========================================
# EVENT CONTROL HELPERS (used by /sthw)
# ==========================================
def _ev_start(db: dict, days: int, login: bool = True, haunt: bool = True):
    st, now = _state(db), time.time()
    day0 = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
    st["active"] = True
    st["event_id"] = int(now)                 # new id => everyone's haunt / login progress starts fresh
    st["start_date"] = day0.strftime("%Y-%m-%d")
    st["days"] = days
    st["login_on"], st["haunt_on"] = bool(login), bool(haunt)
    st["haunt_offset"] = 0
    st["paused_total"] = 0
    st["ends_at"] = (day0 + timedelta(days=days)).timestamp()   # end of the last UTC day
    st.pop("paused_at", None)
    save_db()
    return day0, (day0 + timedelta(days=days - 1)).strftime("%Y-%m-%d")


def _ev_pause(db: dict):
    st = _state(db)
    if not st.get("active"):
        return False, f"{HW_EMOJI} The event isn't running, nothing to pause."
    st["active"] = False
    st["paused_at"] = time.time()
    save_db()
    return True, ("⏸ <b>Event paused.</b> Quests, candies and the store are frozen and the remaining time is kept.\n"
                  "Use <code>/sthw on</code> to resume.")


def _ev_resume(db: dict):
    st, now = _state(db), time.time()
    if not st.get("paused_at"):
        return False, "The event isn't paused."
    dur = now - st.pop("paused_at")
    st["ends_at"] = st.get("ends_at", now) + dur
    st["paused_total"] = st.get("paused_total", 0) + dur
    st["active"] = True
    save_db()
    return True, "▶️ <b>Event resumed.</b>"


def _ev_stop(db: dict):
    st = _state(db)
    st["active"] = False
    st.pop("paused_at", None)
    save_db()
    return True, "⏹ Halloween event ended."


def _ev_extend(db: dict, n: int):
    st = _state(db)
    if not (st.get("paused_at") or event_active(db)):
        return False, "The event is over — start a new one with /sthw on."
    n = max(1, min(30, int(n)))
    st["ends_at"] = st.get("ends_at", time.time()) + n * 86400
    st["days"] = int(st.get("days", 0) or 0) + n
    save_db()
    return True, f"➕ Event extended by <b>{n}</b> day(s)."


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
        return False, ("⚠️ Can't remove that many days — the event would end right away.\n"
                       "Use <code>/sthw off</code> to end it now.")
    st["ends_at"] = new_end
    st["days"] = total - n
    save_db()
    return True, f"➖ Event shortened by <b>{n}</b> day(s)."


# ==========================================
# WEB API for halloween.html (FastAPI router, same style as /api/deck and /api/store)
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
    """Everything halloween.html needs to draw itself. The server is the source of truth,
    including store prices and limits."""
    lon, hon = login_enabled(db, uid), haunt_enabled(db, uid)
    q, h = (_roll_quests(user) if hon else None), _haunt(db, user)
    streak, can, broken, catchup = _login_view(db, user)
    need = _ads_needed(streak, catchup)
    dn, bought, active = event_day(db), user.get("hw_bought", {}), (event_active(db) or bool(user.get("hw_test")))
    left = event_seconds_left(db)
    if not left and user.get("hw_test"):          # no real event: the tester runs their own (starts at /hwtest on)
        td, tt, left = _tester_clock(user)
        dn = (td, tt)
    return {
        "event": {"active": active, "day": dn[0] if dn else 0, "total": dn[1] if dn else 0,
                  "seconds_left": left},
        "candies": candies_of(user),
        "shards": int(user.get("nexus_shards", 0) or 0),
        "features": {"login": lon, "haunt": hon},
        "login": {"streak": streak, "completed": streak >= len(LOGIN_EVENT), "can_claim": bool(can and lon), "broken": broken, "catchup": bool(catchup),
                  "ads_needed": need,
                  "ads_watched": min(_ads_today(user), need) if (can and lon) else 0},
        "quests": {"items": [{"k": i["k"], "text": QUESTS[i["k"]][0].format(t=i["t"]), "t": i["t"],
                              "p": i["p"], "r": i["r"], "done": i["done"], "claimed": _it_claimed(i)} for i in q["items"]] if q else [],
                   "bonus": bool(q and q["bonus"]), "bonus_ready": bool(q and _bonus_ready(q)),
                   "bonus_amount": ALL_DONE_BONUS},
        "haunt": {"days": len(h["days"]), "required": HAUNT_DAYS_REQUIRED, "today": bool(q and q["date"] in h["days"])},
        "store": [{"key": k, "price": v[1], "limit": v[2], "bought": bought.get(k, 0),
                   "locked": _store_gate(db, user, k)} for k, v in STORE_ITEMS.items()],
    }


def get_router(prefix: str = "/halloween"):
    """FastAPI router for halloween.html. Mount it once at startup:
           app.include_router(halloween.get_router(), prefix="/api")
       -> POST /api/halloween/state | /api/halloween/login | /api/halloween/buy
       Body: {"user_id": 123, "init_data": "<Telegram.WebApp.initData>", "key": "<store key (buy only)>"}
       Errors are HTTPException(detail=...), like the other mini-app endpoints."""
    from fastapi import APIRouter, HTTPException
    from pydantic import BaseModel

    class Req(BaseModel):
        user_id: int
        init_data: str = ""
        key: str = ""

    router = APIRouter(prefix=prefix, tags=["halloween"])

    def ctx(req: Req):
        if HW_REQUIRE_INITDATA:
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
        """Open <your-worker>/api/halloween/ping in a browser: {"ok": true} means the router is mounted."""
        return {"ok": True, "event_active": event_active(load_db())}

    @router.get("/ads/reward")
    async def ad_reward(userid: int = 0, secret: str = "", key: str = ""):
        """Adsgram reward postback: counts one confirmed ad toward tonight's login reward."""
        if HW_AD_SECRET and not hmac.compare_digest(secret or key, HW_AD_SECRET):
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
        save_db()                      # persists today's freshly rolled quests
        return {"ok": True, "view": view}

    @router.post("/login")
    async def login(req: Req):
        db, user = ctx(req)
        ok, info = claim_login(db, user, req.user_id)
        if not ok:
            raise HTTPException(400, info["error"])
        return {"ok": True, **info, "view": _web_view(db, user, req.user_id)}

    @router.post("/buy")
    async def buy(req: Req):
        db, user = ctx(req)
        err, res = _purchase(db, user, req.key)
        if err:
            raise HTTPException(400, err)
        return {"ok": True, "name": res["name"], "rarity": res["rarity"], "shards": res["shards"],
                "view": _web_view(db, user, req.user_id)}

    return router

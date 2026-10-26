import time
import random
import asyncio
import html
import uuid
from datetime import datetime, timezone
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery,
    InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto
)
from aiogram.filters import Command
from aiogram.enums import ParseMode, ButtonStyle
from aiogram.exceptions import TelegramBadRequest

from fastapi import APIRouter, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel

from config import (
    bot, main_router, ADMIN_IDS,
    format_rarity, load_db, save_db,
    ensure_user, get_mention,
    is_ghost_banned, is_shadow_banned,
    get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)
from char_stats import get_char_stats, STAT_FIELDS
from gcard import GCARD_REWARD_PER_GUESS
from halloween import quest_progress

# ==========================================
# CONSTANTS
# ==========================================
VERSUS_DAILY_CAP = 10    # legacy — no longer enforced; rewards are gated only by DAILY_MINIGAME_REWARD_CAP
ACCEPT_TIMEOUT   = 60    # seconds to accept challenge
DRAFT_TIMEOUT    = 300   # seconds per draft turn (5 min)

ROLES = [
    "Strength",
    "Mana",
    "Defence",
    "Agility",
    "Vitality",
    "Intelligence",
    "Luck",
]

ROLE_ICONS = {
    "Strength":     "💪",
    "Mana":         "🔮",
    "Defence":      "💢",
    "Agility":      "🚤",
    "Vitality":     "🐋",
    "Intelligence": "🎓",
    "Luck":         "☘️",
}

MODES        = ["Divine", "Elite", "Basic", "Mix"]
MODE_ICONS   = {"Divine": "❄️", "Elite": "⚓", "Basic": "🃏", "Mix": "🌀"}

# Display mode — where a match's live updates are shown.
# "chat"  : the Telegram chat board keeps getting edited every action,
#          same as today; the 🎮 webapp button is left off (nothing to see there).
# "web"   (default): all play happens in the Mini App. The chat message is edited ONCE
#          right after accept to a static "continue in the app" card and is
#          never touched again for per-turn actions (pull/skip/assign/ready/
#          draw offers) — only the final result/draw/timeout still posts, so
#          the group chat isn't left showing a stale "battle in progress" card
#          forever if nobody reopens the app.
DISPLAY_MODES  = ["chat", "web"]
DISPLAY_ICONS  = {"chat": "💬", "web": "🖥️"}
DISPLAY_LABELS = {"chat": "Chat Mode", "web": "Web Mode"}


def _display_of(state: dict) -> str:
    return state.get("display", "chat")


# Anyone polling /state who isn't one of the two duelists is a spectator.
# Spectators "time out" of the list if they stop polling for a while, so the
# webapp isn't stuck showing someone who closed the app minutes ago.
SPECTATOR_TTL = 45  # seconds


def _touch_spectator(state: dict, uid: int | None, name: str) -> None:
    if uid is None:
        return
    if uid in (state.get("challenger"), state.get("opponent")):
        return
    specs = state.setdefault("spectators", {})
    specs[uid] = {"name": (name or "Spectator").strip()[:32] or "Spectator", "ts": time.time()}


def _active_spectators(state: dict) -> list[dict]:
    specs = state.get("spectators", {})
    now = time.time()
    stale = [uid for uid, v in specs.items() if now - v.get("ts", 0) > SPECTATOR_TTL]
    for uid in stale:
        specs.pop(uid, None)
    return [{"uid": uid, "name": v["name"]} for uid, v in specs.items()]


# ==========================================
# LIVE REACTIONS (spectators + players can react/chat from the webapp)
# ==========================================
# Kept deliberately lightweight and read-only from the game's point of view:
# a reaction can never touch roster/turn/stage state, so nobody can be
# "hurt" competitively by what spectators post. Anti-spam is enforced with
# a per-user cooldown, a hard message-length cap, and a capped history so
# the list can never grow unbounded.
REACTION_COOLDOWN     = 2.5   # seconds between messages, per user
REACTION_MAX_LEN      = 60    # characters
REACTION_HISTORY_CAP  = 30    # max stored entries per match
REACTION_TTL          = 180   # seconds a reaction stays visible


def _add_reaction(state: dict, uid: int, name: str, text: str) -> dict:
    text = " ".join((text or "").split())[:REACTION_MAX_LEN]
    if not text:
        raise ValueError("Message can't be empty.")

    cooldowns = state.setdefault("reaction_cooldowns", {})
    now = time.time()
    last = cooldowns.get(uid, 0)
    if now - last < REACTION_COOLDOWN:
        raise PermissionError("Slow down — you're reacting too fast.")
    cooldowns[uid] = now

    entry = {"uid": uid, "name": (name or "Player").strip()[:24] or "Player", "text": text, "ts": now}
    feed = state.setdefault("reactions", [])
    feed.append(entry)
    if len(feed) > REACTION_HISTORY_CAP:
        del feed[: len(feed) - REACTION_HISTORY_CAP]
    return entry


def _active_reactions(state: dict) -> list[dict]:
    feed = state.get("reactions", [])
    now = time.time()
    feed[:] = [r for r in feed if now - r.get("ts", 0) <= REACTION_TTL]
    return feed

# In-memory state
active_versus: dict        = {}
active_versus_by_id: dict  = {}   # match_id (str) -> frozenset key, for webapp lookups
finished_versus: dict      = {}   # match_id (str) -> result snapshot, kept briefly after a match ends
_versus_daily: dict        = {}
_last_click: dict          = {}   # uid -> timestamp of last accepted Versus button click

CLICK_COOLDOWN = 2.0  # seconds — minimum gap between accepted button clicks per user
FINISHED_RETENTION = 180  # seconds a finished/drawn match's result stays fetchable by the webapp

# ==========================================
# WEB MINI APP (REAL-TIME VERSUS ARENA)
# ==========================================
# ⚠️ VERSUS_APP_SHORT_NAME must match the Mini App short name you configured
# for this bot in @BotFather (the same way "webmine" is configured for Mines).
VERSUS_BOT_USERNAME    = "Animenx_bot"
VERSUS_APP_SHORT_NAME  = "versus"

versus_router = APIRouter(prefix="/api/versus", tags=["Versus Web App"])


@versus_router.get("/image/{file_id}")
async def api_versus_image(file_id: str):
    """
    Proxies a Telegram card photo by file_id so the Mini App can use it as a
    plain <img>/background-image URL — the webapp can't hit api.telegram.org
    directly (that would need the bot token in the URL), so we stream the
    bytes through our own backend instead.
    """
    try:
        buf = await bot.download(file_id)
    except Exception:
        raise HTTPException(status_code=404, detail="Image unavailable.")
    return StreamingResponse(
        buf,
        media_type="image/jpeg",
        headers={"Cache-Control": "public, max-age=604800, immutable"}
    )


@versus_router.get("/avatar/{uid}")
async def api_versus_avatar(uid: int):
    """
    Streams a duelist's current Telegram profile photo so the Mini App can
    show a proper avatar next to their name instead of a placeholder.
    404s (no photo set, privacy-restricted, etc.) are expected — the
    frontend falls back to an initials badge in that case.
    """
    try:
        photos = await bot.get_user_profile_photos(uid, limit=1)
        if not photos.photos:
            raise HTTPException(status_code=404, detail="No avatar set.")
        file_id = photos.photos[0][-1].file_id
        buf = await bot.download(file_id)
    except HTTPException:
        raise
    except Exception:
        raise HTTPException(status_code=404, detail="Avatar unavailable.")
    return StreamingResponse(
        buf,
        media_type="image/jpeg",
        headers={"Cache-Control": "public, max-age=3600"}
    )


def _versus_webapp_button(match_id: str, text: str = "🎮 Open Battle Arena") -> InlineKeyboardButton:
    """
    A direct t.me link (not web_app=) so it works identically in group chats
    and DMs, and so anyone who taps it — including non-participants — can
    open the Mini App to spectate.
    """
    return InlineKeyboardButton(
        text=text,
        url=f"https://t.me/{VERSUS_BOT_USERNAME}/{VERSUS_APP_SHORT_NAME}?startapp=vs_{match_id}"
    )

_vsrule_last_use: dict = {}   # uid -> timestamp of last /vsrule command use
VSRULE_COOLDOWN = 5.0  # seconds — minimum gap between /vsrule uses per user


def _vsrule_command_allowed(uid: int) -> bool:
    """
    Rate-limits the /vsrule command per user to prevent spam.
    """
    now = time.time()
    last = _vsrule_last_use.get(uid, 0)
    if now - last < VSRULE_COOLDOWN:
        return False
    _vsrule_last_use[uid] = now
    return True


def _click_allowed(uid: int) -> bool:
    """
    Debounce rapid/duplicate button taps per user to avoid flooding Telegram
    with edit_message calls.
    """
    now = time.time()
    last = _last_click.get(uid, 0)
    if now - last < CLICK_COOLDOWN:
        return False
    _last_click[uid] = now
    return True


# ==========================================
# HELPERS
# ==========================================
def _today_key(uid: int) -> str:
    return f"{uid}_{datetime.now(timezone.utc).strftime('%Y-%m-%d')}"


def _state_key(uid_a: int, uid_b: int) -> frozenset:
    return frozenset({uid_a, uid_b})


def _delete_versus(key: frozenset) -> dict | None:
    """Removes a match from active_versus AND its match_id lookup entry. Always use this
    instead of `del active_versus[key]` so the webapp's match_id -> key mapping never leaks."""
    state = active_versus.pop(key, None)
    if state and state.get("match_id"):
        active_versus_by_id.pop(state["match_id"], None)
    return state


def _get_owned_cards(uid: int, db: dict) -> list:
    """All card_ids user owns with amount >= 1."""
    user_cards = db["users"].get(str(uid), {}).get("cards", {})
    return [cid for cid, cd in user_cards.items() if cd.get("amount", 0) >= 1]


# Field(s) on a global_cards entry that hold the card's anime/series name.
# The first one present wins -- edit this tuple if your DB uses another key.
CARD_ANIME_FIELDS = ("anime", "series", "anime_name", "franchise")
ANIME_PER_PAGE    = 12   # 3 rows x 4 numbered buttons
MIN_DRAFT_CARDS   = 8


def _card_anime(cdata: dict) -> str:
    """The anime/series a card belongs to ('' if the card has none)."""
    for f in CARD_ANIME_FIELDS:
        v = cdata.get(f)
        if v:
            return str(v).strip()
    return ""


def _anime_label(state: dict) -> str:
    return state.get("anime") or "All Anime"


def _anime_suffix(state: dict) -> str:
    return f" ({html.escape(state['anime'])})" if state.get("anime") else ""


def _anime_line(state: dict) -> str:
    """Extra line for the challenge text; empty when no anime is selected."""
    if not state.get("anime"):
        return ""
    return f"<b>⤷「 Anime: 🎬 {html.escape(state['anime'])} 」</b>\n"


def _mode_title(state: dict) -> str:
    """Board header text: 'Divine' or 'Divine · Solo Leveling'."""
    if state.get("anime"):
        return f"{state['mode']} · {html.escape(state['anime'])}"
    return state["mode"]


def _eligible_cards(uid: int, mode: str, db: dict, anime: str | None = None) -> list:
    """
    Owned cards that are usable in Versus. If `anime` is given, only cards
    from that anime are returned.
    """
    owned = _get_owned_cards(uid, db)
    eligible = []
    for cid in owned:
        cdata = db["global_cards"].get(cid, {})
        cs    = get_char_stats(cdata.get("name", ""))
        if not cs:
            continue
        if mode != "Mix" and cs.get("tier") != mode:
            continue
        if anime and _card_anime(cdata).lower() != anime.lower():
            continue
        eligible.append(cid)
    return eligible


def _anime_tier_counts(uid: int, db: dict) -> dict:
    """{anime: {"Divine": n, "Elite": n, "Basic": n, "Mix": total}} for this user's usable cards."""
    out: dict = {}
    for cid in _eligible_cards(uid, "Mix", db):
        cdata = db["global_cards"].get(cid, {})
        a = _card_anime(cdata)
        if not a:
            continue
        tier = (get_char_stats(cdata.get("name", "")) or {}).get("tier")
        d = out.setdefault(a, {"Divine": 0, "Elite": 0, "Basic": 0, "Mix": 0})
        d["Mix"] += 1
        if tier in d:
            d[tier] += 1
    return out


def _usable_modes(counts_a: dict, counts_b: dict, anime: str) -> list:
    """Rarities (in MODES order) where BOTH players have >= 8 cards of `anime`."""
    ca, cb = counts_a.get(anime, {}), counts_b.get(anime, {})
    return [m for m in MODES if ca.get(m, 0) >= MIN_DRAFT_CARDS and cb.get(m, 0) >= MIN_DRAFT_CARDS]


def _available_animes(uid_a: int, uid_b: int, db: dict) -> list:
    """Anime where both players can draft in at least one rarity."""
    ca, cb = _anime_tier_counts(uid_a, db), _anime_tier_counts(uid_b, db)
    return sorted((a for a in ca if _usable_modes(ca, cb, a)), key=str.lower)


def _best_mode(preferred: str, usable: list) -> str:
    """Keep `preferred` if usable, else the first usable rarity (Divine > Elite > Basic > Mix)."""
    return preferred if preferred in usable else usable[0]


def _pull_random_card(uid: int, mode: str, used: set, db: dict, anime: str | None = None) -> str | None:
    """Pull a random eligible card from user's deck excluding already-used ones."""
    eligible  = _eligible_cards(uid, mode, db, anime)
    available = [c for c in eligible if c not in used]
    return random.choice(available) if available else None


# ==========================================
# SHARED DRAFT MUTATIONS
# (used by BOTH the Telegram inline-keyboard callbacks and the webapp REST
#  API below, so the two interfaces can never drift out of sync — every
#  action mutates the exact same `state` dict regardless of where it came
#  from, and the in-chat board is refreshed afterwards either way.)
# ==========================================
def _apply_pull(state: dict, uid: int, db: dict) -> tuple[bool, str, str | None]:
    """Returns (ok, message, card_id)."""
    if state["stage"] != "drafting":
        return False, "Not in drafting stage.", None
    if state["draft_turn"] != uid:
        return False, "It's not your turn!", None
    if state.get("pending_card"):
        return False, "You already have a pulled card — assign or skip it first.", None

    uid_a      = state["challenger"]
    roster_key = "roster_a" if uid == uid_a else "roster_b"
    roster     = state[roster_key]
    used       = set(roster.values())
    mode       = state["mode"]

    card_id = _pull_random_card(uid, mode, used, db, state.get("anime"))
    if not card_id:
        return False, "No available cards left in your deck!", None

    state["expires"]      = time.time() + DRAFT_TIMEOUT
    state["pending_card"] = card_id
    cdata = db["global_cards"].get(card_id, {})
    return True, f"🎲 Pulled: {cdata.get('name','?')}!", card_id


def _apply_skip(state: dict, uid: int) -> tuple[bool, str]:
    if state["stage"] != "drafting":
        return False, "Not in drafting stage."
    if state["draft_turn"] != uid:
        return False, "It's not your turn!"
    if not state.get("pending_card"):
        return False, "No pulled card to skip."

    uid_a    = state["challenger"]
    skip_key = "skip_a" if uid == uid_a else "skip_b"
    skips_left = state.get(skip_key, 2)
    if skips_left <= 0:
        return False, "You have no skips remaining!"

    state[skip_key]        = skips_left - 1
    state["expires"]       = time.time() + DRAFT_TIMEOUT
    state["pending_card"]  = None
    return True, f"⏭️ Card skipped! {state[skip_key]} skips remaining."


def _apply_role_assign(state: dict, uid: int, card_id: str, role: str) -> tuple[bool, str, bool]:
    """Returns (ok, message, draft_complete)."""
    if role not in ROLES:
        return False, "Invalid role.", False
    if state["stage"] != "drafting":
        return False, "Not in drafting stage.", False
    if state["draft_turn"] != uid:
        return False, "It's not your turn!", False
    if state.get("pending_card") != card_id:
        return False, "This card has already been assigned. Pull a new card.", False

    uid_a      = state["challenger"]
    uid_b      = state["opponent"]
    roster_key = "roster_a" if uid == uid_a else "roster_b"
    roster     = state[roster_key]
    if role in roster:
        return False, "Role already taken. Pick another.", False

    roster[role]           = card_id
    state["pending_card"]  = None
    state["expires"]       = time.time() + DRAFT_TIMEOUT

    if len(state["roster_a"]) == len(ROLES) and len(state["roster_b"]) == len(ROLES):
        state["stage"]   = "ready_check"
        state["ready_a"] = False
        state["ready_b"] = False
        state["expires"] = time.time() + DRAFT_TIMEOUT
        return True, f"✅ {role} assigned!", True

    state["draft_turn"] = uid_b if uid == uid_a else uid_a
    return True, f"✅ {role} assigned!", False


def _apply_ready(state: dict, uid: int) -> tuple[bool, str, bool]:
    """Returns (ok, message, both_ready)."""
    if state["stage"] != "ready_check":
        return False, "Not in ready check stage.", False
    uid_a, uid_b = state["challenger"], state["opponent"]
    if uid == uid_a:
        if state.get("ready_a"):
            return False, "You are already ready!", False
        state["ready_a"] = True
    elif uid == uid_b:
        if state.get("ready_b"):
            return False, "You are already ready!", False
        state["ready_b"] = True
    else:
        return False, "You are not part of this battle.", False

    state["expires"] = time.time() + DRAFT_TIMEOUT
    return True, "✅ You are ready!", bool(state.get("ready_a") and state.get("ready_b"))


def _apply_draw_request(state: dict, uid: int) -> tuple[bool, str, bool]:
    """Returns (ok, message, both_offered)."""
    if state["stage"] != "drafting":
        return False, "Draw offers are only available during the draft.", False
    uid_a, uid_b = state["challenger"], state["opponent"]
    if uid != uid_a and uid != uid_b:
        return False, "You are not part of this battle.", False

    req_key = "draw_req_a" if uid == uid_a else "draw_req_b"
    if state.get(req_key):
        return False, "You've already offered a draw. Waiting for your opponent.", False

    state[req_key] = True
    return True, "🤝 Draw offer sent!", bool(state.get("draw_req_a") and state.get("draw_req_b"))


async def _safe_edit_photo_board(chat_id: int, msg_id: int, text: str, kb: InlineKeyboardMarkup | None = None, file_id: str = None) -> int:
    """
    Safely edits a board message. Never creates a new message.
    """
    MAX_RETRIES = 3
    RETRY_DELAY = 2.0

    for attempt in range(MAX_RETRIES):
        if file_id:
            try:
                await bot.edit_message_media(
                    chat_id=chat_id,
                    message_id=msg_id,
                    media=InputMediaPhoto(
                        media=file_id,
                        caption=text,
                        parse_mode=ParseMode.HTML,
                        has_spoiler=True,
                        show_caption_above_media=True
                    ),
                    reply_markup=kb
                )
                return msg_id
            except Exception:
                pass

        try:
            await bot.edit_message_caption(
                chat_id=chat_id,
                message_id=msg_id,
                caption=text,
                parse_mode=ParseMode.HTML,
                show_caption_above_media=True,
                reply_markup=kb
            )
            return msg_id
        except Exception:
            pass

        try:
            await bot.edit_message_text(
                text=text,
                chat_id=chat_id,
                message_id=msg_id,
                parse_mode=ParseMode.HTML,
                reply_markup=kb
            )
            return msg_id
        except Exception:
            pass

        if attempt < MAX_RETRIES - 1:
            await asyncio.sleep(RETRY_DELAY)

    return msg_id


# ==========================================
# BOARD BUILDER
# ==========================================
def _link(uid: int, name: str) -> str:
    """Telegram profile link safe from malformed HTML crashes."""
    return f'<a href="tg://user?id={uid}">{html.escape(name)}</a>'


async def _edit_pending_msg(cq: CallbackQuery, text: str, kb: InlineKeyboardMarkup) -> None:
    if cq.message.photo:
        await cq.message.edit_caption(caption=text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await cq.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


def _pending_kb(uid_a: int, uid_b: int, match_id: str = None, show_webapp: bool = False) -> InlineKeyboardMarkup:
    rows = [
        [
            InlineKeyboardButton(text="Accept", callback_data=f"vs_accept_{uid_a}_{uid_b}", style=ButtonStyle.SUCCESS),
            InlineKeyboardButton(text="Decline", callback_data=f"vs_decline_{uid_a}_{uid_b}", style=ButtonStyle.DANGER),
        ],
        [
            InlineKeyboardButton(text="⚙️ Settings", callback_data=f"vs_settings_{uid_a}_{uid_b}", style=ButtonStyle.PRIMARY),
        ]
    ]
    if match_id and show_webapp:
        rows.append([_versus_webapp_button(match_id, "🎮 View / Respond in App")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _settings_kb(uid_a: int, uid_b: int) -> InlineKeyboardMarkup:
    """Main settings menu:  [Mode][Rarity] / [Universe] / [Back & Save]"""
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="Mode",   callback_data=f"vs_submenu_mode_{uid_a}_{uid_b}",   style=ButtonStyle.PRIMARY),
            InlineKeyboardButton(text="Rarity", callback_data=f"vs_submenu_rarity_{uid_a}_{uid_b}", style=ButtonStyle.PRIMARY),
        ],
        [InlineKeyboardButton(text="Universe", callback_data=f"vs_animepick_0_{uid_a}_{uid_b}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="Back & Save", callback_data=f"vs_back_{uid_a}_{uid_b}")],
    ])


def _mode_kb(uid_a: int, uid_b: int, current_display: str) -> InlineKeyboardMarkup:
    row = [InlineKeyboardButton(
        text=DISPLAY_LABELS[d],
        callback_data=f"vs_setdisplay_{d}_{uid_a}_{uid_b}",
        style=ButtonStyle.SUCCESS if d == current_display else ButtonStyle.PRIMARY
    ) for d in DISPLAY_MODES]
    return InlineKeyboardMarkup(inline_keyboard=[
        row,
        [InlineKeyboardButton(text="Back", callback_data=f"vs_settings_{uid_a}_{uid_b}")],
    ])


def _rarity_kb(uid_a: int, uid_b: int, current_mode: str) -> InlineKeyboardMarkup:
    def btn(m):
        return InlineKeyboardButton(
            text=(f"{MODE_ICONS[m]} {m}" if m != "Mix" else m),
            callback_data=f"vs_setmatchmode_{m}_{uid_a}_{uid_b}",
            style=ButtonStyle.SUCCESS if m == current_mode else ButtonStyle.PRIMARY
        )
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("Divine"), btn("Elite")],
        [btn("Basic"), btn("Mix")],
        [InlineKeyboardButton(text="Back", callback_data=f"vs_settings_{uid_a}_{uid_b}")],
    ])


def _anime_picker_kb(uid_a: int, uid_b: int, options: list, page: int,
                     current_anime: str | None) -> InlineKeyboardMarkup:
    """Numbered buttons, 4 per row, then [All Anime], paging, Back."""
    pages = max(1, (len(options) + ANIME_PER_PAGE - 1) // ANIME_PER_PAGE)
    page  = max(0, min(page, pages - 1))
    start = page * ANIME_PER_PAGE
    rows, row = [], []
    for i, name in enumerate(options[start:start + ANIME_PER_PAGE], start=start):
        row.append(InlineKeyboardButton(
            text=str(i + 1),
            callback_data=f"vs_setanime_{i}_{uid_a}_{uid_b}",
            style=ButtonStyle.SUCCESS if (current_anime and name.lower() == current_anime.lower()) else ButtonStyle.PRIMARY
        ))
        if len(row) == 4:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([InlineKeyboardButton(
        text="All Anime",
        callback_data=f"vs_setanime_x_{uid_a}_{uid_b}",
        style=ButtonStyle.SUCCESS if not current_anime else ButtonStyle.PRIMARY
    )])
    if pages > 1:
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton(text="< Prev", callback_data=f"vs_animepick_{page - 1}_{uid_a}_{uid_b}"))
        nav.append(InlineKeyboardButton(text=f"{page + 1}/{pages}", callback_data=f"vs_animepick_{page}_{uid_a}_{uid_b}"))
        if page < pages - 1:
            nav.append(InlineKeyboardButton(text="Next >", callback_data=f"vs_animepick_{page + 1}_{uid_a}_{uid_b}"))
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="Back", callback_data=f"vs_settings_{uid_a}_{uid_b}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _web_mode_freeze_board(state: dict) -> tuple[str, InlineKeyboardMarkup]:
    """
    The one-time chat message shown for a Web Mode match right after accept.
    Nothing about it changes again during the draft/ready-check — the match
    plays out in the Mini App. Only the final result/draw/timeout still edits
    this message, so the chat isn't left showing "in progress" forever.
    """
    text = (
        f"<b>「  NEXUS  — {_mode_title(state)} Draft ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"⬤ <b>{_link(state['challenger'], state['name_a'])}</b>\n"
        f"⬤ <b>{_link(state['opponent'], state['name_b'])}</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"🖥️ <b>Web Mode</b> — this battle is being played in the app.\n"
        f"Tap below to open the Battle Arena."
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[_versus_webapp_button(state["match_id"])]])
    return text, kb


def _build_board(state: dict, db: dict,
                 stage_hint: str = "",
                 pulled_card_id: str = None) -> tuple[str, InlineKeyboardMarkup | None]:
    uid_a    = state["challenger"]
    uid_b    = state["opponent"]
    name_a   = state["name_a"]
    name_b   = state["name_b"]
    roster_a = state["roster_a"]
    roster_b = state["roster_b"]
    turn_uid = state["draft_turn"]
    mode     = state["mode"]

    status_line_a = " ~ READY" if state.get("ready_a") else ""
    status_line_b = " ~ READY" if state.get("ready_b") else ""

    link_a = f"{_link(uid_a, name_a)}{status_line_a}"
    link_b = f"{_link(uid_b, name_b)}{status_line_b}"

    def role_line(role: str, roster: dict) -> str:
        cid = roster.get(role)
        padded_role = f"{role:<16}"
        if not cid:
            return f"⦿  <b>{padded_role}</b> ➜  ○○○"
        cdata = db["global_cards"].get(cid, {})
        card_name = cdata.get('name', '?')
        rarity_formatted = format_rarity(cdata.get('rarity',''))
        return f"⦿  <b>{padded_role}</b> ➜  <b>{card_name}</b>  《 {rarity_formatted} 》"

    lines_a = "\n".join(role_line(r, roster_a) for r in ROLES)
    lines_b = "\n".join(role_line(r, roster_b) for r in ROLES)

    turn_link = _link(uid_a, name_a) if turn_uid == uid_a else _link(uid_b, name_b)

    pulled_line = ""
    if pulled_card_id:
        cdata = db["global_cards"].get(pulled_card_id, {})
        pulled_line = (
            f"\n\n🎲 <b>Pulled:</b> {cdata.get('name','?')}"
            f"  《 {format_rarity(cdata.get('rarity',''))} 》"
        )

    draw_req_line = ""
    if stage_hint == "pull":
        req_a = state.get("draw_req_a")
        req_b = state.get("draw_req_b")
        if req_a and not req_b:
            draw_req_line = f"\n\n🤝 <b>{name_a}</b> has offered a draw. Waiting for {name_b}…"
        elif req_b and not req_a:
            draw_req_line = f"\n\n🤝 <b>{name_b}</b> has offered a draw. Waiting for {name_a}…"

    text = (
        f"<b>「  NEXUS  — {_mode_title(state)} Draft ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"⬤ <b>{link_a}</b>\n"
        f"{lines_a}\n\n"
        f"⬤ <b>{link_b}</b>\n"
        f"{lines_b}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
    )

    if state["stage"] == "ready_check":
        text += "<b>⚔️ Both players must click Ready to begin!</b>"
    else:
        text += f"<b>Turn   ➜  {turn_link}</b>"

    text += pulled_line
    text += draw_req_line

    kb = None

    if stage_hint == "pull":
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="🎲 Pull Card",
                    callback_data=f"vs_pull_{turn_uid}",
                    style=ButtonStyle.PRIMARY
                ),
            ],
            [
                InlineKeyboardButton(
                    text="🤝 Let's Draw",
                    callback_data=f"vs_drawreq_{uid_a}_{uid_b}",
                    style=ButtonStyle.DANGER
                ),
            ],
        ])

    elif stage_hint == "role" and pulled_card_id:
        roster     = roster_a if turn_uid == uid_a else roster_b
        empty_roles = [r for r in ROLES if r not in roster]
        rows = []
        row  = []
        for role in empty_roles:
            icon = ROLE_ICONS[role]
            row.append(InlineKeyboardButton(
                text=f"{icon} {role}",
                callback_data=f"vs_role_{turn_uid}_{pulled_card_id}_{role}"
            ))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)

        skips_left = state.get("skip_a", 2) if turn_uid == uid_a else state.get("skip_b", 2)
        if skips_left > 0:
            rows.append([InlineKeyboardButton(
                text=f"⏭️ Skip Card ({skips_left} Left)",
                callback_data=f"vs_skip_{turn_uid}",
                style=ButtonStyle.DANGER
            )])

        kb = InlineKeyboardMarkup(inline_keyboard=rows)

    elif state["stage"] == "ready_check":
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(
                text="Ready",
                callback_data=f"vs_ready_{uid_a}_{uid_b}",
                style=ButtonStyle.SUCCESS
            )
        ]])

    match_id = state.get("match_id")
    if kb is not None and match_id and _display_of(state) == "web":
        kb.inline_keyboard.append([_versus_webapp_button(match_id)])

    return text, kb


# ==========================================
# BATTLE CALCULATION
# ==========================================
def resolve_battle(state: dict, db: dict) -> dict:
    uid_a    = state["challenger"]
    uid_b    = state["opponent"]
    roster_a = state["roster_a"]
    roster_b = state["roster_b"]

    def card_name(cid: str) -> str:
        return db["global_cards"].get(cid, {}).get("name", "")

    def stat_val(cid: str, field: str) -> int:
        cs = get_char_stats(card_name(cid))
        return cs.get(field, 0) if cs else 0

    score_a = score_b = 0
    clash_results = {}

    non_luck = [r for r in ROLES if r != "Luck"]
    for role in non_luck:
        cid_a = roster_a[role]
        cid_b = roster_b[role]
        va = stat_val(cid_a, role)
        vb = stat_val(cid_b, role)
        if   va > vb: winner = "a"
        elif vb > va: winner = "b"
        else:         winner = "draw"
        clash_results[role] = {"winner": winner, "value_a": va, "value_b": vb}
        if   winner == "a": score_a += 1
        elif winner == "b": score_b += 1
        else:                score_a += 0.5; score_b += 0.5

    luck_winner = random.choice(["a", "b"])
    clash_results["Luck"] = {
        "winner": luck_winner, "value_a": 0, "value_b": 0,
        "arrancar_side": luck_winner
    }
    if luck_winner == "a":
        score_a += 1
    else:
        score_b += 1

    overall_winner = uid_a if score_a > score_b else (uid_b if score_b > score_a else None)

    return {
        "clash_results": clash_results,
        "score_a": score_a, "score_b": score_b,
        "winner": overall_winner
    }


# ==========================================
# RESULT MESSAGE
# ==========================================
def _fmt_score(n) -> str:
    return str(int(n)) if float(n) == int(n) else str(n)


def build_result_text(state: dict, battle: dict, db: dict) -> str:
    uid_a    = state["challenger"]
    uid_b    = state["opponent"]
    name_a   = state["name_a"]
    name_b   = state["name_b"]
    roster_a = state["roster_a"]
    roster_b = state["roster_b"]
    cr       = battle["clash_results"]

    link_a = _link(uid_a, name_a)
    link_b = _link(uid_b, name_b)

    lines = [
        "<b>「 ⚡ NEXUS AWAKENING — RESULT ぁ 」</b>",
        "━━━━━━━━━━━━━━",
    ]

    for role in ROLES:
        res  = cr[role]
        icon = ROLE_ICONS[role]
        cd_a = db["global_cards"].get(roster_a[role], {})
        cd_b = db["global_cards"].get(roster_b[role], {})
        w    = res["winner"]

        note = ""
        if role == "Luck":
            side = name_a if w == "a" else name_b
            note = f" <i>(→ {side})</i>"

        if role == "Luck":
            if w == "a":
                winner_link = link_a
                body = f" <i><b>{cd_a.get('name','?')} was favored by fortune over {cd_b.get('name','?')}. (+1)</b></i>"
            elif w == "b":
                winner_link = link_b
                body = f" <i><b>{cd_b.get('name','?')} was favored by fortune over {cd_a.get('name','?')}. (+1)</b></i>"
            else:
                winner_link = "Draw"
                body = f" <i><b>{cd_a.get('name','?')} and {cd_b.get('name','?')} shared equal fortune.</b></i>"
        else:
            if w == "a":
                winner_link = link_a
                body = f" <i><b>{cd_a.get('name','?')} defeated {cd_b.get('name','?')}. (+1)</b></i>"
            elif w == "b":
                winner_link = link_b
                body = f" <i><b>{cd_b.get('name','?')} defeated {cd_a.get('name','?')}. (+1)</b></i>"
            else:
                winner_link = "Draw"
                body = f" <i><b>{cd_a.get('name','?')} and {cd_b.get('name','?')} fought to a draw.</b></i>"

        lines.append(f"{icon} <b>{role}</b> - {winner_link}{note}")
        lines.append(body)
        lines.append("")

    if lines[-1] == "":
        lines.pop()

    lines.append("━━━━━━━━━━━━━━")
    lines.append("📊 <b>Score</b>")

    winner_uid = battle["winner"]
    if winner_uid is None:
        lines.append(f" {link_a} — {_fmt_score(battle['score_a'])}")
        lines.append(f" {link_b} — {_fmt_score(battle['score_b'])}")
        lines.append("\n⚖️ <b>DRAW!</b>")
    else:
        if winner_uid == uid_a:
            lines.append(f" {link_a} — {_fmt_score(battle['score_a'])}  [ Winner ]")
            lines.append(f" {link_b} — {_fmt_score(battle['score_b'])}")
        else:
            lines.append(f" {link_a} — {_fmt_score(battle['score_a'])}")
            lines.append(f" {link_b} — {_fmt_score(battle['score_b'])}  [ Winner ]")

    return "\n".join(lines)


# ==========================================
# /versus COMMAND
# ==========================================
@main_router.message(Command("versus"))
async def versus_cmd(message: Message):
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid): return

    if not message.reply_to_message or not message.reply_to_message.from_user:
        await message.reply(
            "⚠️ <b>Usage:</b> Reply to a user's message to challenge them.\n"
            "<code>/versus</code>  (as a reply)",
            parse_mode=ParseMode.HTML
        )
        return

    target = message.reply_to_message.from_user
    if target.is_bot:
        await message.reply("You cannot challenge a bot.", parse_mode=ParseMode.HTML)
        return
    if target.id == uid:
        await message.reply("You cannot challenge yourself.", parse_mode=ParseMode.HTML)
        return

    for k, st in active_versus.items():
        if uid in k or target.id in k:
            await message.reply(
                "⚠️ One of you already has an active Versus. Finish it first.",
                parse_mode=ParseMode.HTML
            )
            return

    db = load_db()
    ensure_user(uid, message.from_user.full_name, message.from_user.username)
    ensure_user(target.id, target.full_name, target.username)

    saved_mode = db["users"].get(str(uid), {}).get("default_versus_mode", "Divine")
    if saved_mode not in MODES:
        saved_mode = "Divine"

    saved_display = db["users"].get(str(uid), {}).get("default_versus_display", "web")
    if saved_display not in DISPLAY_MODES:
        saved_display = "web"

    owned_a = _eligible_cards(uid, saved_mode, db)
    if len(owned_a) < 8:
        await message.reply(
            "You need at least 8 eligible cards in your deck to participate in Versus.",
            parse_mode=ParseMode.HTML
        )
        return

    name_a = get_mention(uid, message.from_user.full_name)
    name_b = get_mention(target.id, target.full_name)
    key    = _state_key(uid, target.id)
    match_id = uuid.uuid4().hex[:12]

    active_versus[key] = {
        "match_id":    match_id,
        "challenger":  uid,
        "opponent":    target.id,
        "name_a":      message.from_user.full_name,
        "name_b":      target.full_name,
        "chat_id":     message.chat.id,
        "msg_id":      None,
        "stage":       "pending",
        "mode":        saved_mode,
        "anime":       None,
        "anime_opts":  [],
        "display":     saved_display,
        "roster_a":    {},
        "roster_b":    {},
        "draft_turn":  uid,
        "score_a":     0,
        "score_b":     0,
        "ready_a":     False,
        "ready_b":     False,
        "skip_a":      2,
        "skip_b":      2,
        "draw_req_a":  False,
        "draw_req_b":  False,
        "expires":     time.time() + ACCEPT_TIMEOUT,
        "photo_board_active": False,
        "processing":  False,
        "pending_card": None,
        "start_time":  None,
        "spectators":  {},
    }
    active_versus_by_id[match_id] = key

    kb = _pending_kb(uid, target.id, match_id, show_webapp=(saved_display == "web"))

    pending_text = (
        f"<b>{name_a} has challenged {name_b} to a Card Battle!</b>\n\n"
        f"<b>⤷「 Mode: {MODE_ICONS[saved_mode]} {saved_mode} 」</b>\n"
        f"<b>⤷「 Display: {DISPLAY_ICONS[saved_display]} {DISPLAY_LABELS[saved_display]} 」</b>\n"
        f"━━━━━━━━━━━━━━━\n\n"
        f"<b><i>{name_b}, will you accept the challenge?</i></b>"
    )

    board_pic = db.get("settings", {}).get("pic_versus")
    if board_pic:
        msg = await message.reply_photo(
            photo=board_pic,
            caption=pending_text,
            parse_mode=ParseMode.HTML,
            reply_markup=kb
        )
        active_versus[key]["photo_board_active"] = True
    else:
        msg = await message.reply(
            pending_text,
            parse_mode=ParseMode.HTML,
            reply_markup=kb
        )
    active_versus[key]["msg_id"] = msg.message_id
    asyncio.create_task(_accept_timeout(key, msg.message_id, message.chat.id))


async def _accept_timeout(key: frozenset, msg_id: int, chat_id: int):
    await asyncio.sleep(ACCEPT_TIMEOUT)
    if key in active_versus and active_versus[key]["stage"] == "pending":
        state = active_versus[key]
        opponent_first_name = state["name_b"].split()[0] if state.get("name_b") else "they"
        _delete_versus(key)
        try:
            await _safe_edit_photo_board(
                chat_id=chat_id,
                msg_id=msg_id,
                text=(
                    "<b>「 ⏰ Versus Timeout 」</b>\n\n"
                    f"💢 Hmph... {opponent_first_name} didn't reply in time 😤 !!"
                ),
                kb=None
            )
        except Exception:
            pass


# ==========================================
# ACCEPT / DECLINE / SETTINGS CALLBACKS
# ==========================================
def _settings_summary(state: dict) -> str:
    display = _display_of(state)
    return (
        f"🎮 Mode: {DISPLAY_ICONS[display]} <b>{DISPLAY_LABELS[display]}</b>\n"
        f"💎 Rarity: {MODE_ICONS[state['mode']]} <b>{state['mode']}</b>\n"
        f"🌌 Universe: <b>{html.escape(_anime_label(state))}</b>"
    )


async def _show_settings(cq: CallbackQuery, state: dict, uid_a: int, uid_b: int, section: str = "main",
                         page: int = 0, options: list | None = None) -> None:
    """Render one of the settings screens (main / mode / rarity / universe)."""
    head = "<b>⚙️ Versus Match Settings</b>\n"
    if section == "mode":
        text = (head + "Choose where this match is played:\n\n" + _settings_summary(state) + "\n\n"
                "<i>Chat Mode plays out as board edits in this chat. Web Mode plays out "
                "entirely in the Battle Arena app — this chat message won't keep updating.</i>")
        kb = _mode_kb(uid_a, uid_b, _display_of(state))
    elif section == "rarity":
        text = head + "Choose the rarity to draft from:\n\n" + _settings_summary(state)
        kb = _rarity_kb(uid_a, uid_b, state["mode"])
    elif section == "universe":
        options = options or []
        start = page * ANIME_PER_PAGE
        lines = "\n".join(f"<b>{i + 1}.</b> {html.escape(n)}"
                          for i, n in enumerate(options[start:start + ANIME_PER_PAGE], start=start))
        text = (head + "🌌 <b>Universe</b> — only cards from the chosen anime will spawn.\n"
                f"Showing anime where <b>both players</b> have {MIN_DRAFT_CARDS}+ usable cards.\n\n"
                f"{lines}\n\nCurrent: <b>{html.escape(_anime_label(state))}</b>")
        kb = _anime_picker_kb(uid_a, uid_b, options, page, state.get("anime"))
    else:
        text = head + "Pick a setting to change:\n\n" + _settings_summary(state)
        kb = _settings_kb(uid_a, uid_b)
    await _edit_pending_msg(cq, text, kb)


async def _settings_guard(cq: CallbackQuery, uid_a: int, uid_b: int):
    """Shared checks for every settings callback. Returns state or None."""
    key = _state_key(uid_a, uid_b)
    if cq.from_user.id != uid_a:
        await cq.answer("⚠️ Only the challenger can change settings.", show_alert=True)
        return None
    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return None
    if key not in active_versus:
        await cq.answer("⚠️ Challenge has expired.", show_alert=True)
        return None
    state = active_versus[key]
    if state["stage"] != "pending":
        await cq.answer("⚠️ Challenge already in progress.", show_alert=True)
        return None
    return state


@main_router.callback_query(F.data.startswith("vs_settings_"))
async def vs_settings_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a, uid_b = int(parts[2]), int(parts[3])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return
    await _show_settings(cq, state, uid_a, uid_b, "main")
    await cq.answer()


@main_router.callback_query(F.data.startswith("vs_submenu_"))
async def vs_submenu_cb(cq: CallbackQuery):
    parts = cq.data.split("_")            # vs_submenu_<mode|rarity>_a_b
    section = parts[2]
    uid_a, uid_b = int(parts[3]), int(parts[4])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return
    if section not in ("mode", "rarity"):
        await cq.answer()
        return
    await _show_settings(cq, state, uid_a, uid_b, section)
    await cq.answer()


@main_router.callback_query(F.data.startswith("vs_animepick_"))
async def vs_animepick_cb(cq: CallbackQuery):
    parts = cq.data.split("_")            # vs_animepick_<page>_a_b
    page = int(parts[2])
    uid_a, uid_b = int(parts[3]), int(parts[4])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return
    db = load_db()
    options = _available_animes(uid_a, uid_b, db)
    state["anime_opts"] = options
    if not options:
        await cq.answer(
            f"⚠️ No anime where both of you have {MIN_DRAFT_CARDS}+ usable cards.",
            show_alert=True
        )
        return
    await _show_settings(cq, state, uid_a, uid_b, "universe", page=page, options=options)
    await cq.answer()


@main_router.callback_query(F.data.startswith("vs_setanime_"))
async def vs_setanime_cb(cq: CallbackQuery):
    parts = cq.data.split("_")            # vs_setanime_<idx|x>_a_b
    sel = parts[2]
    uid_a, uid_b = int(parts[3]), int(parts[4])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return

    note, alert = "Universe: All Anime", False
    if sel == "x":
        state["anime"] = None
    else:
        opts = state.get("anime_opts") or []
        try:
            chosen = opts[int(sel)]
        except (ValueError, IndexError):
            await cq.answer("⚠️ That list is out of date — reopen Universe.", show_alert=True)
            return
        db = load_db()
        ca, cb = _anime_tier_counts(uid_a, db), _anime_tier_counts(uid_b, db)
        usable = _usable_modes(ca, cb, chosen)
        if not usable:
            await cq.answer("⚠️ One of you no longer has enough cards for that anime.", show_alert=True)
            return
        old_mode = state["mode"]
        state["anime"] = chosen
        state["mode"] = _best_mode(old_mode, usable)
        note = f"Universe: {chosen}"
        if state["mode"] != old_mode:
            note = (f"Rarity switched to {MODE_ICONS[state['mode']]} {state['mode']} — "
                    f"not enough {old_mode} cards in {chosen}.")
            alert = True

    await _show_settings(cq, state, uid_a, uid_b, "main")
    await cq.answer(note, show_alert=alert)


@main_router.callback_query(F.data.startswith("vs_setmatchmode_"))
async def vs_setmatchmode_cb(cq: CallbackQuery):
    parts = cq.data.split("_")            # vs_setmatchmode_<rarity>_a_b
    mode = parts[2]
    uid_a, uid_b = int(parts[3]), int(parts[4])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return
    if mode not in MODES:
        await cq.answer("⚠️ Invalid rarity.", show_alert=True)
        return

    db = load_db()
    anime = state.get("anime")
    scope = f"{mode}" + (f" in {anime}" if anime else "")
    if len(_eligible_cards(uid_a, mode, db, anime)) < MIN_DRAFT_CARDS:
        await cq.answer(f"⚠️ You don't own {MIN_DRAFT_CARDS} eligible characters for {scope}.", show_alert=True)
        return
    if len(_eligible_cards(uid_b, mode, db, anime)) < MIN_DRAFT_CARDS:
        await cq.answer(f"⚠️ {state['name_b']} doesn't own {MIN_DRAFT_CARDS} eligible characters for {scope}.", show_alert=True)
        return

    state["mode"] = mode
    await _show_settings(cq, state, uid_a, uid_b, "rarity")
    await cq.answer(f"Rarity set to {mode}!")


@main_router.callback_query(F.data.startswith("vs_setdisplay_"))
async def vs_setdisplay_cb(cq: CallbackQuery):
    parts = cq.data.split("_")            # vs_setdisplay_<chat|web>_a_b
    display = parts[2]
    uid_a, uid_b = int(parts[3]), int(parts[4])
    state = await _settings_guard(cq, uid_a, uid_b)
    if state is None:
        return
    if display not in DISPLAY_MODES:
        await cq.answer("⚠️ Invalid display mode.", show_alert=True)
        return
    state["display"] = display
    await _show_settings(cq, state, uid_a, uid_b, "mode")
    await cq.answer(f"Mode set to {DISPLAY_LABELS[display]}!")


@main_router.callback_query(F.data.startswith("vs_back_"))
async def vs_back_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a = int(parts[2])
    uid_b = int(parts[3])
    key   = _state_key(uid_a, uid_b)

    if cq.from_user.id != uid_a:
        await cq.answer("⚠️ Only the challenger can change settings.", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    if key not in active_versus:
        await cq.answer("⚠️ Challenge has expired.", show_alert=True)
        return

    state = active_versus[key]
    if state["stage"] != "pending":
        await cq.answer("⚠️ Challenge already in progress.", show_alert=True)
        return

    name_a  = get_mention(uid_a, state["name_a"])
    name_b  = get_mention(uid_b, state["name_b"])
    mode    = state["mode"]
    display = _display_of(state)

    db = load_db()
    ensure_user(uid_a, state["name_a"])
    changed = False
    if db["users"].get(str(uid_a), {}).get("default_versus_mode") != mode:
        db["users"][str(uid_a)]["default_versus_mode"] = mode
        changed = True
    if db["users"].get(str(uid_a), {}).get("default_versus_display") != display:
        db["users"][str(uid_a)]["default_versus_display"] = display
        changed = True
    if changed:
        save_db()

    kb = _pending_kb(uid_a, uid_b, state.get("match_id"), show_webapp=(display == "web"))
    await _edit_pending_msg(
        cq,
        f"<b>{name_a} has challenged {name_b} to a Card Battle!</b>\n\n"
        f"「 Mode: {MODE_ICONS[mode]} {mode} 」\n"
        f"{_anime_line(state)}"
        f"「 Display: {DISPLAY_ICONS[display]} {DISPLAY_LABELS[display]} 」\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<b><i>{name_b}, will you accept the challenge?</i></b>",
        kb
    )
    await cq.answer("✅ Settings saved!")


@main_router.callback_query(F.data.startswith("vs_accept_"))
async def vs_accept_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a = int(parts[2])
    uid_b = int(parts[3])
    key   = _state_key(uid_a, uid_b)

    if cq.from_user.id != uid_b:
        await cq.answer("⚠️ This challenge isn't for you.", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    if key not in active_versus:
        await cq.answer("⚠️ Challenge has expired.", show_alert=True)
        return

    state = active_versus[key]
    if state["stage"] != "pending":
        await cq.answer("⚠️ Already in progress.", show_alert=True)
        return

    if state.get("processing"):
        await cq.answer("⏳ Processing acceptance...", show_alert=False)
        return
    state["processing"] = True

    try:
        db = load_db()

        owned_a_mode = _eligible_cards(uid_a, state["mode"], db, state.get("anime"))
        owned_b_mode = _eligible_cards(uid_b, state["mode"], db, state.get("anime"))
        if len(owned_a_mode) < 8:
            await cq.answer(
                f"⚠️ {state['name_a']} no longer owns 8 eligible characters for {state['mode']} mode{_anime_suffix(state)}.",
                show_alert=True
            )
            void_text = (
                f"<b>「 𝗔𝗡𝗜𝗠𝗘 𝗡𝗘𝗫𝗨𝗦 ぁ 」</b>\n"
                f"━━━━━━━━━━━━━━━\n"
                f"⚠️ <b>Challenge cancelled</b> — {state['name_a']} doesn't have 8 eligible "
                f"characters for {state['mode']} mode{_anime_suffix(state)}.\n"
                f"━━━━━━━━━━━━━━━"
            )
            try:
                await _safe_edit_photo_board(state["chat_id"], cq.message.message_id, void_text, kb=None)
            except Exception:
                pass
            _delete_versus(key)
            return
        if len(owned_b_mode) < 8:
            await cq.answer(
                f"⚠️ You don't own 8 eligible characters for {state['mode']} mode{_anime_suffix(state)}.",
                show_alert=True
            )
            void_text = (
                f"<b>「 𝗔𝗡𝗜𝗠𝗘 𝗡𝗘𝗫𝗨𝗦 ぁ 」</b>\n"
                f"━━━━━━━━━━━━━━━\n"
                f"⚠️ <b>Challenge cancelled</b> — {state['name_b']} doesn't have 8 eligible "
                f"characters for {state['mode']} mode{_anime_suffix(state)}.\n"
                f"━━━━━━━━━━━━━━━"
            )
            try:
                await _safe_edit_photo_board(state["chat_id"], cq.message.message_id, void_text, kb=None)
            except Exception:
                pass
            _delete_versus(key)
            return

        state["stage"]      = "drafting"
        state["expires"]    = time.time() + DRAFT_TIMEOUT
        state["start_time"] = time.time()

        if _display_of(state) == "web":
            text, kb = _web_mode_freeze_board(state)
        else:
            text, kb = _build_board(state, db, stage_hint="pull")
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], cq.message.message_id, text, kb)
        await cq.answer("✅ Challenge accepted! Draft begins.")
        asyncio.create_task(_draft_timeout_loop(key))
    finally:
        state["processing"] = False


@main_router.callback_query(F.data.startswith("vs_decline_"))
async def vs_decline_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a = int(parts[2])
    uid_b = int(parts[3])
    key   = _state_key(uid_a, uid_b)

    if cq.from_user.id != uid_b:
        await cq.answer("⚠️ This challenge isn't for you.", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    if key not in active_versus:
        await cq.answer("⚠️ Challenge has expired.", show_alert=True)
        return

    state = active_versus[key]
    if state.get("processing"):
        await cq.answer("⏳ Processing decline...", show_alert=False)
        return
    state["processing"] = True

    try:
        _delete_versus(key)
        if cq.message.photo:
            await cq.message.edit_caption(caption="<b>Challenge declined.</b>", parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text("<b>Challenge declined.</b>", parse_mode=ParseMode.HTML)
        await cq.answer()
    finally:
        state["processing"] = False


# ==========================================
# PULL CARD — random pick, send or update photo board
# ==========================================
@main_router.callback_query(F.data.startswith("vs_pull_"))
async def vs_pull_cb(cq: CallbackQuery):
    turn_uid = int(cq.data.split("_")[2])

    if cq.from_user.id != turn_uid:
        await cq.answer("⚠️ It's not your turn!", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    key = None
    for k, st in active_versus.items():
        if turn_uid in k and st["stage"] == "drafting":
            key = k
            break

    if not key:
        await cq.answer("⚠️ No active versus found.", show_alert=True)
        return

    state = active_versus[key]
    if state.get("processing"):
        await cq.answer("⏳ Processing card pull...", show_alert=False)
        return
    state["processing"] = True

    try:
        db = load_db()
        ok, msg, card_id = _apply_pull(state, turn_uid, db)
        if not ok:
            await cq.answer(msg, show_alert=True)
            return

        cdata = db["global_cards"].get(card_id, {})
        file_id = cdata.get("file_id")

        text, kb = _build_board(state, db, stage_hint="role", pulled_card_id=card_id)
        is_first_pull = not state.get("photo_board_active")

        if is_first_pull:
            if file_id:
                try:
                    sent = await bot.send_photo(
                        chat_id=state["chat_id"],
                        photo=file_id,
                        caption=text,
                        parse_mode=ParseMode.HTML,
                        has_spoiler=True,
                        show_caption_above_media=True,
                        reply_markup=kb
                    )
                    state["msg_id"] = sent.message_id
                    state["photo_board_active"] = True
                    try:
                        await cq.message.delete()
                    except Exception:
                        pass
                except Exception:
                    state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], cq.message.message_id, text, kb)
                    state["photo_board_active"] = False
            else:
                state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], cq.message.message_id, text, kb)
                state["photo_board_active"] = False
        else:
            state["msg_id"] = await _safe_edit_photo_board(
                chat_id=state["chat_id"],
                msg_id=state["msg_id"],
                text=text,
                kb=kb,
                file_id=file_id
            )

        await cq.answer(msg)
    finally:
        state["processing"] = False


# ==========================================
# SKIP CARD — ignore pull, allow a fresh pull
# ==========================================
@main_router.callback_query(F.data.startswith("vs_skip_"))
async def vs_skip_cb(cq: CallbackQuery):
    turn_uid = int(cq.data.split("_")[2])

    if cq.from_user.id != turn_uid:
        await cq.answer("⚠️ It's not your turn!", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    key = None
    for k, st in active_versus.items():
        if turn_uid in k and st["stage"] == "drafting":
            key = k
            break

    if not key:
        await cq.answer("⚠️ No active versus found.", show_alert=True)
        return

    state = active_versus[key]
    if state.get("processing"):
        await cq.answer("⏳ Processing card skip...", show_alert=False)
        return
    state["processing"] = True

    try:
        ok, msg = _apply_skip(state, turn_uid)
        if not ok:
            await cq.answer(msg, show_alert=True)
            return

        db = load_db()
        text, kb = _build_board(state, db, stage_hint="pull")
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb)

        await cq.answer(msg)
    finally:
        state["processing"] = False


# ==========================================
# DRAW REQUEST — both players must agree
# ==========================================
async def _finalize_mutual_draw(key: frozenset, chat_id: int, db: dict, msg_id: int):
    if key not in active_versus:
        return

    state = active_versus[key]
    uid_a = state["challenger"]
    uid_b = state["opponent"]

    vstats = db.setdefault("versus_stats", {
        "total_battles": 0,
        "completed_battles": 0,
        "cancelled_battles": 0,
        "total_shards_distributed": 0,
        "total_match_duration": 0,
        "match_duration_count": 0,
        "pvp_players": {}
    })

    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    daily_stats = db.setdefault("versus_daily_stats", {})
    if daily_stats.get("date") != today_str:
        daily_stats["date"] = today_str
        daily_stats["battles_today"] = 0
        daily_stats["shards_distributed_today"] = 0
        daily_stats["active_players"] = []
        daily_stats["player_battles_today"] = {}

    vstats["total_battles"] = vstats.get("total_battles", 0) + 1
    vstats["completed_battles"] = vstats.get("completed_battles", 0) + 1
    daily_stats["battles_today"] = daily_stats.get("battles_today", 0) + 1

    for u in [uid_a, uid_b]:
        daily_stats.setdefault("active_players", [])
        if u not in daily_stats["active_players"]:
            daily_stats["active_players"].append(u)
        daily_stats["player_battles_today"][str(u)] = daily_stats["player_battles_today"].get(str(u), 0) + 1
        p_record = vstats.setdefault("pvp_players", {}).setdefault(
            str(u), {"wins": 0, "losses": 0, "draws": 0, "streak": 0, "max_streak": 0}
        )
        p_record["draws"] = p_record.get("draws", 0) + 1
        p_record["streak"] = 0
        quest_progress(u, "versus_play", db=db)   # 🎃 quest

    save_db()

    uid_key_a = _today_key(uid_a)
    uid_key_b = _today_key(uid_b)
    _versus_daily[uid_key_a] = _versus_daily.get(uid_key_a, 0) + 1
    _versus_daily[uid_key_b] = _versus_daily.get(uid_key_b, 0) + 1

    final_text = (
        "<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"🤝 <b>{_link(uid_a, state['name_a'])}</b> and <b>{_link(uid_b, state['name_b'])}</b> "
        "agreed to a draw.\n"
        "━━━━━━━━━━━━━━━━━\n\n"
        "<b>「 𝗩𝗘𝗥𝗦𝗨𝗦 𝗥𝗘𝗪𝗔𝗥𝗗𝗦 」</b>\n"
        "⚖️ Match ended in a mutual draw! No rewards distributed."
    )
    await _safe_edit_photo_board(chat_id=chat_id, msg_id=msg_id, text=final_text, kb=None)

    if state.get("match_id"):
        finished_versus[state["match_id"]] = {
            "match_id":      state["match_id"],
            "uid_a":         uid_a, "uid_b": uid_b,
            "name_a":        state["name_a"], "name_b": state["name_b"],
            "mode":          state["mode"],
            "anime":         state.get("anime"),
            "display":       _display_of(state),
            "chat_id":       chat_id,
            "roster_a":      state["roster_a"], "roster_b": state["roster_b"],
            "score_a":       0, "score_b": 0,
            "winner_uid":    None,
            "clash_results": {},
            "reward_amount": 0,
            "mutual_draw":   True,
            "finished_at":   time.time(),
        }

    _delete_versus(key)


@main_router.callback_query(F.data.startswith("vs_drawreq_"))
async def vs_drawreq_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a = int(parts[2])
    uid_b = int(parts[3])
    key   = _state_key(uid_a, uid_b)

    clicker = cq.from_user.id
    if clicker != uid_a and clicker != uid_b:
        await cq.answer("⚠️ You are not part of this battle.", show_alert=True)
        return

    if not _click_allowed(clicker):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    if key not in active_versus:
        await cq.answer("⚠️ No active versus found.", show_alert=True)
        return

    state = active_versus[key]
    if state["stage"] != "drafting":
        await cq.answer("⚠️ Draw offers are only available during the draft.", show_alert=True)
        return

    if state.get("processing"):
        await cq.answer("⏳ Processing…", show_alert=False)
        return
    state["processing"] = True

    try:
        ok, msg, both_offered = _apply_draw_request(state, clicker)
        if not ok:
            await cq.answer(msg, show_alert=True)
            return
        await cq.answer(msg)

        if both_offered:
            db = load_db()
            await _finalize_mutual_draw(key, state["chat_id"], db, state["msg_id"])
            return

        db = load_db()
        text, kb = _build_board(state, db, stage_hint="pull")
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


# ==========================================
# ROLE PICK — assign pulled card to role, update board caption
# ==========================================
@main_router.callback_query(F.data.startswith("vs_role_"))
async def vs_role_pick_cb(cq: CallbackQuery):
    parts    = cq.data.split("_")
    turn_uid = int(parts[2])

    role    = parts[-1]
    card_id = "_".join(parts[3:-1])

    if cq.from_user.id != turn_uid:
        await cq.answer("⚠️ It's not your turn!", show_alert=True)
        return

    if role not in ROLES:
        await cq.answer("⚠️ Invalid role.", show_alert=True)
        return

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    key = None
    for k, st in active_versus.items():
        if turn_uid in k and st["stage"] == "drafting":
            key = k
            break

    if not key:
        await cq.answer("⚠️ No active versus found.", show_alert=True)
        return

    state = active_versus[key]
    if state.get("processing"):
        await cq.answer("⏳ Processing role assignment...", show_alert=False)
        return
    state["processing"] = True

    try:
        ok, msg, draft_complete = _apply_role_assign(state, turn_uid, card_id, role)
        if not ok:
            await cq.answer(msg, show_alert=True)
            return

        db = load_db()
        await cq.answer(msg)

        if draft_complete:
            text, kb = _build_board(state, db)
        else:
            text, kb = _build_board(state, db, stage_hint="pull")
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb)
    finally:
        state["processing"] = False


# ==========================================
# READY CHECK CALLBACK
# ==========================================
@main_router.callback_query(F.data.startswith("vs_ready_"))
async def vs_ready_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid_a = int(parts[2])
    uid_b = int(parts[3])
    key   = _state_key(uid_a, uid_b)

    if not _click_allowed(cq.from_user.id):
        await cq.answer("⏳ Slow down a bit!", show_alert=False)
        return

    if key not in active_versus:
        await cq.answer("⚠️ Challenge has expired.", show_alert=True)
        return

    state = active_versus[key]
    if state["stage"] != "ready_check":
        await cq.answer("⚠️ Not in ready check stage.", show_alert=True)
        return

    if state.get("processing"):
        await cq.answer("⏳ Processing readiness...", show_alert=False)
        return
    state["processing"] = True

    try:
        clicker = cq.from_user.id
        ok, msg, both_ready = _apply_ready(state, clicker)
        if not ok:
            await cq.answer(msg, show_alert=True)
            return
        await cq.answer(msg)

        db = load_db()
        if both_ready:
            await _finalize_battle(key, state["chat_id"], db, state["msg_id"])
            return

        text, kb = _build_board(state, db)
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb)
    finally:
        state["processing"] = False


# ==========================================
# DRAFT TIMEOUT LOOP
# ==========================================
async def _draft_timeout_loop(key: frozenset):
    while key in active_versus:
        await asyncio.sleep(10)
        if key not in active_versus:
            break
        state = active_versus[key]
        if state["stage"] not in ("drafting", "ready_check"):
            break
        if time.time() <= state["expires"]:
            continue

        chat_id = state["chat_id"]
        msg_id  = state["msg_id"]
        _delete_versus(key)

        db = load_db()
        vstats = db.setdefault("versus_stats", {})
        vstats["total_battles"] = vstats.get("total_battles", 0) + 1
        vstats["cancelled_battles"] = vstats.get("cancelled_battles", 0) + 1
        save_db()

        try:
            await _safe_edit_photo_board(
                chat_id=chat_id,
                msg_id=msg_id,
                text=(
                    f"<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"⏛ <b>Versus ended</b> — Match timed out.\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━"
                ),
                kb=None
            )
        except Exception:
            pass
        break


# ==========================================
# FINALIZE BATTLE & REWARDS
# ==========================================
async def _finalize_battle(key: frozenset, chat_id: int, db: dict, msg_id: int):
    if key not in active_versus:
        return

    state        = active_versus[key]
    state["stage"] = "battle"
    uid_a          = state["challenger"]
    uid_b          = state["opponent"]

    state["msg_id"] = await _safe_edit_photo_board(
        chat_id=chat_id,
        msg_id=msg_id,
        text=(
            "<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            "⚔️ <b>Draft complete! Calculating clash…</b>\n"
            "━━━━━━━━━━━━━━━━━"
        ),
        kb=None
    )

    await asyncio.sleep(1.5)

    MAX_FINALIZE_ATTEMPTS = 3
    RETRY_DELAY = 3.0

    battle = None
    result_text = None
    last_error = None

    for attempt in range(1, MAX_FINALIZE_ATTEMPTS + 1):
        try:
            fresh_db = load_db()
            battle = resolve_battle(state, fresh_db)
            result_text = build_result_text(state, battle, fresh_db)
            last_error = None
            break
        except Exception as e:
            last_error = e
            if attempt < MAX_FINALIZE_ATTEMPTS:
                try:
                    await _safe_edit_photo_board(
                        chat_id=chat_id,
                        msg_id=state["msg_id"],
                        text=(
                            "<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
                            "━━━━━━━━━━━━━━━━━\n"
                            "⚠️ <b>Hiccup calculating the result — retrying…</b>\n"
                            f"<i>Attempt {attempt}/{MAX_FINALIZE_ATTEMPTS}</i>\n"
                            "━━━━━━━━━━━━━━━━━"
                        ),
                        kb=None
                    )
                except Exception:
                    pass
                await asyncio.sleep(RETRY_DELAY)

    if last_error is not None:
        error_text = (
            "<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            "⚠️ <b>Match voided</b> — couldn't calculate a result after several tries.\n"
            f"<code>{last_error}</code>\n"
            "Please start a new Versus.\n"
            "━━━━━━━━━━━━━━━━━"
        )
        try:
            await _safe_edit_photo_board(chat_id=chat_id, msg_id=state["msg_id"], text=error_text, kb=None)
        except Exception:
            pass
        _delete_versus(key)
        return

    db = load_db()
    vstats = db.setdefault("versus_stats", {
        "total_battles": 0,
        "completed_battles": 0,
        "cancelled_battles": 0,
        "total_shards_distributed": 0,
        "total_match_duration": 0,
        "match_duration_count": 0,
        "pvp_players": {}
    })

    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    daily_stats = db.setdefault("versus_daily_stats", {})
    if daily_stats.get("date") != today_str:
        daily_stats["date"] = today_str
        daily_stats["battles_today"] = 0
        daily_stats["shards_distributed_today"] = 0
        daily_stats["active_players"] = []
        daily_stats["player_battles_today"] = {}

    vstats["total_battles"] = vstats.get("total_battles", 0) + 1
    vstats["completed_battles"] = vstats.get("completed_battles", 0) + 1
    daily_stats["battles_today"] = daily_stats.get("battles_today", 0) + 1

    if state.get("start_time"):
        match_dur = time.time() - state["start_time"]
        vstats["total_match_duration"] = vstats.get("total_match_duration", 0) + match_dur
        vstats["match_duration_count"] = vstats.get("match_duration_count", 0) + 1

    for u in [uid_a, uid_b]:
        daily_stats.setdefault("active_players", [])
        if u not in daily_stats["active_players"]:
            daily_stats["active_players"].append(u)
        daily_stats["player_battles_today"][str(u)] = daily_stats["player_battles_today"].get(str(u), 0) + 1
        vstats.setdefault("pvp_players", {}).setdefault(str(u), {"wins": 0, "losses": 0, "draws": 0, "streak": 0, "max_streak": 0})

    reward_msg = ""
    reward_amount = 0
    winner_uid = battle["winner"]

    if winner_uid:
        loser_uid = uid_b if winner_uid == uid_a else uid_a
        w_record = vstats["pvp_players"][str(winner_uid)]
        l_record = vstats["pvp_players"][str(loser_uid)]

        w_record["wins"] = w_record.get("wins", 0) + 1
        w_record["streak"] = w_record.get("streak", 0) + 1
        if w_record["streak"] > w_record.get("max_streak", 0):
            w_record["max_streak"] = w_record["streak"]

        l_record["losses"] = l_record.get("losses", 0) + 1
        l_record["streak"] = 0

        ensure_user(winner_uid, state["name_a"] if winner_uid == uid_a else state["name_b"])
        winner_data = db["users"][str(winner_uid)]
        v_rewards = get_daily_minigame_rewards(winner_data)

        current_rewarded_today = v_rewards.get("shards", 0)
        if current_rewarded_today < DAILY_MINIGAME_REWARD_CAP:
            reward_amount = min(150, DAILY_MINIGAME_REWARD_CAP - current_rewarded_today)
            winner_data["nexus_shards"] = winner_data.get("nexus_shards", 0) + reward_amount
            v_rewards["shards"] = current_rewarded_today + reward_amount

            vstats["total_shards_distributed"] = vstats.get("total_shards_distributed", 0) + reward_amount
            daily_stats["shards_distributed_today"] = daily_stats.get("shards_distributed_today", 0) + reward_amount

            reward_msg = (
                f"\n\n<b>「 𝗩𝗘𝗥𝗦𝗨𝗦 𝗥𝗘𝗪𝗔𝗥𝗗𝗦 」</b>\n"
                f"🏆 {_link(winner_uid, state['name_a'] if winner_uid == uid_a else state['name_b'])} won and received <b>+{reward_amount} 💠 Nexus Shards</b>!"
            )
            if v_rewards["shards"] >= DAILY_MINIGAME_REWARD_CAP:
                reward_msg += f"\n🎉 <i>You have reached your daily reward cap of {DAILY_MINIGAME_REWARD_CAP:,} 💠 shards (shared with Guess-the-Card)!</i>"
        else:
            reward_msg = (
                f"\n\n<b>「 𝗩𝗘𝗥𝗦𝗨𝗦 𝗥𝗘𝗪𝗔𝗥𝗗𝗦 」</b>\n"
                f"🏆 {_link(winner_uid, state['name_a'] if winner_uid == uid_a else state['name_b'])} won! "
                f"(No shards rewarded - daily cap reached)."
            )
    else:
        for u in [uid_a, uid_b]:
            p_record = vstats["pvp_players"][str(u)]
            p_record["draws"] = p_record.get("draws", 0) + 1
            p_record["streak"] = 0
        reward_msg = "\n\n<b>「 𝗩𝗘𝗥𝗦𝗨𝗦 𝗥𝗘𝗪𝗔𝗥𝗗𝗦 」</b>\n⚖️ Match ended in a draw! No rewards distributed."

    # 🎃 Halloween quests: both players played, the winner also won (+ shards paid)
    for _qu in (uid_a, uid_b):
        quest_progress(_qu, "versus_play", db=db)
    if winner_uid:
        quest_progress(winner_uid, "versus_win", db=db)
        if reward_amount:
            quest_progress(winner_uid, "shards", reward_amount, db=db)

    save_db()

    uid_key_a = _today_key(uid_a)
    uid_key_b = _today_key(uid_b)
    _versus_daily[uid_key_a] = _versus_daily.get(uid_key_a, 0) + 1
    _versus_daily[uid_key_b] = _versus_daily.get(uid_key_b, 0) + 1

    final_text = result_text + reward_msg
    if _display_of(state) == "web":
        # Web Mode: keep the offline chat clean — no scores/clash breakdown
        # posted there. The full result only ever shows inside the app.
        chat_final_text = (
            "<b>「 ⚡ NEXUS AWAKENING ぁ 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            "🏁 <b>Match complete.</b> Full results are in the Battle Arena app.\n"
            "━━━━━━━━━━━━━━━━━"
        )
        await _safe_edit_photo_board(chat_id=chat_id, msg_id=state["msg_id"], text=chat_final_text, kb=None)
    else:
        await _safe_edit_photo_board(chat_id=chat_id, msg_id=state["msg_id"], text=final_text, kb=None)

    # Stash a snapshot so the webapp can still show the result screen for a
    # short while after the match is gone from active_versus.
    if state.get("match_id"):
        finished_versus[state["match_id"]] = {
            "match_id":      state["match_id"],
            "uid_a":         uid_a, "uid_b": uid_b,
            "name_a":        state["name_a"], "name_b": state["name_b"],
            "mode":          state["mode"],
            "anime":         state.get("anime"),
            "display":       _display_of(state),
            "chat_id":       chat_id,
            "roster_a":      state["roster_a"], "roster_b": state["roster_b"],
            "score_a":       battle["score_a"], "score_b": battle["score_b"],
            "winner_uid":    winner_uid,
            "clash_results": battle["clash_results"],
            "reward_amount": reward_amount,
            "finished_at":   time.time(),
        }

    _delete_versus(key)


# ==========================================
# WEBAPP SYNC HELPER
# (keeps the Telegram chat board in sync whenever an action is driven by
#  the Mini App instead of an in-chat button tap)
# ==========================================
async def _sync_chat_board(state: dict, db: dict, stage_hint: str = "", pulled_card_id: str = None):
    if _display_of(state) == "web":
        return  # Web Mode: chat board is frozen after accept — nothing to sync per-turn.
    text, kb = _build_board(state, db, stage_hint=stage_hint, pulled_card_id=pulled_card_id)
    file_id = None
    if pulled_card_id:
        file_id = db["global_cards"].get(pulled_card_id, {}).get("file_id")
    try:
        state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb, file_id=file_id)
    except Exception:
        pass


# ==========================================
# WEBAPP JSON SERIALIZERS
# ==========================================
def _roster_out(roster: dict, db: dict) -> list:
    out = []
    for r in ROLES:
        cid = roster.get(r)
        if cid:
            cd = db["global_cards"].get(cid, {})
            out.append({
                "role": r, "icon": ROLE_ICONS[r], "filled": True,
                "card_id": cid,
                "name": cd.get("name", "?"),
                "rarity": format_rarity(cd.get("rarity", "")),
                "file_id": cd.get("file_id"),
            })
        else:
            out.append({"role": r, "icon": ROLE_ICONS[r], "filled": False})
    return out


def _viewer_role(state_or_snapshot: dict, viewer_uid: int | None) -> str:
    if viewer_uid == state_or_snapshot.get("challenger", state_or_snapshot.get("uid_a")):
        return "challenger"
    if viewer_uid == state_or_snapshot.get("opponent", state_or_snapshot.get("uid_b")):
        return "opponent"
    return "spectator"


def _serialize_state(state: dict, db: dict, viewer_uid: int | None) -> dict:
    uid_a, uid_b = state["challenger"], state["opponent"]
    role = _viewer_role(state, viewer_uid)
    turn_uid = state.get("draft_turn")

    pulled_card_out = None
    pulled_cid = state.get("pending_card")
    if pulled_cid:
        # Visible to everyone (the active drafter, the opponent, and any
        # spectator) so the pull feels shared/live — only the drafter gets
        # the assign/skip controls, gated client-side on `your_turn`.
        cd = db["global_cards"].get(pulled_cid, {})
        drafter_is_a = (turn_uid == uid_a)
        pulled_card_out = {
            "card_id": pulled_cid,
            "name": cd.get("name", "?"),
            "rarity": format_rarity(cd.get("rarity", "")),
            "file_id": cd.get("file_id"),
            "skip_left": state.get("skip_a" if drafter_is_a else "skip_b", 2),
            "taken_roles": [r for r in ROLES if r in (state["roster_a"] if drafter_is_a else state["roster_b"])],
        }

    return {
        "match_id":   state["match_id"],
        "stage":      state["stage"],
        "mode":       state["mode"],
        "anime":      state.get("anime"),
        "display":    _display_of(state),
        "role":       role,
        "viewer_uid": viewer_uid,
        "player_a": {
            "uid": uid_a, "name": state["name_a"], "ready": state.get("ready_a", False),
            "skip_left": state.get("skip_a", 2), "roster": _roster_out(state["roster_a"], db),
        },
        "player_b": {
            "uid": uid_b, "name": state["name_b"], "ready": state.get("ready_b", False),
            "skip_left": state.get("skip_b", 2), "roster": _roster_out(state["roster_b"], db),
        },
        "turn_uid": turn_uid,
        "your_turn": bool(state["stage"] == "drafting" and viewer_uid == turn_uid),
        "pulled_card": pulled_card_out,
        "opponent_is_choosing": bool(pulled_cid) and viewer_uid != turn_uid,
        "draw_offered_by_you":        (viewer_uid == uid_a and state.get("draw_req_a")) or (viewer_uid == uid_b and state.get("draw_req_b")),
        "draw_offered_by_opponent":   (viewer_uid == uid_a and state.get("draw_req_b")) or (viewer_uid == uid_b and state.get("draw_req_a")),
        "expires_at": state.get("expires"),
        "spectators": _active_spectators(state),
        "reactions": _active_reactions(state),
    }


def _serialize_finished(snap: dict, db: dict, viewer_uid: int | None) -> dict:
    role = _viewer_role(snap, viewer_uid)
    return {
        "match_id": snap["match_id"],
        "stage": "draw" if snap.get("mutual_draw") else "result",
        "mode": snap["mode"],
        "anime": snap.get("anime"),
        "display": snap.get("display", "chat"),
        "role": role,
        "player_a": {"uid": snap["uid_a"], "name": snap["name_a"], "roster": _roster_out(snap["roster_a"], db)},
        "player_b": {"uid": snap["uid_b"], "name": snap["name_b"], "roster": _roster_out(snap["roster_b"], db)},
        "score_a": snap["score_a"], "score_b": snap["score_b"],
        "winner_uid": snap["winner_uid"],
        "clash_results": snap["clash_results"],
        "reward_amount": snap["reward_amount"],
        "expires_at": None,
        "spectators": [],
        "reactions": [],
        "can_rematch": role in ("challenger", "opponent"),
        "rematch_of": snap["match_id"],
    }


def _get_state_by_match(match_id: str) -> tuple[frozenset, dict]:
    key = active_versus_by_id.get(match_id)
    if key is None or key not in active_versus:
        raise HTTPException(status_code=404, detail="Match not found or already ended.")
    return key, active_versus[key]


def _parse_uid(user_id: str) -> int | None:
    try:
        return int(user_id)
    except (TypeError, ValueError):
        return None


# ==========================================
# WEBAPP REST API SCHEMAS
# ==========================================
class VersusActionReq(BaseModel):
    user_id: str
    match_id: str

class VersusRoleReq(BaseModel):
    user_id: str
    match_id: str
    card_id: str
    role: str

class VersusModeReq(BaseModel):
    user_id: str
    match_id: str
    mode: str

class VersusReactReq(BaseModel):
    user_id: str
    match_id: str
    name: str = ""
    text: str


# ==========================================
# WEBAPP REST API ENDPOINTS
# ==========================================
@versus_router.get("/state/{match_id}")
async def api_versus_state(match_id: str, user_id: str = "", name: str = ""):
    db = load_db()
    viewer_uid = _parse_uid(user_id)

    if match_id not in active_versus_by_id:
        snap = finished_versus.get(match_id)
        if snap:
            if time.time() - snap["finished_at"] > FINISHED_RETENTION:
                finished_versus.pop(match_id, None)
                raise HTTPException(status_code=404, detail="Match has ended.")
            return _serialize_finished(snap, db, viewer_uid)
        raise HTTPException(status_code=404, detail="Match not found.")

    key, state = _get_state_by_match(match_id)
    _touch_spectator(state, viewer_uid, name)
    return _serialize_state(state, db, viewer_uid)


@versus_router.get("/active")
async def api_versus_active():
    """Lobby list of currently live matches anyone can tap into to spectate."""
    out = []
    for state in active_versus.values():
        if state["stage"] in ("drafting", "ready_check") and state.get("match_id") and _display_of(state) == "web":
            out.append({
                "match_id": state["match_id"],
                "name_a": state["name_a"], "name_b": state["name_b"],
                "mode": state["mode"], "anime": state.get("anime"), "stage": state["stage"],
            })
    return {"matches": out}


@versus_router.post("/accept")
async def api_versus_accept(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if uid != state["opponent"]:
        raise HTTPException(status_code=403, detail="This challenge isn't for you.")
    if state["stage"] != "pending":
        raise HTTPException(status_code=400, detail="Challenge already in progress.")
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        db = load_db()
        uid_a, uid_b = state["challenger"], state["opponent"]
        if len(_eligible_cards(uid_a, state["mode"], db, state.get("anime"))) < 8:
            _delete_versus(key)
            try:
                await _safe_edit_photo_board(
                    state["chat_id"], state["msg_id"],
                    f"⚠️ <b>Challenge cancelled</b> — {state['name_a']} doesn't have 8 eligible characters for {state['mode']} mode{_anime_suffix(state)}.",
                    kb=None
                )
            except Exception:
                pass
            raise HTTPException(status_code=400, detail=f"{state['name_a']} no longer owns 8 eligible characters for this mode.")
        if len(_eligible_cards(uid_b, state["mode"], db, state.get("anime"))) < 8:
            _delete_versus(key)
            try:
                await _safe_edit_photo_board(
                    state["chat_id"], state["msg_id"],
                    f"⚠️ <b>Challenge cancelled</b> — {state['name_b']} doesn't have 8 eligible characters for {state['mode']} mode{_anime_suffix(state)}.",
                    kb=None
                )
            except Exception:
                pass
            raise HTTPException(status_code=400, detail="You don't own 8 eligible characters for this mode.")

        state["stage"]      = "drafting"
        state["expires"]    = time.time() + DRAFT_TIMEOUT
        state["start_time"] = time.time()
        if _display_of(state) == "web":
            text, kb = _web_mode_freeze_board(state)
            try:
                state["msg_id"] = await _safe_edit_photo_board(state["chat_id"], state["msg_id"], text, kb)
            except Exception:
                pass
        else:
            await _sync_chat_board(state, db, stage_hint="pull")
        asyncio.create_task(_draft_timeout_loop(key))
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/decline")
async def api_versus_decline(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if uid != state["opponent"]:
        raise HTTPException(status_code=403, detail="This challenge isn't for you.")

    chat_id, msg_id, photo_active = state["chat_id"], state["msg_id"], state.get("photo_board_active")
    _delete_versus(key)
    try:
        if photo_active:
            await bot.edit_message_caption(chat_id=chat_id, message_id=msg_id, caption="<b>Challenge declined.</b>", parse_mode=ParseMode.HTML)
        else:
            await bot.edit_message_text(chat_id=chat_id, message_id=msg_id, text="<b>Challenge declined.</b>", parse_mode=ParseMode.HTML)
    except Exception:
        pass
    return {"ok": True}


@versus_router.post("/react")
async def api_versus_react(req: VersusReactReq):
    """
    Lightweight live reaction/chat feed for the webapp. Open to both
    duelists and spectators. This never mutates match/game state (roster,
    turn, stage, rewards) — it only appends to a capped, self-expiring
    feed — so it cannot affect the outcome of a match either player is in.
    """
    uid = _parse_uid(req.user_id)
    if uid is None:
        raise HTTPException(status_code=400, detail="Invalid user.")
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        raise HTTPException(status_code=403, detail="You can't do that right now.")

    key, state = _get_state_by_match(req.match_id)
    if state["stage"] not in ("pending", "drafting", "ready_check"):
        raise HTTPException(status_code=400, detail="This match isn't accepting messages anymore.")

    name = req.name or ("Player" if uid in (state["challenger"], state["opponent"]) else "Spectator")
    try:
        _add_reaction(state, uid, name, req.text)
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))
    except PermissionError as e:
        raise HTTPException(status_code=429, detail=str(e))

    db = load_db()
    return _serialize_state(state, db, uid)


@versus_router.post("/mode")
async def api_versus_mode(req: VersusModeReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if uid != state["challenger"]:
        raise HTTPException(status_code=403, detail="Only the challenger can change settings.")
    if state["stage"] != "pending":
        raise HTTPException(status_code=400, detail="Challenge already in progress.")
    if _display_of(state) == "web":
        raise HTTPException(
            status_code=400,
            detail="For Web Mode matches, the tier can only be changed from the ⚙️ Settings button in chat."
        )
    if req.mode not in MODES:
        raise HTTPException(status_code=400, detail="Invalid mode.")

    db = load_db()
    if len(_eligible_cards(uid, req.mode, db, state.get("anime"))) < 8:
        raise HTTPException(status_code=400, detail=f"You don't own 8 eligible characters for {req.mode} mode.")
    if len(_eligible_cards(state["opponent"], req.mode, db, state.get("anime"))) < 8:
        raise HTTPException(status_code=400, detail=f"{state['name_b']} doesn't own 8 eligible characters for {req.mode} mode.")

    state["mode"] = req.mode
    ensure_user(uid, state["name_a"])
    db["users"][str(uid)]["default_versus_mode"] = req.mode
    save_db()

    name_a = get_mention(state["challenger"], state["name_a"])
    name_b = get_mention(state["opponent"], state["name_b"])
    text = (
        f"<b>{name_a} has challenged {name_b} to a Card Battle!</b>\n\n"
        f"「 Mode: {MODE_ICONS[req.mode]} {req.mode} 」\n"
        f"{_anime_line(state)}"
        f"「 Display: {DISPLAY_ICONS[_display_of(state)]} {DISPLAY_LABELS[_display_of(state)]} 」\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<b><i>{name_b}, will you accept the challenge?</i></b>"
    )
    kb = _pending_kb(state["challenger"], state["opponent"], state["match_id"], show_webapp=(_display_of(state) == "web"))
    try:
        if state.get("photo_board_active"):
            await bot.edit_message_caption(chat_id=state["chat_id"], message_id=state["msg_id"], caption=text, parse_mode=ParseMode.HTML, reply_markup=kb)
        else:
            await bot.edit_message_text(chat_id=state["chat_id"], message_id=state["msg_id"], text=text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception:
        pass
    return _serialize_state(state, db, uid)


@versus_router.post("/pull")
async def api_versus_pull(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        db = load_db()
        ok, msg, card_id = _apply_pull(state, uid, db)
        if not ok:
            raise HTTPException(status_code=400, detail=msg)
        await _sync_chat_board(state, db, stage_hint="role", pulled_card_id=card_id)
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/skip")
async def api_versus_skip(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        ok, msg = _apply_skip(state, uid)
        if not ok:
            raise HTTPException(status_code=400, detail=msg)
        db = load_db()
        await _sync_chat_board(state, db, stage_hint="pull")
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/assign")
async def api_versus_assign(req: VersusRoleReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        ok, msg, draft_complete = _apply_role_assign(state, uid, req.card_id, req.role)
        if not ok:
            raise HTTPException(status_code=400, detail=msg)
        db = load_db()
        if draft_complete:
            await _sync_chat_board(state, db)
        else:
            await _sync_chat_board(state, db, stage_hint="pull")
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/ready")
async def api_versus_ready(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        ok, msg, both_ready = _apply_ready(state, uid)
        if not ok:
            raise HTTPException(status_code=400, detail=msg)
        db = load_db()
        if both_ready:
            await _finalize_battle(key, state["chat_id"], db, state["msg_id"])
            snap = finished_versus.get(req.match_id)
            return _serialize_finished(snap, db, uid) if snap else {"ok": True, "stage": "result"}
        await _sync_chat_board(state, db)
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/draw_request")
async def api_versus_draw_request(req: VersusActionReq):
    key, state = _get_state_by_match(req.match_id)
    uid = _parse_uid(req.user_id)
    if state.get("processing"):
        raise HTTPException(status_code=409, detail="Processing — try again shortly.")
    state["processing"] = True
    try:
        ok, msg, both_offered = _apply_draw_request(state, uid)
        if not ok:
            raise HTTPException(status_code=400, detail=msg)
        db = load_db()
        if both_offered:
            await _finalize_mutual_draw(key, state["chat_id"], db, state["msg_id"])
            snap = finished_versus.get(req.match_id)
            return _serialize_finished(snap, db, uid) if snap else {"ok": True, "stage": "draw"}
        await _sync_chat_board(state, db, stage_hint="pull")
        return _serialize_state(state, db, uid)
    finally:
        if key in active_versus:
            active_versus[key]["processing"] = False


@versus_router.post("/rematch")
async def api_versus_rematch(req: VersusActionReq):
    """
    Lets either duelist from a just-finished match immediately re-challenge
    the same opponent with the same mode/display, without leaving the app.
    The opponent still needs to tap Accept — this only saves both players
    re-typing /versus in chat.
    """
    snap = finished_versus.get(req.match_id)
    if not snap:
        raise HTTPException(status_code=404, detail="That match is no longer available for a rematch.")

    uid = _parse_uid(req.user_id)
    uid_a_prev, uid_b_prev = snap["uid_a"], snap["uid_b"]
    if uid not in (uid_a_prev, uid_b_prev):
        raise HTTPException(status_code=403, detail="Only the two duelists can request a rematch.")

    other_uid  = uid_b_prev if uid == uid_a_prev else uid_a_prev
    name_mine  = snap["name_a"] if uid == uid_a_prev else snap["name_b"]
    name_other = snap["name_b"] if uid == uid_a_prev else snap["name_a"]

    for k in active_versus:
        if uid in k or other_uid in k:
            raise HTTPException(status_code=400, detail="One of you already has an active Versus. Finish it first.")

    db = load_db()
    mode = snap["mode"]
    if len(_eligible_cards(uid, mode, db, snap.get("anime"))) < 8:
        raise HTTPException(status_code=400, detail=f"You don't own 8 eligible characters for {mode} mode.")
    if len(_eligible_cards(other_uid, mode, db, snap.get("anime"))) < 8:
        raise HTTPException(status_code=400, detail=f"{name_other} doesn't own 8 eligible characters for {mode} mode.")

    display  = snap.get("display", "chat")
    chat_id  = snap.get("chat_id")
    match_id = uuid.uuid4().hex[:12]
    key      = _state_key(uid, other_uid)

    active_versus[key] = {
        "match_id":    match_id,
        "challenger":  uid,
        "opponent":    other_uid,
        "name_a":      name_mine,
        "name_b":      name_other,
        "chat_id":     chat_id,
        "msg_id":      None,
        "stage":       "pending",
        "mode":        mode,
        "anime":       snap.get("anime"),
        "anime_opts":  [],
        "display":     display,
        "roster_a":    {},
        "roster_b":    {},
        "draft_turn":  uid,
        "score_a":     0,
        "score_b":     0,
        "ready_a":     False,
        "ready_b":     False,
        "skip_a":      2,
        "skip_b":      2,
        "draw_req_a":  False,
        "draw_req_b":  False,
        "expires":     time.time() + ACCEPT_TIMEOUT,
        "photo_board_active": False,
        "processing":  False,
        "pending_card": None,
        "start_time":  None,
        "spectators":  {},
    }
    active_versus_by_id[match_id] = key

    kb = _pending_kb(uid, other_uid, match_id, show_webapp=(display == "web"))
    pending_text = (
        f"<b>🔁 Rematch! {_link(uid, name_mine)} has challenged {_link(other_uid, name_other)} "
        f"to another Card Battle!</b>\n\n"
        f"<b>⤷「 Mode: {MODE_ICONS[mode]} {mode} 」</b>\n"
        f"{_anime_line(active_versus[key])}"
        f"<b>⤷「 Display: {DISPLAY_ICONS[display]} {DISPLAY_LABELS[display]} 」</b>\n"
        f"━━━━━━━━━━━━━━━\n\n"
        f"<b><i>{_link(other_uid, name_other)}, will you accept the rematch?</i></b>"
    )

    if chat_id:
        try:
            board_pic = db.get("settings", {}).get("pic_versus")
            if board_pic:
                msg = await bot.send_photo(
                    chat_id=chat_id, photo=board_pic, caption=pending_text,
                    parse_mode=ParseMode.HTML, reply_markup=kb
                )
                active_versus[key]["photo_board_active"] = True
            else:
                msg = await bot.send_message(
                    chat_id=chat_id, text=pending_text,
                    parse_mode=ParseMode.HTML, reply_markup=kb
                )
            active_versus[key]["msg_id"] = msg.message_id
            asyncio.create_task(_accept_timeout(key, msg.message_id, chat_id))
        except Exception:
            pass

    return {"ok": True, "match_id": match_id, "mode": mode, "display": display}


# ==========================================
# /vslive — LIST SPECTATABLE MATCHES
# ==========================================
def _strip_vs_tag(name: str) -> str:
    """Drop a leading 'ⱽˢ' clan tag from a display name (the list adds its own ⱽˢ between players)."""
    n = (name or "").strip()
    while n.startswith("ⱽˢ"):
        n = n[len("ⱽˢ"):].lstrip()
    return n or (name or "").strip()


@main_router.message(Command("vslive"))
async def vslive_cmd(message: Message):
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid): return

    live = [s for s in active_versus.values() if s["stage"] in ("drafting", "ready_check") and s.get("match_id") and _display_of(s) == "web"]
    if not live:
        await message.reply("⚔️ No live Versus matches right now.", parse_mode=ParseMode.HTML)
        return

    lines = ["<b>All Live Versus Matches</b>", "━━━━━━━━━━━━━━━━━", ""]
    buttons = []
    for i, s in enumerate(live[:10], start=1):
        name_a = html.escape(_strip_vs_tag(s["name_a"]))
        name_b = html.escape(_strip_vs_tag(s["name_b"]))
        lines.append(f"{i}) <b>{name_a} ⱽˢ {name_b}</b>")
        lines.append(f"- Mode : {MODE_ICONS[s['mode']]} {s['mode']}")
        lines.append("")
        buttons.append(_versus_webapp_button(s["match_id"], f"Watch {i}"))

    # 5 buttons per row, numbered to match the list
    rows = [buttons[j:j + 5] for j in range(0, len(buttons), 5)]

    await message.reply(
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(inline_keyboard=rows)
    )


# ==========================================
# ADMIN COMMANDS
# ==========================================
@main_router.message(Command("vim"))
async def vim_cmd(message: Message):
    uid = message.from_user.id
    if uid not in ADMIN_IDS:
        return

    if not message.reply_to_message or not message.reply_to_message.photo:
        await message.reply(
            "⚠️ <b>Usage:</b> Reply to an image with <code>/vim</code> to set it as the Versus board image.",
            parse_mode=ParseMode.HTML
        )
        return

    file_id = message.reply_to_message.photo[-1].file_id

    db = load_db()
    db["settings"]["pic_versus"] = file_id
    save_db()

    await message.reply("✅ <b>Versus board image updated!</b>", parse_mode=ParseMode.HTML)


def _build_vstats_text(db: dict) -> str:
    vstats = db.get("versus_stats", {})
    daily_stats = db.get("versus_daily_stats", {})
    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    total_battles     = vstats.get("total_battles", 0)
    completed_battles = vstats.get("completed_battles", 0)
    cancelled_battles = vstats.get("cancelled_battles", 0)
    active_battles    = len(active_versus)

    battles_today = daily_stats.get("battles_today", 0) if daily_stats.get("date") == today_str else 0
    shards_today  = daily_stats.get("shards_distributed_today", 0) if daily_stats.get("date") == today_str else 0
    shards_total  = vstats.get("total_shards_distributed", 0)

    cap_hits = 0
    for user_id, udata in db.get("users", {}).items():
        vr = udata.get("minigame_rewards_today", {})
        if vr.get("date") == today_str and vr.get("shards", 0) >= DAILY_MINIGAME_REWARD_CAP:
            cap_hits += 1

    pvp_players   = vstats.get("pvp_players", {})
    total_players = len(pvp_players)
    active_today  = len(daily_stats.get("active_players", [])) if daily_stats.get("date") == today_str else 0

    highest_streak = 0
    for p_id, p_rec in pvp_players.items():
        highest_streak = max(highest_streak, p_rec.get("max_streak", 0))

    highest_battles_today = 0
    if daily_stats.get("date") == today_str:
        for p_id, cnt in daily_stats.get("player_battles_today", {}).items():
            highest_battles_today = max(highest_battles_today, cnt)

    dur = vstats.get("total_match_duration", 0)
    cnt = vstats.get("match_duration_count", 0)
    if cnt > 0:
        avg_sec = dur / cnt
        minutes, seconds = divmod(int(avg_sec), 60)
        avg_time_str = f"{minutes}m {seconds}s"
    else:
        avg_time_str = "2m 18s"

    # ── Guess-the-Card stats ────────────────────────────────────────────────
    gstats = db.get("gcard_stats", {})
    gdaily = db.get("gcard_daily_stats", {})

    g_total_rounds  = gstats.get("total_rounds", 0)
    g_correct       = gstats.get("correct_guesses", 0)
    g_timeouts      = gstats.get("timeouts", 0)
    g_shards_total  = gstats.get("total_shards_distributed", 0)
    g_accuracy      = (g_correct / g_total_rounds * 100) if g_total_rounds else 0.0

    g_rounds_today  = gdaily.get("rounds_today", 0) if gdaily.get("date") == today_str else 0
    g_correct_today = gdaily.get("correct_today", 0) if gdaily.get("date") == today_str else 0
    g_shards_today  = gdaily.get("shards_distributed_today", 0) if gdaily.get("date") == today_str else 0
    g_active_today  = len(gdaily.get("active_players", [])) if gdaily.get("date") == today_str else 0

    stats_text = (
    "<b>「 𝗩𝗘𝗥𝗦𝗨𝗦 𝗔𝗗𝗠𝗜𝗡 𝗦𝗧𝗔𝗧𝗦 」</b>\n\n"

    f"• <b>Total Battles:</b> <code>{total_battles:,}</code>\n"
    f"• <b>Battles Today:</b> <code>{battles_today:,}</code>\n"
    f"• <b>Active Battles:</b> <code>{active_battles:,}</code>\n"
    f"• <b>Completed Battles:</b> <code>{completed_battles:,}</code>\n"
    f"• <b>Cancelled / AFK:</b> <code>{cancelled_battles:,}</code>\n\n"

    "<b>【 Reward Statistics 】</b>\n\n"
    f"• <b>Shards Distributed Today:</b> <code>{shards_today:,} 💠</code>\n"
    f"• <b>Total Shards Distributed:</b> <code>{shards_total:,} 💠</code>\n"
    f"• <b>Players Hit Daily Cap:</b> <code>{cap_hits:,}</code>\n\n"

    "<b>【 Player Statistics 】</b>\n\n"
    f"• <b>Total PvP Players:</b> <code>{total_players:,}</code>\n"
    f"• <b>Active Today:</b> <code>{active_today:,}</code>\n"
    f"• <b>Highest Win Streak:</b> <code>{highest_streak:,}</code>\n"
    f"• <b>Highest Battles Today:</b> <code>{highest_battles_today:,}</code>\n\n"

    "<b>【 System 】</b>\n\n"
    f"• <b>Average Match Time:</b> <code>{avg_time_str}</code>\n"
    "• <b>AFK Timeout:</b> <code>60s</code>\n"
    "• <b>Reward Per Win:</b> <code>150 💠</code>\n"
    f"• <b>Daily Reward Cap:</b> <code>{DAILY_MINIGAME_REWARD_CAP:,} 💠 (shared w/ Guess-the-Card)</code>\n\n"

    "<b>「 𝗚𝗨𝗘𝗦𝗦-𝗧𝗛𝗘-𝗖𝗔𝗥𝗗 𝗦𝗧𝗔𝗧𝗦 」</b>\n\n"
    f"• <b>Total Rounds:</b> <code>{g_total_rounds:,}</code>\n"
    f"• <b>Rounds Today:</b> <code>{g_rounds_today:,}</code>\n"
    f"• <b>Correct Guesses:</b> <code>{g_correct:,}</code>\n"
    f"• <b>Correct Today:</b> <code>{g_correct_today:,}</code>\n"
    f"• <b>Timeouts (No Guess):</b> <code>{g_timeouts:,}</code>\n"
    f"• <b>Accuracy:</b> <code>{g_accuracy:.1f}%</code>\n"
    f"• <b>Active Today:</b> <code>{g_active_today:,}</code>\n"
    f"• <b>Shards Distributed Today:</b> <code>{g_shards_today:,} 💠</code>\n"
    f"• <b>Total Shards Distributed:</b> <code>{g_shards_total:,} 💠</code>\n"
    f"• <b>Reward Per Correct Guess:</b> <code>{GCARD_REWARD_PER_GUESS} 💠</code>"
)

    return stats_text


def _vstats_refresh_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="vstats_refresh")]
    ])


@main_router.message(Command("vstats"))
async def vstats_cmd(message: Message):
    uid = message.from_user.id
    if uid not in ADMIN_IDS:
        return

    db = load_db()
    stats_text = _build_vstats_text(db)
    await message.reply(stats_text, parse_mode=ParseMode.HTML, reply_markup=_vstats_refresh_kb())


@main_router.callback_query(F.data == "vstats_refresh")
async def vstats_refresh_cb(cq: CallbackQuery):
    uid = cq.from_user.id
    if uid not in ADMIN_IDS:
        await cq.answer("Admins only.", show_alert=True)
        return

    db = load_db()
    stats_text = _build_vstats_text(db)
    try:
        await cq.message.edit_text(stats_text, parse_mode=ParseMode.HTML, reply_markup=_vstats_refresh_kb())
        await cq.answer("Refreshed ✅")
    except TelegramBadRequest:
        # Content unchanged since last refresh — nothing to edit
        await cq.answer("Already up to date.")


# ==========================================
# RULES COMMAND
# ==========================================
def _vsrule_menu_text() -> str:
    return (
        "<b>NEXUS AWAKENING — Versus Arena</b>\n\n"
        "Welcome to the Arena! Card Battle is a 1v1 PvP minigame where you draft "
        "cards from your own collection and clash stat-for-stat against another player.\n\n"
        "Tap a button below for details:\n"
        "<b>How to Play</b> — step-by-step walkthrough of a match.\n"
        "<b>Rules</b> — rewards, limits, and restrictions.\n"
        "<b>Stats</b> — what each stat means, with an example."
    )


def _vsrule_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="How to Play", callback_data="vsrule_howto", style=ButtonStyle.PRIMARY),
            InlineKeyboardButton(text="Rules", callback_data="vsrule_rules", style=ButtonStyle.SUCCESS),
        ],
        [InlineKeyboardButton(text="Stats", callback_data="vsrule_stats", style=ButtonStyle.PRIMARY)],
    ])


def _vsrule_howto_text() -> str:
    return (
        "<b>HOW TO PLAY — Versus Mode</b>\n"
        "━━━━━━━━━━━━━━━━━\n\n"

        "1) <b>Issue the Challenge</b>\n"
        "<blockquote>"
        "• Reply to a player's message with <code>/versus</code> to challenge them "
        "(<b>60s</b> to Accept).\n"
        "• The challenger customizes the match from <b>Settings</b> on the challenge message."
        "</blockquote>\n\n"

        "2) <b>Match Settings</b>\n"
        "<blockquote>"
        "• <b>Mode:</b> Chat or Web.\n"
        "• <b>Rarity:</b> Divine, Elite, Basic, or Mix.\n"
        "• <b>Universe:</b> Pick a specific anime series — only cards from that series will spawn. "
        "Only series where <b>both players</b> have enough cards are available.\n"
        "• If the selected rarity doesn't have enough cards, it automatically switches to a "
        "rarity both players have enough cards for."
        "</blockquote>\n\n"

        "3) <b>Ready Up</b>\n"
        "<blockquote>"
        "• Both players tap <b>Ready</b> to start the draft."
        "</blockquote>\n\n"

        "4) <b>The Draft Phase</b>\n"
        "<blockquote>"
        "• Take turns: tap <b>Pull Card</b>, then assign it to a slot — "
        "<b>Strength, Mana, Defence, Agility, Vitality, Intelligence, Luck</b>.\n"
        "• <b>Skip Card</b> discards a pull for a new one (max <b>2</b> per player).\n"
        "• <b>Let's Draw</b> ends the match early if both players agree — no reward.\n"
        "• <b>5 minutes</b> per turn, or the match may be forfeited as AFK."
        "</blockquote>\n\n"

        "5) <b>The Clash</b>\n"
        "<blockquote>"
        "• Matching slots are compared — higher stat wins the slot (+1 point), ties split it.\n"
        "• <b>Luck</b> is a 50/50 coin flip."
        "</blockquote>\n\n"

        "6) <b>The Result</b>\n"
        "<blockquote>"
        "• Highest total score across all 7 slots wins the duel."
        "</blockquote>\n\n"

        "Tap <b>Rules</b> to see rewards and limits, or <b>Back</b> to return."
    )


def _vsrule_rules_text() -> str:
    return (
        "<b>RULES — Rewards & Limits</b>\n"
        "━━━━━━━━━━━━━━━━━\n\n"
        "<b>「 𝗥𝗘𝗪𝗔𝗥𝗗𝗦 」</b>\n"
        "◉ <b>Victory Reward:</b> +150 💠 Nexus Shards per win.\n"
        f"◉ <b>Daily Shard Cap:</b> {DAILY_MINIGAME_REWARD_CAP:,} 💠 Nexus Shards per day — "
        "shared with the Guess-the-Card game. Once you hit it (from either game), further "
        "wins pay 0 shards until it resets, though a win that lands right at the cap can "
        "still pay out a partial amount.\n"
        "◉ <b>Defeat / Draw Reward:</b> No shards, win or nothing.\n"
        "◉ <b>Mutual Draw:</b> If both players tap <b>Let's Draw</b>, the match ends "
        "instantly as a draw — pays no shards.\n\n"
        "<b>「 𝗥𝗘𝗦𝗧𝗥𝗜𝗖𝗧𝗜𝗢𝗡𝗦 」</b>\n"
        "◉ You need at least <b>8 eligible cards</b> in the chosen rarity (and Universe, if one is selected) "
        "to start or accept a duel.\n"
        "◉ You can't challenge yourself or a bot.\n"
        "◉ You can only have <b>one active Versus</b> at a time — finish it before starting another.\n"
        "◉ <b>AFK Rule:</b> If either player fails to respond or participate in time, "
        "no rewards will be granted.\n\n"
        "Tap <b>How to Play</b> for a full walkthrough, or <b>Back</b> to return."
    )


def _vsrule_stats_text() -> str:
    return (
        "<b>STATS — What They Mean</b>\n"
        "━━━━━━━━━━━━━━━━━\n\n"
        "Every character card has its own value for each stat. In a match you fill "
        "<b>7 slots</b>, one per stat, and each slot is decided by comparing the two "
        "cards placed in it.\n\n"
        "<b>「 𝗧𝗛𝗘 𝗦𝗧𝗔𝗧𝗦 」</b>\n"
        "◉ <b>Strength</b> — raw physical power.\n"
        "◉ <b>Mana</b> — magical or spiritual energy.\n"
        "◉ <b>Defence</b> — how well the character withstands damage.\n"
        "◉ <b>Agility</b> — speed and reflexes.\n"
        "◉ <b>Vitality</b> — stamina and endurance.\n"
        "◉ <b>Intelligence</b> — tactics and brainpower.\n"
        "◉ <b>Luck</b> — pure chance. Card stats don't matter; it's a 50/50 coin flip.\n\n"
        "<b>「 𝗘𝗫𝗔𝗠𝗣𝗟𝗘 」</b>\n"
        "<blockquote>"
        "You pull <b>Card X</b> with Strength <b>90</b> and Mana <b>40</b>.\n"
        "• Put it in the <b>Strength</b> slot and it fights with <b>90</b>.\n"
        "• Put it in the <b>Mana</b> slot and it fights with only <b>40</b>.\n"
        "Only the stat matching the slot counts, so place each card where it is strongest."
        "</blockquote>\n\n"
        "<b>「 𝗦𝗖𝗢𝗥𝗜𝗡𝗚 」</b>\n"
        "<blockquote>"
        "Player A vs Player B:\n"
        "• Strength: 90 vs 75 — A wins (+1 to A)\n"
        "• Mana: 60 vs 80 — B wins (+1 to B)\n"
        "• Defence: 70 vs 55 — A wins (+1 to A)\n"
        "• Agility: 65 vs 65 — tie (+0.5 each)\n"
        "• Vitality: 85 vs 70 — A wins (+1 to A)\n"
        "• Intelligence: 50 vs 72 — B wins (+1 to B)\n"
        "• Luck: coin flip — A wins (+1 to A)\n\n"
        "Final score: <b>A 4.5 — B 2.5</b>. Player A wins the duel."
        "</blockquote>\n\n"
        "Tap <b>How to Play</b> or <b>Rules</b> for more, or <b>Back</b> to return."
    )


_VSRULE_PAGES = {
    "vsrule_howto": ("How to Play", ButtonStyle.PRIMARY),
    "vsrule_rules": ("Rules",       ButtonStyle.SUCCESS),
    "vsrule_stats": ("Stats",       ButtonStyle.PRIMARY),
}


def _vsrule_detail_kb(current: str) -> InlineKeyboardMarkup:
    """Buttons for the two pages other than `current`, plus Back."""
    others = [
        InlineKeyboardButton(text=label, callback_data=key, style=style)
        for key, (label, style) in _VSRULE_PAGES.items() if key != current
    ]
    return InlineKeyboardMarkup(inline_keyboard=[
        others,
        [InlineKeyboardButton(text="Back", callback_data="vsrule_menu", style=ButtonStyle.DANGER)]
    ])


@main_router.message(Command("vsrule"))
async def vsrule_cmd(message: Message):
    uid = message.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid): return

    if not _vsrule_command_allowed(uid):
        return

    await message.reply(
        _vsrule_menu_text(),
        parse_mode=ParseMode.HTML,
        reply_markup=_vsrule_menu_kb()
    )


@main_router.callback_query(F.data == "vsrule_howto")
async def vsrule_howto_cb(cq: CallbackQuery):
    uid = cq.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        await cq.answer()
        return

    await cq.message.edit_text(
        _vsrule_howto_text(),
        parse_mode=ParseMode.HTML,
        reply_markup=_vsrule_detail_kb("vsrule_howto")
    )
    await cq.answer()


@main_router.callback_query(F.data == "vsrule_rules")
async def vsrule_rules_cb(cq: CallbackQuery):
    uid = cq.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        await cq.answer()
        return

    await cq.message.edit_text(
        _vsrule_rules_text(),
        parse_mode=ParseMode.HTML,
        reply_markup=_vsrule_detail_kb("vsrule_rules")
    )
    await cq.answer()


@main_router.callback_query(F.data == "vsrule_stats")
async def vsrule_stats_cb(cq: CallbackQuery):
    uid = cq.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        await cq.answer()
        return

    await cq.message.edit_text(
        _vsrule_stats_text(),
        parse_mode=ParseMode.HTML,
        reply_markup=_vsrule_detail_kb("vsrule_stats")
    )
    await cq.answer()


@main_router.callback_query(F.data == "vsrule_menu")
async def vsrule_menu_cb(cq: CallbackQuery):
    uid = cq.from_user.id
    if is_ghost_banned(uid) or is_shadow_banned(uid):
        await cq.answer()
        return

    await cq.message.edit_text(
        _vsrule_menu_text(),
        parse_mode=ParseMode.HTML,
        reply_markup=_vsrule_menu_kb()
    )
    await cq.answer()

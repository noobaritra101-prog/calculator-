# --- START OF FILE gcard.py ---

import time
import random
import asyncio
import difflib
import io
import re
from datetime import datetime, timezone
from html import escape as _html_esc

from PIL import Image, ImageFilter
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery, BufferedInputFile, InputMediaPhoto,
    InlineKeyboardMarkup, InlineKeyboardButton
)
from aiogram.filters import Command
from aiogram.enums import ParseMode, ChatType
from aiogram.exceptions import TelegramBadRequest

import config
from config import (
    bot, main_router, load_db, save_db, format_rarity,
    get_mention, is_ghost_banned, is_shadow_banned,
    ensure_user, get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)

# ==========================================
# GUESS-THE-CARD MINIGAME SETTINGS
# ==========================================
GCARD_ROUND_TIMEOUT_SECS = 45      # time players have to guess before reveal
GCARD_REWARD_PER_GUESS   = 50      # shards awarded per correct guess


def _gcard_view_kb(chat_id: int, message_id: int) -> InlineKeyboardMarkup:
    """Builds a View button linking directly to the round's card message."""
    cid = str(chat_id)
    internal_id = cid[4:] if cid.startswith("-100") else cid.lstrip("-")
    link = f"https://t.me/c/{internal_id}/{message_id}"
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="View", url=link)]])

# Only these regions of the card art get blurred — everything else (the
# character's face/body/artwork) stays fully visible. Regions are fractions
# of (width, height) so they scale to any image size: (x0, y0, x1, y1).
NAME_BLUR_REGIONS = [
    (0.00, 0.06, 0.20, 0.66),   # left edge: vertical kanji + big vertical name text
    (0.55, 0.00, 1.00, 0.16),   # top-right: name / anime title / kanji / quote badge
    (0.10, 0.61, 0.90, 0.69),   # center: italic quote attribution ("— Character Name")
    (0.00, 0.96, 0.32, 1.00),   # footer: card ID code (often encodes the surname)
]
NAME_BLUR_RADIUS = 18

# Static caption to use both during and after the game finishes
GAME_CAPTION = (
    "Who's <b>hiding behind the blur?</b>\n\n"
    "<b>✎𓂃Type the character's name to guess!</b>"
)

# ── In-memory state ──────────────────────────────────────────────────────────
active_gcard: dict = {}   # str(chat_id) -> {"card_id","time","message_id","warn_msg_id"}


def _touch_gcard_daily(db: dict) -> dict:
    """Returns today's gcard daily-stats dict, resetting it if the date rolled over."""
    today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    daily = db.setdefault("gcard_daily_stats", {})
    if daily.get("date") != today_str:
        daily["date"] = today_str
        daily["rounds_today"] = 0
        daily["correct_today"] = 0
        daily["shards_distributed_today"] = 0
        daily["active_players"] = []
    return daily


def _blur_card_image(raw_bytes: bytes) -> bytes:
    """Blurs only the specific name-bearing regions of the card, leaving the
    main character artwork fully visible."""
    img = Image.open(io.BytesIO(raw_bytes)).convert("RGB")
    w, h = img.size
    for (fx0, fy0, fx1, fy1) in NAME_BLUR_REGIONS:
        box = (int(fx0 * w), int(fy0 * h), int(fx1 * w), int(fy1 * h))
        if box[2] <= box[0] or box[3] <= box[1]:
            continue
        region = img.crop(box)
        blurred_region = region.filter(ImageFilter.GaussianBlur(radius=NAME_BLUR_RADIUS))
        img.paste(blurred_region, box)
    out = io.BytesIO()
    img.save(out, format="JPEG", quality=90)
    out.seek(0)
    return out.getvalue()


async def _reveal_gcard(chat_id: int, msg_id: int, original_file_id: str):
    """Swaps the round's blurred photo back to the real card art while preserving original caption."""
    try:
        await bot.edit_message_media(
            chat_id=chat_id, message_id=msg_id,
            media=InputMediaPhoto(media=original_file_id, caption=GAME_CAPTION, parse_mode=ParseMode.HTML)
        )
    except TelegramBadRequest:
        pass
    except Exception:
        pass


async def _delete_message_after_delay(chat_id: int, message_id: int, delay: int = 120):
    """Safely deletes a targeted message after a specific delay in seconds."""
    await asyncio.sleep(delay)
    try:
        await bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception:
        pass


async def _warn_gcard(cid_str: str, msg_id: int, chat_id: int):
    """Replies with a warning indicator after 30 seconds of play."""
    await asyncio.sleep(30)
    if cid_str in active_gcard and active_gcard[cid_str].get("message_id") == msg_id:
        try:
            warn_msg = await bot.send_message(
                chat_id=chat_id,
                text="<b>⏰ Hurry up!</b> Only <b>15 Sec</b> left !",
                reply_to_message_id=msg_id,
                parse_mode=ParseMode.HTML
            )
            if cid_str in active_gcard:
                active_gcard[cid_str]["warn_msg_id"] = warn_msg.message_id
        except Exception:
            pass


async def _expire_gcard(cid_str: str, msg_id: int, chat_id: int):
    await asyncio.sleep(GCARD_ROUND_TIMEOUT_SECS)
    if cid_str in active_gcard and active_gcard[cid_str].get("message_id") == msg_id:
        card_id = active_gcard[cid_str]["card_id"]
        warn_msg_id = active_gcard[cid_str].get("warn_msg_id")
        del active_gcard[cid_str]

        # Clean up warning message instantly
        if warn_msg_id:
            asyncio.create_task(_delete_message_after_delay(chat_id, warn_msg_id, 0))

        db = load_db()
        card_data = db.get("global_cards", {}).get(card_id, {})
        name = card_data.get("name", "?")

        gstats = db.setdefault("gcard_stats", {})
        gstats["timeouts"] = gstats.get("timeouts", 0) + 1
        save_db()

        # Send timeout notice as a clean, brand-new reply to the game card
        anime = card_data.get("anime", "?")
        timeout_text = (
            "<b>⏰ TIME'S UP!</b>\n\n"
            "No one guessed it right!\n"
            f"It was <b>{name} from {anime}</b>"
        )
        timeout_msg = await bot.send_message(
            chat_id=chat_id,
            text=timeout_text,
            reply_to_message_id=msg_id,
            parse_mode=ParseMode.HTML,
            reply_markup=_gcard_view_kb(chat_id, msg_id)
        )

        # Unblur the card while keeping the caption exactly the same
        await _reveal_gcard(chat_id, msg_id, card_data.get("file_id"))
        
        # Remove only the revealed card picture after 2 minutes; the timeout notice stays
        asyncio.create_task(_delete_message_after_delay(chat_id, msg_id, 120))


@main_router.message(Command("gcard"))
async def gcard_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return

    # Restrict execution within private direct messages (DMs)
    if message.chat.type == ChatType.PRIVATE:
        await message.reply(
            "The <b>Card Guessing Game</b> can only be played in <b>group chats</b>.",
            parse_mode=ParseMode.HTML
        )
        return

    chat_id = message.chat.id
    cid_str = str(chat_id)

    # Concurrency Lock: Check if a slot is already pending or active
    if cid_str in active_gcard:
        msg_id = active_gcard[cid_str].get("message_id")
        kb = _gcard_view_kb(chat_id, msg_id) if msg_id else None
        await message.reply(
            "<b>⚠️ A guessing round is already active!</b>\n\n"
            "💬 Just type the character's name in chat to answer.",
            parse_mode=ParseMode.HTML,
            reply_markup=kb
        )
        return

    # Reserve the active slot immediately to block subsequent concurrent command inputs
    active_gcard[cid_str] = {"pending": True}

    db = load_db()
    if not db.get("global_cards"):
        active_gcard.pop(cid_str, None)
        await message.reply("❌ No cards exist in the system yet.", parse_mode=ParseMode.HTML)
        return

    card_id, card_data = random.choice(list(db["global_cards"].items()))
    original_file_id = card_data["file_id"]

    try:
        cached_blur_id = card_data.get("blurred_file_id")
        
        # Attempt instant load via pre-compiled blurry file_id
        if cached_blur_id:
            try:
                msg = await bot.send_photo(
                    chat_id=chat_id, photo=cached_blur_id,
                    caption=GAME_CAPTION, parse_mode=ParseMode.HTML
                )
            except Exception:
                cached_blur_id = None  # Fallback if cached file expired
                
        # Generate and save blurred template on cache miss
        if not cached_blur_id:
            file_info  = await bot.get_file(original_file_id)
            file_bytes = await bot.download_file(file_info.file_path)
            blurred_bytes = _blur_card_image(file_bytes.getvalue())
            photo_input = BufferedInputFile(blurred_bytes, filename="gcard_blur.jpg")
            
            msg = await bot.send_photo(
                chat_id=chat_id, photo=photo_input,
                caption=GAME_CAPTION, parse_mode=ParseMode.HTML
            )
            # Save the newly uploaded blurry file_id for instant load next time
            db["global_cards"][card_id]["blurred_file_id"] = msg.photo[-1].file_id
            save_db()

        # Update slot reservation with active state parameters
        active_gcard[cid_str] = {
            "card_id": card_id,
            "time": time.time(),
            "message_id": msg.message_id,
            "warn_msg_id": None
        }

        # Track round-start stats
        gstats = db.setdefault("gcard_stats", {})
        gstats["total_rounds"] = gstats.get("total_rounds", 0) + 1
        daily = _touch_gcard_daily(db)
        daily["rounds_today"] = daily.get("rounds_today", 0) + 1
        save_db()

        # Schedule warning and expiration threads
        asyncio.create_task(_warn_gcard(cid_str, msg.message_id, chat_id))
        asyncio.create_task(_expire_gcard(cid_str, msg.message_id, chat_id))

    except Exception as e:
        active_gcard.pop(cid_str, None)
        await message.reply(f"❌ Failed to start round: {e}", parse_mode=ParseMode.HTML)


# Plain-text guess listener — NOT a command. Only fires on non-"/" text, and
# only does anything at all if this chat currently has a round running.
@main_router.message(F.text, ~F.text.startswith("/"))
async def gcard_plain_guess_listener(message: Message):
    chat_id = message.chat.id
    cid_str = str(chat_id)

    if cid_str not in active_gcard or "pending" in active_gcard[cid_str]:
        return  # no active round running here

    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return

    game_data   = active_gcard[cid_str]
    card_id     = game_data["card_id"]
    start_time  = game_data["time"]
    msg_id      = game_data["message_id"]
    warn_msg_id = game_data.get("warn_msg_id")

    db = load_db()
    card_data = db["global_cards"].get(card_id)
    if not card_data:
        return

    target_name = card_data["name"].lower().strip()
    query = message.text.lower().strip()

    # Split targets into distinct alphanumeric parts to handle component guesses
    target_parts = re.findall(r'\b\w+\b', target_name)
    
    matched = False
    
    # 1. Direct match on the complete phrase
    if query == target_name:
        matched = True
    elif len(query) >= 3:
        # 2. Check if query matches any specific sub-part of the card name
        for part in target_parts:
            if len(part) < 3:
                continue
            # Exact match with a component part
            if query == part or part in query:
                matched = True
                break
            # Fuzzy match with an individual component part
            if difflib.SequenceMatcher(None, query, part).ratio() > 0.75:
                matched = True
                break
        
        # 3. Overall fuzzy match against the full combined name
        if not matched:
            if difflib.SequenceMatcher(None, query, target_name).ratio() > 0.70:
                matched = True

    if not matched:
        return  # wrong/unrelated message — stay silent, don't spam the chat

    time_taken = round(time.time() - start_time, 2)
    del active_gcard[cid_str]

    # Clean up warning message instantly if it was generated
    if warn_msg_id:
        asyncio.create_task(_delete_message_after_delay(chat_id, warn_msg_id, 0))

    user_id = str(uid_int)
    name    = message.from_user.first_name

    # ── Reward handling (shared daily cap with Versus) ──────────────────────
    ensure_user(user_id, name, message.from_user.username)
    user_data = db["users"][user_id]
    g_rewards = get_daily_minigame_rewards(user_data)

    current_rewarded_today = g_rewards.get("shards", 0)
    reward_amount = 0
    if current_rewarded_today < DAILY_MINIGAME_REWARD_CAP:
        reward_amount = min(GCARD_REWARD_PER_GUESS, DAILY_MINIGAME_REWARD_CAP - current_rewarded_today)
        user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + reward_amount
        g_rewards["shards"] = current_rewarded_today + reward_amount

    # ── Stats tracking ───────────────────────────────────────────────────────
    gstats = db.setdefault("gcard_stats", {})
    gstats["correct_guesses"] = gstats.get("correct_guesses", 0) + 1
    if reward_amount > 0:
        gstats["total_shards_distributed"] = gstats.get("total_shards_distributed", 0) + reward_amount

    daily = _touch_gcard_daily(db)
    daily["correct_today"] = daily.get("correct_today", 0) + 1
    if reward_amount > 0:
        daily["shards_distributed_today"] = daily.get("shards_distributed_today", 0) + reward_amount
    daily.setdefault("active_players", [])
    if user_id not in daily["active_players"]:
        daily["active_players"].append(user_id)

    # Personal record for /gcard_lbd (correct guesses, fastest guess, shards earned)
    rec = user_data.setdefault("gcard", {})
    rec["correct"] = rec.get("correct", 0) + 1
    rec["shards"] = rec.get("shards", 0) + reward_amount
    best = rec.get("best_time")
    if best is None or time_taken < best:
        rec["best_time"] = time_taken

    save_db()

    if reward_amount > 0:
        reward_suffix = f" <b>(+{reward_amount} Shards)</b>"
    else:
        reward_suffix = " <i>(Daily reward cap reached)</i>"

    winner_text = (
        f"🎊 {get_mention(user_id, name)} guessed it in <b>{time_taken}s</b>!{reward_suffix}\n\n"
        f"It was <b>{card_data['name']} From {card_data['anime']}.</b>"
    )

    # Send the win notification as a clean, brand-new text message with a View button
    winner_msg = await bot.send_message(
        chat_id=chat_id,
        text=winner_text,
        parse_mode=ParseMode.HTML,
        reply_markup=_gcard_view_kb(chat_id, msg_id)
    )

    # Unblur the original card image while maintaining the original caption
    await _reveal_gcard(chat_id, msg_id, card_data.get("file_id"))

    # Remove only the revealed card picture after 2 minutes; the victory text stays
    asyncio.create_task(_delete_message_after_delay(chat_id, msg_id, 120))


# ==========================================
# /gcard_lbd — LEADERBOARD (same layout as /scramble_lbd, own stats)
# ==========================================
GCARD_LB_TABS = {"time": "Fastest guess", "correct": "Correct guesses", "shards": "Total shards collected"}
GCARD_LB_TITLES = {"time": "FASTEST GUESS", "correct": "CORRECT GUESSES", "shards": "TOTAL SHARDS"}
GCARD_LBD_IMAGE = "https://i.ibb.co/9kpH571g/IMG-20261010-130819.jpg"   # leaderboard banner (caption limit: 1024 chars)

_GCARD_HAS_STYLE = "style" in getattr(InlineKeyboardButton, "model_fields", {})


def _gcard_btn(text: str, data: str, style: str | None = None):
    if style and _GCARD_HAS_STYLE:
        return InlineKeyboardButton(text=text, callback_data=data, style=style)
    return InlineKeyboardButton(text=f"[{text}]" if style == "success" else text, callback_data=data)


def _gcard_board(db: dict, tab: str):
    """[(value, uid, name)] best first. Time: lowest wins; Correct / Shards: highest wins."""
    rows = []
    for uid, u in (db.get("users") or {}).items():
        rec = u.get("gcard") if isinstance(u, dict) else None
        if not isinstance(rec, dict):
            continue
        if tab == "time":
            v = rec.get("best_time")
        elif tab == "correct":
            v = rec.get("correct", 0)
        else:
            v = rec.get("shards", 0)
        if v and v > 0:
            name = str(u.get("name") or "User")[:24]
            rows.append((v, str(uid), name))
    if tab == "time":
        rows.sort(key=lambda r: (r[0], r[1]))
    else:
        rows.sort(key=lambda r: (-r[0], r[1]))
    return rows


def _gcard_fmt_value(tab: str, v) -> str:
    if tab == "time":
        return f"{v:.2f}s" if v < 60 else f"{int(v // 60)}m {v % 60:04.1f}s"
    if tab == "correct":
        return f"{int(v):,} guess" + ("" if int(v) == 1 else "es")
    return f"{int(v):,} shards"


def _gcard_lb_text(db: dict, tab: str, uid) -> str:
    rows = _gcard_board(db, tab)
    text = f"<b>「 GCARD - {GCARD_LB_TITLES[tab]} 」</b>\n━━━━━━━━━━━━━━━━━\n"
    if rows:
        text += "\n".join(
            f"<b>{i + 1}.</b> <b>{_html_esc(name[:18])}</b> - {_gcard_fmt_value(tab, v)}"
            for i, (v, _u, name) in enumerate(rows[:10])
        )
    else:
        text += "Nobody has guessed a card yet. Be the first with /gcard"
    text += "\n━━━━━━━━━━━━━━━━━\n"
    me = str(uid)
    idx = next((i for i, r in enumerate(rows) if r[1] == me), None)
    if idx is None:
        text += "<b>Your rank:</b> Unranked"
    else:
        text += f"<b>Your rank:</b> #{idx + 1} with {_gcard_fmt_value(tab, rows[idx][0])}"
    return text


def _gcard_lb_kb(owner, active: str) -> InlineKeyboardMarkup:
    def btn(tab):
        return _gcard_btn(GCARD_LB_TABS[tab], f"glb:{tab}:{owner}",
                          "success" if tab == active else "primary")
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("time"), btn("correct")],
        [btn("shards")],
    ])


@main_router.message(Command("gcard_lbd"))
async def gcard_lbd_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    try:
        ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
        db = load_db()
        text = _gcard_lb_text(db, "time", uid_int)
        kb = _gcard_lb_kb(uid_int, "time")
        try:   # banner image with the leaderboard as its caption
            await message.reply_photo(photo=GCARD_LBD_IMAGE, caption=text,
                                      reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception:   # image unreachable: still show the leaderboard as text
            await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[gcard_lbd_CRASH] {e}")
        await message.reply("The leaderboard is unavailable right now. Please try again in a moment.")


@main_router.callback_query(F.data.startswith("glb:"))
async def gcard_lbd_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id):
        return
    try:
        _, tab, owner = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return
    if tab not in GCARD_LB_TABS:
        await cq.answer()
        return
    if str(cq.from_user.id) != owner:
        await cq.answer("This leaderboard belongs to someone else. Send /gcard_lbd for your own.", show_alert=True)
        return
    try:
        db = load_db()
        text = _gcard_lb_text(db, tab, cq.from_user.id)
        kb = _gcard_lb_kb(owner, tab)
        if cq.message.photo:   # banner image: the leaderboard lives in the caption
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[gcard_lbd_cb] failed: {e}")
    await cq.answer()


# --- END OF FILE gcard.py ---

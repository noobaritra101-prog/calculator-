import math
import difflib
import re
import unicodedata
import traceback
import os
import time
import random
import logging
from datetime import datetime, timezone
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery,
    InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto, WebAppInfo
)
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ChatMemberStatus

from fastapi import APIRouter, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
import aiohttp

import config
from config import (
    bot, main_router, DECK_PER_PAGE, RARITY_ORDER, BACKEND_PUBLIC_URL,
    format_rarity, ensure_user, load_db, save_db, is_ghost_banned, is_shadow_banned
)
from handlers import smart_reply, smart_reply_photo, _check_action_cooldown
from vlog import log_action

# ==========================================
# ERROR-ONLY FILE LOGGER (dlog.txt / /dlog)
# ==========================================
DLOG_PATH = "dlog.txt"

dlog = logging.getLogger("deck_dlog")
dlog.setLevel(logging.ERROR)
dlog.propagate = False  # keep this off the root logger so nothing but errors ends up in the file
if not dlog.handlers:
    _dlog_handler = logging.FileHandler(DLOG_PATH, encoding="utf-8")
    _dlog_handler.setLevel(logging.ERROR)
    _dlog_handler.setFormatter(logging.Formatter("%(asctime)s | %(message)s", datefmt="%Y-%m-%d %H:%M:%S"))
    dlog.addHandler(_dlog_handler)

# ==========================================
# FASTAPI WEB APP API ROUTER (/api/deck)
# ==========================================
deck_api = APIRouter(prefix="/api/deck", tags=["Deck"])

# ==========================================
# ADSGRAM REWARDED-AD DAILY CARD
# ==========================================
# Watch 2 ads/day, then tap Claim -> 1 random Basic/Elite card. The ONLY
# trusted source for the watch COUNT is Adsgram's own server-to-server
# postback (adsgram_reward_cb below), configured as the block's "Reward url"
# in partner.adsgram.ai as:
#   https://<your-domain>/api/deck/ads/reward?userid=[userId]&key=<secret>
# The client-side AdController.show().then() in deck.html must NEVER credit
# anything, and never even learns what the reward will be — it's UI-only
# (progress display). The card itself is picked and revealed only when the
# player explicitly taps Claim (adsgram_claim_cb below), once the postback
# has confirmed enough real watches — so the reward is never previewed or
# spoiled before that deliberate action.
ADSGRAM_REWARD_SECRET = "gUz6e7bs0-TrdtHVtx7EAM63mMpfvQsc"
ADSGRAM_ADS_PER_CYCLE = 2
ADSGRAM_REWARD_RARITIES = ["Basic 🃏", "Elite ⚓", "Divine ❄️"]

# Weighted odds for which rarity tier a claim rolls into. Divine is a true
# rare-chance tier — roughly 10 in 2000 claims — with the remaining
# probability split 60/40 between Elite and Basic. Once a tier is picked,
# the specific card is chosen from that tier's pool: for Elite/Basic we
# prefer a card the player doesn't already own (falling back to the full
# pool only if every card in that tier is already owned), while Divine is
# picked uniformly from its whole pool, so a duplicate Divine the player
# already owns is expected and fine (it still adds +1 to that card's amount).
ADSGRAM_DIVINE_CHANCE = 10 / 2000         # 0.5%
ADSGRAM_ELITE_SHARE = 0.60                # of the remaining 99.9%
ADSGRAM_BASIC_SHARE = 0.40
ADSGRAM_RARITY_WEIGHTS = {
    "Divine ❄️": ADSGRAM_DIVINE_CHANCE,
    "Elite ⚓": (1 - ADSGRAM_DIVINE_CHANCE) * ADSGRAM_ELITE_SHARE,
    "Basic 🃏": (1 - ADSGRAM_DIVINE_CHANCE) * ADSGRAM_BASIC_SHARE,
}

def _today_str() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")

def _get_ad_progress(user_data: dict) -> dict:
    """Returns today's ad-watch progress, resetting it if the UTC date rolled over."""
    progress = user_data.setdefault("ad_progress", {})
    if progress.get("date") != _today_str():
        progress["date"] = _today_str()
        progress["watched"] = 0
        progress["claimed"] = False
    return progress

@deck_api.get("/ads/status/{user_id}")
async def get_ad_status(user_id: str):
    """Lets the frontend show today's watch progress (e.g. '2/2') and
    whether today's card is ready to claim / already claimed. Never
    includes any hint of what the reward is."""
    db = load_db()
    actual_key, user_data = get_user_from_db(db, user_id)
    if not user_data:
        ensure_user(user_id, "User", None)
        db = load_db()
        actual_key, user_data = get_user_from_db(db, user_id)
    if not user_data:
        return {"watched": 0, "required": ADSGRAM_ADS_PER_CYCLE, "claimed": False, "ready": False}

    progress = _get_ad_progress(user_data)
    save_db()
    return {
        "watched": progress["watched"],
        "required": ADSGRAM_ADS_PER_CYCLE,
        "claimed": progress["claimed"],
        "ready": progress["watched"] >= ADSGRAM_ADS_PER_CYCLE and not progress["claimed"]
    }

@deck_api.get("/ads/reward")
async def adsgram_reward_callback(userid: str, key: str = ""):
    """Server-to-server callback — Adsgram calls this directly after a
    genuine (non-debug) completed rewarded-ad view. This is the sole
    source of truth for the daily watch COUNT. It never picks or grants
    a card — that only happens via an explicit /ads/claim call."""
    if key != ADSGRAM_REWARD_SECRET:
        raise HTTPException(status_code=403, detail="Invalid key")

    db = load_db()
    actual_key, user_data = get_user_from_db(db, userid)
    if not user_data:
        ensure_user(userid, "User", None)
        db = load_db()
        actual_key, user_data = get_user_from_db(db, userid)
    if not user_data:
        raise HTTPException(status_code=404, detail="User not found")

    progress = _get_ad_progress(user_data)

    if progress["claimed"]:
        save_db()
        return {"ok": True, "status": "already_claimed_today", "watched": progress["watched"]}

    if progress["watched"] < ADSGRAM_ADS_PER_CYCLE:
        progress["watched"] += 1

    save_db()
    if progress["watched"] >= ADSGRAM_ADS_PER_CYCLE:
        return {"ok": True, "status": "ready_to_claim", "watched": progress["watched"]}
    return {"ok": True, "status": "progress", "watched": progress["watched"]}

@deck_api.post("/ads/claim/{user_id}")
async def claim_ad_reward(user_id: str):
    """Explicit claim step — only runs once enough genuine watches have
    been confirmed via the Adsgram postback above. Picks the random card
    HERE (never before), so nothing is revealed until this exact moment,
    and returns the card so the frontend can pop it up."""
    db = load_db()
    actual_key, user_data = get_user_from_db(db, user_id)
    if not user_data:
        raise HTTPException(status_code=404, detail="User not found")

    progress = _get_ad_progress(user_data)

    if progress["claimed"]:
        raise HTTPException(status_code=400, detail="Already claimed today")
    if progress["watched"] < ADSGRAM_ADS_PER_CYCLE:
        raise HTTPException(status_code=400, detail="Watch requirement not met yet")

    locked_animes = db.get("settings", {}).get("locked_animes", [])
    locked_animes_lower = [a.lower().strip() for a in locked_animes]

    pools_by_rarity = {rarity: {} for rarity in ADSGRAM_REWARD_RARITIES}
    for k, v in db.get("global_cards", {}).items():
        r = format_rarity(v["rarity"])
        if r in pools_by_rarity and v["anime"].lower().strip() not in locked_animes_lower:
            pools_by_rarity[r][k] = v

    available_rarities = [r for r in ADSGRAM_REWARD_RARITIES if pools_by_rarity[r]]
    if not available_rarities:
        raise HTTPException(status_code=503, detail="No cards available right now — try again shortly")

    # Roll the rarity tier first (weighted), then pick a card uniformly
    # from within that tier. Re-normalize weights over only the tiers that
    # currently have cards, so an empty tier never blocks a claim.
    weights = [ADSGRAM_RARITY_WEIGHTS[r] for r in available_rarities]
    chosen_rarity = random.choices(available_rarities, weights=weights, k=1)[0]
    card_pool = pools_by_rarity[chosen_rarity]

    if chosen_rarity != "Divine ❄️":
        # No duplicates for Elite/Basic if we can help it — restrict to
        # cards the player doesn't already own. Only fall back to the full
        # (possibly-owned) pool if literally every card in this tier is
        # already in their deck, so a claim never gets stuck.
        owned = user_data.get("cards", {})
        unowned_pool = {k: v for k, v in card_pool.items() if k not in owned}
        if unowned_pool:
            card_pool = unowned_pool

    card_id, card_data = random.choice(list(card_pool.items()))
    user_cards = user_data.setdefault("cards", {})
    if card_id not in user_cards:
        user_cards[card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
    user_cards[card_id]["amount"] += 1

    progress["claimed"] = True

    log_action(db, str(actual_key), {
        "type": "ad_reward",
        "card_name": card_data["name"],
        "rarity": format_rarity(card_data["rarity"]),
        "chat_title": "Adsgram Daily Reward"
    })
    save_db()

    display_rarity = format_rarity(card_data["rarity"])
    dm_caption = (
        f"<b>「 🎁 DAILY AD REWARD 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<b>Name</b>   : {card_data.get('name', 'Card')}\n"
        f"<b>Rarity</b> : {display_rarity}\n"
        f"<b>Anime</b>  : {card_data.get('anime', 'Unknown')}\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<blockquote>✨ <b>Added to your deck!</b></blockquote>"
    )
    try:
        file_id = card_data.get("file_id")
        if file_id:
            await bot.send_photo(chat_id=int(actual_key), photo=file_id, caption=dm_caption, parse_mode=ParseMode.HTML)
        else:
            await bot.send_message(chat_id=int(actual_key), text=dm_caption, parse_mode=ParseMode.HTML)
    except Exception as e:
        # DM can fail if the user blocked the bot / never started a chat with it —
        # never let that break the claim itself, just log it.
        dlog.error(f"[ads/claim] failed to DM user {actual_key} their claimed card: {e}")

    return {
        "ok": True,
        "card_id": card_id,
        "name": card_data["name"],
        "rarity": display_rarity,
        "anime": card_data.get("anime", "Unknown")
    }


# ==========================================
# /watchad — IN-CHAT (NON-WEBAPP) ADSGRAM ADS
# ==========================================
# This is a SEPARATE AdsGram ad block from the webapp rewarded-card system
# above (deck.html uses the AdsGram JS SDK; this uses AdsGram's bot-chat
# API: https://api.adsgram.ai/advbot). Sending the ad itself uses that
# GET-based advbot endpoint below. Crediting the reward is SEPARATE and
# trustworthy: this ad block's "Reward URL" (set in the AdsGram dashboard)
# points back at watchad_reward_callback() below, which AdsGram's own
# server calls with the real Telegram user id once a genuine REWARD event
# fires. That callback is the ONLY place shards get credited — nothing in
# the /watchad command itself grants anything.
ADSGRAM_BOT_TOKEN = "37e23e9115824303b8efec1b8e23cd78"    # from your AdsGram profile (Copy token)
ADSGRAM_WATCHAD_BLOCKID = "48391"                          # numeric only, no "bot-" prefix
ADSGRAM_WATCHAD_REWARD_SECRET = "8yhhrHral2eMLBMr_oK0NQkWTxsk-vVv"  # put the same value in the Reward URL's &key=
ADSGRAM_WATCHAD_REWARD_AMOUNT = 30                          # flat shards per confirmed watch
ADSGRAM_WATCHAD_COOLDOWN_SECONDS = 30 * 60                  # 30 min between claimable rewards, per user

def _watchad_seconds_remaining(user_data: dict) -> int:
    """Seconds left before this user can earn another /watchad reward.
    0 (or negative) means they're eligible right now. Stored on the user
    record (not an in-memory cooldown) so it survives restarts and can't
    be reset by spamming /watchad — the ad-fetch cooldown below is a
    separate, shorter anti-spam check on the command itself."""
    last = user_data.get("watchad_last_reward_ts", 0)
    elapsed = time.time() - last
    return int(ADSGRAM_WATCHAD_COOLDOWN_SECONDS - elapsed)

@deck_api.get("/ads/watchad-reward")
async def watchad_reward_callback(userid: str, key: str = ""):
    """Server-to-server callback configured as this ad block's Reward URL:
    https://<your-domain>/api/deck/ads/watchad-reward?userid=[userId]&key=<secret>
    AdsGram substitutes [userId] with the Telegram user id and calls this
    from their server after a genuine completed ad view. This is the sole
    source of truth for the /watchad reward — the command handler never
    credits anything on its own."""
    if key != ADSGRAM_WATCHAD_REWARD_SECRET:
        raise HTTPException(status_code=403, detail="Invalid key")

    db = load_db()
    actual_key, user_data = get_user_from_db(db, userid)
    if not user_data:
        ensure_user(userid, "User", None)
        db = load_db()
        actual_key, user_data = get_user_from_db(db, userid)
    if not user_data:
        raise HTTPException(status_code=404, detail="User not found")

    remaining = _watchad_seconds_remaining(user_data)
    if remaining > 0:
        save_db()
        return {"ok": True, "status": "on_cooldown", "seconds_remaining": remaining}

    user_data["watchad_last_reward_ts"] = time.time()
    user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + ADSGRAM_WATCHAD_REWARD_AMOUNT

    log_action(db, str(actual_key), {
        "type": "watchad_reward",
        "shards_earned": ADSGRAM_WATCHAD_REWARD_AMOUNT,
        "chat_title": "Adsgram /watchad Reward"
    })
    save_db()

    try:
        await bot.send_message(
            chat_id=int(actual_key),
            text=f"💠 <b>+{ADSGRAM_WATCHAD_REWARD_AMOUNT} Nexus Shards</b> credited for watching an ad!",
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        # DM can fail if the user blocked the bot — never let that break
        # the credit itself, just log it.
        dlog.error(f"[watchad_reward] failed to DM user {actual_key} their reward: {e}")

    return {"ok": True, "status": "credited", "shards_earned": ADSGRAM_WATCHAD_REWARD_AMOUNT}

async def _fetch_adsgram_bot_ad(tgid: str, language: str = "en") -> dict | None:
    """Calls AdsGram's bot-chat ad endpoint and returns the parsed JSON, or
    None if no ad is available / the request failed."""
    url = (
        "https://api.adsgram.ai/advbot"
        f"?tgid={tgid}&blockid={ADSGRAM_WATCHAD_BLOCKID}"
        f"&language={language}&token={ADSGRAM_BOT_TOKEN}"
    )
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                if resp.status != 200:
                    dlog.error(f"[watchad] AdsGram returned status {resp.status} for tgid={tgid}")
                    return None
                data = await resp.json(content_type=None)
                if not data or not data.get("text_html"):
                    return None
                return data
    except Exception as e:
        dlog.error(f"[watchad] AdsGram fetch failed for tgid={tgid}: {e}")
        return None

@main_router.message(Command("watchad"))
async def watchad_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    if _check_action_cooldown(f"watchad_{user_id}"):
        await smart_reply(message, "⏳ Please wait a moment before requesting another ad.", parse_mode=ParseMode.HTML)
        return

    _, user_data = get_user_from_db(db, user_id)
    remaining = _watchad_seconds_remaining(user_data) if user_data else 0
    if remaining > 0:
        mins = max(1, remaining // 60)
        await smart_reply(
            message,
            f"⏳ You've already earned shards from an ad recently. Try again in ~{mins} min.",
            parse_mode=ParseMode.HTML,
        )
        return

    ad = await _fetch_adsgram_bot_ad(user_id)
    if not ad:
        await smart_reply(message, "😕 No ads available right now — try again in a bit.", parse_mode=ParseMode.HTML)
        return

    buttons = []
    if ad.get("button_name") and ad.get("click_url"):
        buttons.append(InlineKeyboardButton(text=ad["button_name"], url=ad["click_url"]))
    if ad.get("button_reward_name") and ad.get("reward_url"):
        buttons.append(InlineKeyboardButton(text=ad["button_reward_name"], url=ad["reward_url"]))
    kb = InlineKeyboardMarkup(inline_keyboard=[buttons]) if buttons else None

    # AdsGram requires ads sent via the bot API to be non-forwardable.
    # reply_to_message_id ties the ad back to the /watchad command that
    # triggered it — this matters in groups where several people may be
    # requesting ads around the same time. allow_sending_without_reply
    # keeps this from erroring if the original command got deleted.
    try:
        if ad.get("image_url"):
            await bot.send_photo(
                chat_id=message.chat.id,
                photo=ad["image_url"],
                caption=ad["text_html"],
                parse_mode=ParseMode.HTML,
                reply_markup=kb,
                protect_content=True,
                reply_to_message_id=message.message_id,
                allow_sending_without_reply=True,
            )
        else:
            await bot.send_message(
                chat_id=message.chat.id,
                text=ad["text_html"],
                parse_mode=ParseMode.HTML,
                reply_markup=kb,
                protect_content=True,
                reply_to_message_id=message.message_id,
                allow_sending_without_reply=True,
            )
    except Exception as e:
        dlog.error(f"[watchad] failed to send ad to {user_id}: {e}")
        await smart_reply(message, "😕 Couldn't load an ad right now — try again shortly.", parse_mode=ParseMode.HTML)
        return

    await smart_reply(
        message,
        f"💠 Complete the ad above and your <b>+{ADSGRAM_WATCHAD_REWARD_AMOUNT} shards</b> will be credited automatically.",
        parse_mode=ParseMode.HTML,
    )


# In-memory cache for Telegram image URLs.
# Telegram only guarantees a getFile() link stays valid for ~1 hour, so we
# cache with a TTL comfortably under that and re-resolve on expiry — without
# this, any card viewed once would silently start 404ing after an hour.
_file_url_cache: dict[str, tuple[str, float]] = {}  # file_id -> (url, resolved_at)
_FILE_URL_TTL_SECONDS = 45 * 60  # 45 min, safely under Telegram's ~1hr guarantee

class BurnRequest(BaseModel):
    user_id: str
    card_id: str

class SpecialRequest(BaseModel):
    user_id: str
    card_id: str

class ClientErrorReport(BaseModel):
    user_id: str | None = None
    message: str = ""
    stack: str | None = None
    user_agent: str | None = None
    context: str | None = None  # e.g. "loadDeck"


@deck_api.post("/clientlog")
async def report_client_error(req: ClientErrorReport):
    """Best-effort sink for client-side failures (network errors, WebView
    quirks, etc.) that never reach any other endpoint — these previously had
    zero server-side visibility. Always returns 200; a failure to log an
    error should never itself surface as a user-facing error."""
    try:
        dlog.error(
            f"[CLIENT_ERROR] uid={req.user_id} context={req.context} "
            f"ua={req.user_agent} msg={req.message} stack={req.stack}"
        )
    except Exception as e:
        print(f"[clientlog] failed to write: {e}")
    return {"ok": True}


def get_user_from_db(db: dict, user_id: str):
    """Helper to locate user data supporting BOTH string and integer DB keys."""
    if not db or not isinstance(db, dict):
        return None, None
        
    users = db.get("users", {})
    if not isinstance(users, dict):
        return None, None

    str_id = str(user_id)
    int_id = int(user_id) if str_id.isdigit() else None

    if str_id in users:
        return str_id, users[str_id]
    elif int_id is not None and int_id in users:
        return int_id, users[int_id]
    return None, None


@deck_api.get("/image/{card_id}")
async def get_card_image_proxy(card_id: str):
    """Streams a Telegram-hosted card image through our own server.

    Deliberately does NOT redirect to Telegram's file URL — that URL embeds
    our bot token (https://api.telegram.org/file/bot<TOKEN>/...), which
    would otherwise be visible to any client in DevTools/Network tab and
    could be used to hijack the bot. Fetching and streaming the bytes here
    keeps the token server-side only.
    """
    try:
        db = load_db()
        global_cards = db.get("global_cards", {}) if isinstance(db, dict) else {}
        file_id = global_cards.get(card_id, {}).get("file_id") if isinstance(global_cards, dict) else None

        if not file_id:
            raise HTTPException(status_code=404, detail="Image file_id not found")

        cached = _file_url_cache.get(file_id)
        if cached and (time.time() - cached[1]) < _FILE_URL_TTL_SECONDS:
            direct_url = cached[0]
        else:
            telegram_file = await bot.get_file(file_id)
            direct_url = f"https://api.telegram.org/file/bot{config.BOT_TOKEN}/{telegram_file.file_path}"
            _file_url_cache[file_id] = (direct_url, time.time())

        session = aiohttp.ClientSession()
        try:
            resp = await session.get(direct_url)
        except Exception:
            await session.close()
            raise

        if resp.status != 200:
            resp.release()
            await session.close()
            raise HTTPException(status_code=404, detail="Image unavailable")

        content_type = resp.headers.get("Content-Type", "image/jpeg")

        async def _stream():
            try:
                async for chunk in resp.content.iter_chunked(64 * 1024):
                    yield chunk
            finally:
                resp.release()
                await session.close()

        return StreamingResponse(
            _stream(),
            media_type=content_type,
            headers={"Cache-Control": "public, max-age=86400"},  # card art doesn't change, safe to cache client-side for a day
        )
    except HTTPException:
        raise
    except Exception as e:
        print(f"[image_proxy] Failed to resolve file_id {card_id}: {e}")
        dlog.error(f"[image_proxy] Failed to resolve file_id {card_id}: {e}", exc_info=True)
        raise HTTPException(status_code=404, detail="Image unavailable")


@deck_api.get("/state/{user_id}")
async def get_deck_state(user_id: str):
    """Crash-proof state endpoint that always returns a valid JSON response."""
    try:
        db = load_db()
        actual_key, user_data = get_user_from_db(db, user_id)
        
        if not user_data:
            ensure_user(user_id, "User", None)
            db = load_db()
            actual_key, user_data = get_user_from_db(db, user_id)

        if not user_data or not isinstance(user_data, dict):
            return {
                "user_id": str(user_id),
                "name": "User",
                "balance": 0,
                "special_card": None,
                "cards": []
            }

        cards = user_data.get("cards")
        if not isinstance(cards, dict):
            cards = {}

        global_cards = db.get("global_cards")
        if not isinstance(global_cards, dict):
            global_cards = {}
        
        enriched_cards = []
        for cid, cdata in cards.items():
            if not isinstance(cdata, dict):
                continue
                
            g_info = global_cards.get(cid)
            if not isinstance(g_info, dict):
                g_info = {}

            has_photo = bool(g_info.get("file_id"))
            
            card_name = cdata.get("name") or g_info.get("name") or "Unknown Card"
            card_rarity = cdata.get("rarity") or g_info.get("rarity") or "Common"
            card_amount = cdata.get("amount", 1)
            card_anime = g_info.get("anime") or "Unknown Anime"

            enriched_cards.append({
                "id": str(cid),
                "name": str(card_name),
                "rarity": format_rarity(card_rarity),
                "amount": int(card_amount) if str(card_amount).isdigit() else 1,
                "anime": str(card_anime),
                "img_url": f"{BACKEND_PUBLIC_URL}/api/deck/image/{cid}" if has_photo else None
            })

        balance_val = user_data.get("nexus_shards", 0)
        try:
            balance_val = int(balance_val)
        except Exception:
            balance_val = 0

        return {
            "user_id": str(user_id),
            "name": str(user_data.get("name", "User")),
            "balance": balance_val,
            "special_card": user_data.get("special_card"),
            "cards": enriched_cards,
            "error": False
        }
    except Exception as e:
        print(f"[get_deck_state_CRASH] Exception for {user_id}: {e}")
        traceback.print_exc()
        dlog.error(f"[get_deck_state_CRASH] Exception for {user_id}: {e}", exc_info=True)
        # Still return 200 (frontend-safe) but flag it so the client can tell
        # a genuine empty collection apart from "we crashed and are hiding it".
        return {
            "user_id": str(user_id),
            "name": "User",
            "balance": 0,
            "special_card": None,
            "cards": [],
            "error": True
        }


@deck_api.post("/burn")
async def api_burn_card(req: BurnRequest):
    try:
        db = load_db()
        actual_key, user_data = get_user_from_db(db, req.user_id)

        if not user_data or not isinstance(user_data, dict):
            raise HTTPException(status_code=400, detail="User profile not found.")

        user_cards = user_data.get("cards")
        if not isinstance(user_cards, dict):
            raise HTTPException(status_code=400, detail="No cards owned.")

        if req.card_id not in user_cards or user_cards[req.card_id].get("amount", 0) <= 0:
            raise HTTPException(status_code=400, detail="Card not owned.")

        card_data = user_cards[req.card_id]
        rarity_normalized = format_rarity(card_data.get("rarity", "Common"))

        burn_payout = 150
        if rarity_normalized == "Elite ⚓": burn_payout = 450
        elif rarity_normalized == "Divine ❄️": burn_payout = 1800

        user_cards[req.card_id]["amount"] -= 1
        if user_cards[req.card_id]["amount"] <= 0:
            del user_cards[req.card_id]
            if user_data.get("special_card") == req.card_id:
                user_data["special_card"] = None

        user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + burn_payout

        log_action(db, str(actual_key), {
            "type": "web_burn",
            "card_name": card_data.get("name", "Card"),
            "rarity": rarity_normalized,
            "shards_earned": burn_payout
        })
        save_db()

        return {
            "success": True,
            "burned_card": card_data.get("name", "Card"),
            "shards_earned": burn_payout,
            "new_balance": user_data["nexus_shards"]
        }
    except HTTPException:
        raise
    except Exception as e:
        print(f"[burn_CRASH] Exception: {e}")
        dlog.error(f"[burn_CRASH] Exception for {req.user_id}: {e}", exc_info=True)
        traceback.print_exc()
        raise HTTPException(status_code=500, detail="Burn processing error.")


@deck_api.post("/special")
async def api_set_special(req: SpecialRequest):
    try:
        db = load_db()
        actual_key, user_data = get_user_from_db(db, req.user_id)

        if not user_data or not isinstance(user_data, dict):
            raise HTTPException(status_code=400, detail="User profile not found.")

        user_cards = user_data.get("cards")
        if not isinstance(user_cards, dict) or req.card_id not in user_cards:
            raise HTTPException(status_code=400, detail="Card not owned.")

        user_data["special_card"] = req.card_id
        save_db()

        return {"success": True, "special_card": req.card_id}
    except HTTPException:
        raise
    except Exception as e:
        print(f"[special_CRASH] Exception: {e}")
        traceback.print_exc()
        dlog.error(f"[special_CRASH] Exception for {req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Special card update error.")


# ==========================================
# /webdeck COMMAND (OPEN NETLIFY WEB APP)
# ==========================================
BOT_USERNAME = "Animenx_bot"
WEBDECK_APP_LINK = f"https://t.me/{BOT_USERNAME}/webdeck"


@main_router.message(Command("webdeck"))
async def open_web_deck_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    # Direct Mini App link — unlike a `web_app` inline button, this works
    # fine inside groups too, and Telegram still populates initDataUnsafe.user
    # correctly on open, so no group/DM split is needed anymore.
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎴 Open Card Deck Web", url=WEBDECK_APP_LINK)]
    ])

    await smart_reply(
        message,
        "<b>「 🎴 CARDS COLLECTION WEB 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Explore your anime card deck in 3D, inspect stats, filter by anime/rarity, and recycle duplicate cards for <b>Nexus Shards 💠</b>!",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /airdrop COMMAND — opens the mini app directly to the ad-reward section
# ==========================================
AIRDROP_APP_LINK = f"https://t.me/{BOT_USERNAME}/webdeck?startapp=airdrop"

@main_router.message(Command("airdrop"))
async def airdrop_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📺 Open Airdrop", url=AIRDROP_APP_LINK)]
    ])
    await smart_reply(
        message,
        "<b>「 📺 DAILY AIRDROP ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Watch a couple of quick ads for a free card drop!",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )


@main_router.message(Command("adrop"))
async def adrop_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📺 Open Airdrop", url="https://t.me/Animenx_bot/airdrop")]
    ])
    await smart_reply(
        message,
        "<b>「 📺 DAILY AIRDROP ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Watch a couple of quick ads for a free card drop!",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )


# NOTE: /dlog, /bug, and /adstats used to live here — they've moved to
# a_handlers.py so every admin command lives in one place.


# ==========================================
# DECK DISPLAY LAYER (/deck)
# ==========================================
_ZERO_WIDTH_CHARS = {
    "\u200b", "\u200c", "\u200d", "\u200e", "\u200f", "\ufeff",
    "\u2060", "\u2061", "\u2062", "\u2063", "\u2064",
}

def sanitize_display_name(name: str, max_len: int = 24) -> str:
    """Strips zero-width/invisible characters and Unicode combining marks."""
    if not name:
        return "User"
    cleaned = "".join(ch for ch in str(name) if ch not in _ZERO_WIDTH_CHARS)
    cleaned = "".join(ch for ch in cleaned if unicodedata.category(ch) not in ("Mn", "Mc", "Me"))
    cleaned = cleaned.strip()
    return cleaned[:max_len] if cleaned else "User"


# Telegram caption hard limit: 1024 characters, counted in UTF-16 code units,
# AFTER the HTML entities (<b>, <i>, <code>, <a>, ...) are parsed out — it's
# the visible text that's capped, not the raw markup source. A small safety
# margin is kept below the hard cap for pagination footers/edits appended later.
TELEGRAM_CAPTION_LIMIT = 1024
CAPTION_SAFE_LIMIT = 1000

_HTML_TAG_RE = re.compile(r"<[^>]+>")

def caption_visible_length(html_text: str) -> int:
    """Length Telegram will actually count against the caption limit.

    Two things a plain `len(text)` on the raw HTML string gets wrong here:
    1. It counts the HTML tags themselves (<b>, <a href="...">, ...), which
       Telegram strips before applying the limit — this makes captions look
       LONGER than they really are.
    2. Deck captions lean heavily on Mathematical Alphanumeric Symbols for
       styled headers (𝗖𝗔𝗥𝗗, 𝗗𝗘𝗖𝗞, 𝗔𝗻𝗶𝗺𝗲, 𝗣𝗮𝗴𝗲, ...). Those sit outside the
       Basic Multilingual Plane, so Telegram (which counts in UTF-16 code
       units) sees each one as 2 units, while Python's len() counts each as
       a single character — this makes captions look SHORTER than they
       really are. With enough of these in a caption, this alone can push
       the real length past 1024 while the naive count still looks safe.
    These two errors don't reliably cancel out, which is why a caption could
    intermittently fail to send/edit even when it looked short enough.
    """
    plain = _HTML_TAG_RE.sub("", html_text)
    return sum(2 if ord(ch) > 0xFFFF else 1 for ch in plain)


async def send_deck_page(message, db: dict, user_id: str, page=0, edit=False, mult=1):
    actual_key, user_data = get_user_from_db(db, user_id)
    if not user_data:
        ensure_user(user_id, "User", None)
        db = load_db()
        actual_key, user_data = get_user_from_db(db, user_id)

    cards     = user_data.get("cards", {}) if isinstance(user_data, dict) else {}
    items     = list(cards.items()) if isinstance(cards, dict) else []
    user_name = user_data.get("name", "User") if isinstance(user_data, dict) else "User"

    if not items:
        text = "<b>「 COLLECTION EMPTY ぁ 」</b>\n━━━━━━━━━━━━━━━━━\nYou haven't collected any cards yet!\nWait for a drop in the group."
        if edit and isinstance(message, CallbackQuery): await message.message.edit_text(text, parse_mode=ParseMode.HTML)
        else:
            target = message.message if isinstance(message, CallbackQuery) else message
            await smart_reply(target, text, parse_mode=ParseMode.HTML)
        return

    global_cards = db.get("global_cards", {}) if isinstance(db, dict) else {}
    enriched = []
    for cid, cdata in items:
        anime = global_cards.get(cid, {}).get("anime", "Unknown") if isinstance(global_cards, dict) else "Unknown"
        enriched.append((cid, cdata, anime))

    sort_pref = user_data.get("sort_pref", "default")
    if sort_pref == "rarity":   enriched.sort(key=lambda x: (x[2], RARITY_ORDER.get(format_rarity(x[1].get("rarity", "Common")), 99)))
    elif sort_pref == "name":   enriched.sort(key=lambda x: (x[2], x[1].get("name", "").lower()))
    elif sort_pref == "amount": enriched.sort(key=lambda x: (x[2], x[1].get("amount", 1)), reverse=True)
    else:                       enriched.sort(key=lambda x: x[2])

    total_pages = max(1, math.ceil(len(enriched) / DECK_PER_PAGE))
    if page >= total_pages: page = total_pages - 1
    if page < 0:            page = 0

    start      = page * DECK_PER_PAGE
    end        = min(start + DECK_PER_PAGE, len(enriched))
    page_items = enriched[start:end]

    display_pic = None
    special_card_id = user_data.get("special_card")
    
    if special_card_id and special_card_id in cards:
        display_pic = global_cards.get(special_card_id, {}).get("file_id")
    elif enriched:
        display_pic = global_cards.get(enriched[0][0], {}).get("file_id")

    safe_name = sanitize_display_name(user_name)
    safe_name = safe_name.replace("<", "&lt;").replace(">", "&gt;")
    name_link = f'<a href="tg://user?id={user_id}">{safe_name}</a>'
    text = f"『 𝗖𝗔𝗥𝗗 𝗗𝗘𝗖𝗞 - {name_link} 』\n━━━━━━━━━━━━━━━━━\n\n"

    anime_owned_count = {}
    for _, _, a in enriched:
        anime_owned_count[a] = anime_owned_count.get(a, 0) + 1

    anime_total_count = {}
    for cdata in global_cards.values():
        a = cdata.get("anime", "Unknown")
        anime_total_count[a] = anime_total_count.get(a, 0) + 1

    current_anime = None
    for cid, cdata, anime in page_items:
        if anime != current_anime:
            if current_anime is not None: text += "\n﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌\n\n"
            obtained = anime_owned_count.get(anime, 0)
            total    = anime_total_count.get(anime, 0)
            text += f"𝗔𝗻𝗶𝗺𝗲  - <b>{anime} ↧</b>  ({obtained}/{total})\n﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌\n"
            current_anime = anime
            
        disp_rarity = format_rarity(cdata.get("rarity", "Common"))
        card_name = cdata.get("name", "Unknown")
        card_amt = cdata.get("amount", 1)
        
        if cid == special_card_id:
            text += f"✨ <b><i><code>{card_name}</code></i> - [{disp_rarity}]  ×{card_amt} </b>\n"
        else:
            text += f"✦ <b><i><code>{card_name}</code></i> - [{disp_rarity}]  ×{card_amt} </b>\n"

    if current_anime is not None: text += "\n﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌﹌\n"

    MAX_MULT  = min(25, max(2, total_pages // 3))
    show_fast = total_pages > 3
    mult      = max(1, min(mult, MAX_MULT)) if show_fast else 1

    has_prev  = page > 0
    has_next  = end < len(enriched)
    prev_page = max(0, page - mult)
    next_page = min(total_pages - 1, page + mult)

    prev_label = f"❮ {mult}x" if mult > 1 else "❮"
    next_label = f"x{mult} ❯" if mult > 1 else "❯"

    prev_btn = InlineKeyboardButton(
        text=prev_label,
        callback_data=f"deck_prev_{user_id}_{prev_page}_{mult}" if has_prev else "dedge_prev"
    )
    next_btn = InlineKeyboardButton(
        text=next_label,
        callback_data=f"deck_next_{user_id}_{next_page}_{mult}" if has_next else "dedge_next"
    )

    nav_buttons = [prev_btn]
    if show_fast:
        nav_buttons.append(InlineKeyboardButton(text="Fast ⏩", callback_data=f"deck_fast_{user_id}_{page}_{mult}"))
    nav_buttons.append(next_btn)

    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"⌈ 𝗣𝗮𝗴𝗲 {page+1}/{total_pages} ⌋", callback_data=f"page_alert_{page+1}")],
        nav_buttons,
        [
            InlineKeyboardButton(text="Collection 🫧", switch_inline_query_current_chat=f"card_user.{user_id}"),
            InlineKeyboardButton(text="🌐 Web", url=WEBDECK_APP_LINK)
        ],
        [InlineKeyboardButton(text="🗑️", callback_data=f"deckdel_{user_id}")]
    ])

    caption_too_long = caption_visible_length(text) > CAPTION_SAFE_LIMIT

    if display_pic and not caption_too_long:
        if edit and isinstance(message, CallbackQuery):
            try:
                await message.message.edit_media(InputMediaPhoto(media=display_pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=keyboard)
            except Exception as e:
                print(f"[deck] edit_media failed, falling back to text: {e}")
                try:
                    await message.message.edit_text(text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                except Exception as e2:
                    print(f"[deck] text fallback also failed: {e2}")
                    dlog.error(f"[deck] edit_media AND text fallback both failed for user {user_id}: {e2}", exc_info=True)
        else:
            target = message.message if isinstance(message, CallbackQuery) else message
            try:
                await smart_reply_photo(target, photo=display_pic, caption=text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
            except Exception as e:
                print(f"[deck] send photo with caption failed, falling back to text: {e}")
                dlog.error(f"[deck] send photo with caption failed for user {user_id}: {e}", exc_info=True)
                try:
                    await smart_reply(target, text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                except Exception as e2:
                    print(f"[deck] text fallback also failed: {e2}")
                    dlog.error(f"[deck] send photo AND text fallback both failed for user {user_id}: {e2}", exc_info=True)
    else:
        if edit and isinstance(message, CallbackQuery):
            # The message being edited may currently be a photo (from a page that
            # had a display_pic and fit under CAPTION_SAFE_LIMIT). Telegram won't
            # let edit_text touch a media message's caption — only edit_caption or
            # edit_media can — so plain edit_text intermittently fails here whenever
            # the previous page rendered as a photo. Delete + resend as plain text
            # instead, so a too-long caption never gets stuck failing to edit.
            has_media = bool(getattr(message.message, "photo", None))
            if has_media:
                try:
                    await message.message.delete()
                except Exception as e:
                    print(f"[deck] delete before text resend failed: {e}")
                    dlog.error(f"[deck] delete before text resend failed for user {user_id}: {e}", exc_info=True)
                try:
                    await smart_reply(message.message, text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                except Exception as e:
                    print(f"[deck] resend as text after delete failed: {e}")
                    dlog.error(f"[deck] resend as text after delete failed for user {user_id}: {e}", exc_info=True)
            else:
                try:
                    await message.message.edit_text(text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                except Exception as e:
                    print(f"[deck] edit_text failed: {e}")
                    dlog.error(f"[deck] edit_text failed for user {user_id}: {e}", exc_info=True)
        else:
            target = message.message if isinstance(message, CallbackQuery) else message
            await smart_reply(target, text, reply_markup=keyboard, parse_mode=ParseMode.HTML)


@main_router.message(Command("deck"))
async def view_deck_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    try:
        member = await bot.get_chat_member(config.MAIN_GROUP_USERNAME, message.from_user.id)
        if member.status in [ChatMemberStatus.LEFT, ChatMemberStatus.KICKED]:
            raise Exception("Not member")
    except Exception as e:
        print(f"[deck_access] get_chat_member failed for {message.from_user.id}: {e}")
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✦ Join Group", url=config.MAIN_GROUP_LINK)],
            [InlineKeyboardButton(text="↻ Try Again", callback_data="check_deck_access")]
        ])
        await smart_reply(message, 
            "⚠️「 𝗔𝗖𝗖𝗘𝗦𝗦 𝗗𝗘𝗡𝗜𝗘𝗗 ぁ 」\n\n"
            "🧿 𝗧𝗼 𝘃𝗶𝗲𝘄 𝘆𝗼𝘂𝗿 𝗱𝗲𝗰𝗸, "
            "𝘆𝗼𝘂 𝗺𝘂𝘀𝘁 𝗷𝗼𝗶𝗻 𝗼𝘂𝗿 𝗠𝗮𝗶𝗻 𝗚𝗿𝗼𝘂𝗽.",
            reply_markup=kb,
            parse_mode=ParseMode.HTML
        )
        return

    user_id = str(message.from_user.id)
    db      = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    await send_deck_page(message, db, user_id, page=0, edit=False)


@main_router.callback_query(F.data == "check_deck_access")
async def check_deck_access_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    try:
        member = await bot.get_chat_member(config.MAIN_GROUP_USERNAME, cq.from_user.id)
        if member.status in [ChatMemberStatus.LEFT, ChatMemberStatus.KICKED]:
            await cq.answer("You haven't joined the group yet!", show_alert=True)
            return
    except Exception as e:
        print(f"[deck_access] get_chat_member failed for {cq.from_user.id}: {e}")
        await cq.answer("You haven't joined the group yet!", show_alert=True)
        return

    await cq.message.delete()
    user_id = str(cq.from_user.id)
    db = ensure_user(user_id, cq.from_user.first_name, cq.from_user.username)
    await send_deck_page(cq, db, user_id, page=0, edit=False)
    await cq.answer("✅ Access Granted!")


@main_router.callback_query(F.data.startswith("deck_"))
async def deck_nav_cb(callback_query: CallbackQuery):
    uid_int = callback_query.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await callback_query.answer("🔇 You are currently restricted.", show_alert=True)
        return

    parts                = callback_query.data.split("_")
    direction, owner_id, page_str = parts[1], parts[2], parts[3]
    mult = int(parts[4]) if len(parts) > 4 else 1

    if str(callback_query.from_user.id) != owner_id:
        await callback_query.answer("Not your deck!", show_alert=True)
        return

    db = load_db()

    if direction == "fast":
        cards_count = len(db["users"].get(owner_id, {}).get("cards", {}))
        total_pages = max(1, math.ceil(cards_count / DECK_PER_PAGE))
        max_mult    = min(25, max(2, total_pages // 3))

        if mult >= max_mult:
            new_mult = 1
        else:
            new_mult = mult * 2 if mult >= 1 else 2
        await send_deck_page(callback_query, db, owner_id, int(page_str), edit=True, mult=new_mult)
        await callback_query.answer(f"Speed changed to {new_mult}x", show_alert=True)
        return

    await send_deck_page(callback_query, db, owner_id, int(page_str), edit=True, mult=mult)
    await callback_query.answer()


@main_router.callback_query(F.data.in_({"dedge_prev", "dedge_next"}))
async def deck_edge_cb(callback_query: CallbackQuery):
    await callback_query.answer("No more pages.", show_alert=False)


@main_router.callback_query(F.data.startswith("deckdel_"))
async def deck_delete_cb(callback_query: CallbackQuery):
    uid_int = callback_query.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await callback_query.answer("🔇 You are currently restricted.", show_alert=True)
        return

    owner_id = callback_query.data.split("deckdel_", 1)[1]
    if str(uid_int) != owner_id:
        await callback_query.answer("Only the deck owner can delete this.", show_alert=True)
        return

    try:
        await callback_query.message.delete()
    except Exception:
        pass
    await callback_query.answer()


@main_router.callback_query(F.data.startswith("page_alert_"))
async def page_indicator_alert(callback_query: CallbackQuery):
    page_num = callback_query.data.split("_")[2]
    await callback_query.answer(f"ℹ️ You are currently on page {page_num}.", show_alert=True)


@main_router.callback_query(F.data == "noop")
async def noop_cb(callback_query: CallbackQuery):
    await callback_query.answer()

# ==========================================
# /special (Spoiler + Confirmation)
# ==========================================
@main_router.message(Command("special"))
async def set_special_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(message.from_user.id)
    name    = message.from_user.first_name
    db      = ensure_user(user_id, name, message.from_user.username)

    if not command.args:
        await smart_reply(message, "⚠️ <b>Usage:</b> <code>/special <card name></code>", parse_mode=ParseMode.HTML)
        return

    query    = command.args.lower().strip()
    my_cards = db["users"][user_id].get("cards", {})

    if not my_cards:
        await smart_reply(message, "You don't own any cards yet!", parse_mode=ParseMode.HTML)
        return

    best_match = None
    best_ratio = 0.0

    for cid, cdata in my_cards.items():
        name_lower = cdata.get("name", "").lower()
        if query == name_lower:
            best_match = (cid, cdata)
            break
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)
        else:
            ratio = difflib.SequenceMatcher(None, query, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)

    if not best_match:
        await smart_reply(message, f"You do not own a card matching <b>{command.args}</b>.", parse_mode=ParseMode.HTML)
        return

    matched_cid, matched_data = best_match
    global_data    = db["global_cards"].get(matched_cid, {})
    display_rarity = format_rarity(matched_data.get("rarity", "Common"))

    caption = (
        f"<b>「 SET SPECIAL CARD ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"⤿ Are you sure you want to set <b>{matched_data.get('name', 'Card')}「 {display_rarity}」</b> this as your <b>Special Card?</b>"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Yes, Set Special", callback_data=f"setsp_{user_id}_{matched_cid}")],
        [InlineKeyboardButton(text="Cancel", callback_data=f"cancel_action_{user_id}")]
    ])
    await smart_reply_photo(message, 
        photo=global_data.get("file_id"), caption=caption,
        reply_markup=kb, parse_mode=ParseMode.HTML, has_spoiler=True
    )


@main_router.callback_query(F.data.startswith("setsp_"))
async def confirm_special_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return

    parts   = cq.data.split("_", 2)
    owner_id = parts[1]
    card_id = parts[2]
    user_id = str(cq.from_user.id)

    if user_id != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    db = load_db()
    actual_key, user_data = get_user_from_db(db, user_id)

    if not user_data or card_id not in user_data.get("cards", {}):
        await cq.answer("You don't own this card anymore!", show_alert=True)
        return

    user_data["special_card"] = card_id
    save_db()

    cdata          = user_data["cards"][card_id]
    display_rarity = format_rarity(cdata.get("rarity", "Common"))
    caption = (
        "<b>「 SPECIAL CARD SET ぁ 」\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"Character : </b>{cdata.get('name', 'Card')}\n"
        f"<b>Rarity :</b> {display_rarity}\n\n"
        "<blockquote><b>✨ Pinned to the top of your deck!</b></blockquote>"
    )
    await cq.message.edit_caption(caption=caption, parse_mode=ParseMode.HTML, reply_markup=None)
    await cq.answer("✅ Special card updated!")


# ==========================================
# /flex SHOWCASE COMMAND
# ==========================================
@main_router.message(Command("flex"))
async def flex_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)
    db      = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    if not command.args:
        await message.reply("⚠️ <b>Usage:</b> <code>/flex &lt;card name&gt;</code>", parse_mode=ParseMode.HTML)
        return

    query    = command.args.lower().strip()
    my_cards = db["users"][user_id].get("cards", {})

    if not my_cards:
        await message.reply("You don't own any cards to flex!", parse_mode=ParseMode.HTML)
        return

    best_match = None
    best_ratio = 0.0

    for cid, cdata in my_cards.items():
        name_lower = cdata.get("name", "").lower()
        if query == name_lower:
            best_match = (cid, cdata)
            break
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)
        else:
            ratio = difflib.SequenceMatcher(None, query, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)

    if not best_match:
        await message.reply(f"You do not own a card matching <b>{command.args}</b>.", parse_mode=ParseMode.HTML)
        return

    matched_cid, matched_data = best_match
    global_data    = db["global_cards"].get(matched_cid, {})
    display_rarity = format_rarity(matched_data.get("rarity", "Common"))

    safe_name = str(message.from_user.first_name).replace("<", "&lt;").replace(">", "&gt;")
    mention = f'<a href="tg://user?id={user_id}">{safe_name}</a>'
    
    caption = (
        f"<i><b>Ooooh! Check out {mention}'s card!</b></i>\n\n"
        f"<b>⦿ <i>Character </i>» {matched_data.get('name', 'Card')} ⟪ {global_data.get('anime', 'Unknown')} ⟫ \n"
        f"⦾ <i>Rarity </i>» {display_rarity}\n"
        f"⬤ <i>Owned</i>  » x{matched_data.get('amount', 1)}</b>"
    )

    try:
        await message.reply_photo(
            photo=global_data.get("file_id"),
            caption=caption,
            parse_mode=ParseMode.HTML
        )
    except Exception:
        await message.reply(caption, parse_mode=ParseMode.HTML)


# ==========================================
# CARD BURNING RECYCLING SYSTEM (/burn)
# ==========================================
@main_router.message(Command("burn"))
async def burn_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    if not command.args:
        await smart_reply(message, "⚠️ <b>Usage:</b> <code>/burn &lt;card name&gt;</code>\nExample: <code>/burn naruto</code>", parse_mode=ParseMode.HTML)
        return

    query    = command.args.lower().strip()
    my_cards = db["users"][user_id].get("cards", {})

    if not my_cards:
        await smart_reply(message, "You do not own any cards to burn.", parse_mode=ParseMode.HTML)
        return

    best_match = None
    best_ratio = 0.0

    for cid, cdata in my_cards.items():
        if cdata.get("amount", 0) <= 0: continue
        name_lower = cdata.get("name", "").lower()
        if query == name_lower:
            best_match = (cid, cdata)
            break
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)
        else:
            ratio = difflib.SequenceMatcher(None, query, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)

    if not best_match:
        await smart_reply(message, f"You do not own any cards matching <b>{command.args}</b>.", parse_mode=ParseMode.HTML)
        return

    matched_cid, matched_data = best_match
    global_data       = db["global_cards"].get(matched_cid, {})
    rarity_normalized = format_rarity(matched_data.get("rarity", "Common"))

    burn_payout = 150
    if rarity_normalized == "Elite ⚓":   burn_payout = 450
    elif rarity_normalized == "Divine ❄️": burn_payout = 1800

    caption = (
        f"<b>「 🔥 BURN CONFIRMATION 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"⚠️ <b>WARNING:</b> This card will be permanently destroyed!\n\n"
        f"👤 Character ➜ <b>{matched_data.get('name', 'Card')}</b>\n"
        f"🌟 Rarity    ➜ <b>{rarity_normalized}</b>\n"
        f"💠 Returns   ➜ <b>+{burn_payout} Shards</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<i>Are you sure you want to proceed? This action is irreversible.</i>"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔥 Confirm Destruction", callback_data=f"cfburn_{user_id}_{matched_cid}")],
        [InlineKeyboardButton(text="Cancel", callback_data=f"cancel_action_{user_id}")]
    ])
    await smart_reply_photo(message, photo=global_data.get("file_id"), caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("cfburn_"))
async def confirm_burn_cb(cq: CallbackQuery):
    parts = cq.data.split("_", 2)
    uid   = parts[1]
    card_id = parts[2]

    if str(cq.from_user.id) != uid:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    if _check_action_cooldown(f"burn_{uid}"):
        await cq.answer("⏳ Please wait a moment before burning again.", show_alert=True)
        return

    db = load_db()
    actual_key, user_data = get_user_from_db(db, uid)

    if not user_data or card_id not in user_data.get("cards", {}) or user_data["cards"][card_id].get("amount", 0) <= 0:
        await cq.answer("You don't own this card anymore!", show_alert=True)
        return

    my_cards = user_data["cards"]
    card_data = my_cards[card_id]
    rarity_normalized = format_rarity(card_data.get("rarity", "Common"))

    burn_payout = 150
    if rarity_normalized == "Elite ⚓":   burn_payout = 450
    elif rarity_normalized == "Divine ❄️": burn_payout = 1800

    my_cards[card_id]["amount"] -= 1
    if my_cards[card_id]["amount"] <= 0:
        del my_cards[card_id]
        if user_data.get("special_card") == card_id:
            user_data["special_card"] = None

    user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + burn_payout

    log_action(db, str(actual_key), {
        "type": "burn", "card_name": card_data.get("name", "Card"), "rarity": rarity_normalized,
        "shards_earned": burn_payout,
        "chat_id": cq.message.chat.id, "chat_title": cq.message.chat.title or "Private DM",
    })
    save_db()

    caption = (
        f"<b>「 🔥 CARD INCINERATED 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"Card: <b>{card_data.get('name', 'Card')}</b> [{rarity_normalized}]\n"
        f"Action: Destroyed and recycled.\n\n"
        f"💰 Earned: <b>+{burn_payout} Nexus Shards</b> 💠"
    )
    await cq.message.edit_caption(caption=caption, parse_mode=ParseMode.HTML, reply_markup=None)
    await cq.answer("🔥 Card burned successfully!")
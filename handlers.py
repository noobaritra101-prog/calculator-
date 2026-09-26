import math
import time
import uuid
import random
import asyncio
import difflib
import unicodedata
from datetime import datetime, timezone, timedelta
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery, InlineQuery,
    InlineKeyboardMarkup, InlineKeyboardButton,
    CopyTextButton, WebAppInfo,
    InlineQueryResultPhoto, InlineQueryResultCachedPhoto, InlineQueryResultArticle,
    InputTextMessageContent, BufferedInputFile, InputMediaPhoto, ReactionTypeEmoji,
    FSInputFile
)
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ChatType, ChatMemberStatus
from aiogram.exceptions import TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest

import config
from config import (
    bot, main_router, ADMIN_IDS, DECK_PER_PAGE, CARDS_PER_PAGE, BROWSE_PER_PAGE,
    group_counters, active_drops, bot_start_time, spoiler_cache, RARITIES,
    RARITY_ORDER, RARITY_SAFE, SAFE_RARITY, format_rarity, load_db, save_db,
    ensure_user, ensure_group, get_mention, is_ghost_banned, is_shadow_banned,
    format_wait_mmss, QUERY_GROUP_ID, get_query_daily_tracker
)
from vlog import log_action

# Top-level import (not deferred) so its @main_router commands
# (/ab, /rb, /lbanner, /set_default, /mybanners) register as soon as
# banners.py loads at startup — not only after the first /profile call.
import banners

# In-memory mining tracking dictionary to prevent spam farming
user_mine_cooldowns = {}

# Per-user cooldown dict for burn/gift to prevent rapid double-executions
_action_cooldowns: dict[str, float] = {}
ACTION_COOLDOWN_SECS = 8

# # Gifting limit configuration
GIFT_COOLDOWN = 300           # 5-minute cooldown between gifts for regular users
DAILY_GIFT_SEND_LIMIT = 3     # Maximum cards a user can send per day
DAILY_GIFT_RECEIVE_LIMIT = 3  # Maximum cards a user can receive per day
_gift_cooldowns: dict[str, float] = {}

# Shards transfer cooldown tracking
_sgive_cooldowns: dict[str, float] = {}
SGIVE_COOLDOWN_SECS = 300   # seconds between transfers for regular users (5 min)
SGIVE_MIN_AMOUNT    = 10    # minimum shards per transfer
SGIVE_MAX_AMOUNT    = 15000 # maximum shards per transfer

# ==========================================
# /qry SUPPORT-TICKET SYSTEM CONFIGURATION
# ==========================================
_query_cooldowns: dict[str, float] = {}
QUERY_COOLDOWN_SECS = 90     # seconds between submissions for regular users
QUERY_DAILY_LIMIT   = 5      # max queries a user can submit per day
QUERY_MAX_PENDING   = 3      # max unanswered queries a user can have open at once
QUERY_MIN_LEN       = 5      # minimum characters in a query
QUERY_MAX_LEN       = 800    # maximum characters in a query

# ==========================================
# /trade STATE & CONFIGURATION
# ==========================================
# In-memory pending trade offers: trade_id -> offer details.
# Not persisted to disk — a restart simply drops any offers still in flight,
# which is fine since nothing has moved between inventories yet at that point.
active_trades: dict[str, dict] = {}
TRADE_EXPIRY_SECS  = 300   # Unanswered offers auto-expire after 5 minutes
TRADE_COOLDOWN_SECS = 60   # 1 minute cooldown between trade offers (per initiator)
_trade_cooldowns: dict[str, float] = {}

# Basic 🃏 <-> Basic/Elite, Elite ⚓ <-> Basic/Elite, Divine ❄️ <-> Divine only
def _trade_rarities_compatible(rarity_a: str, rarity_b: str) -> bool:
    if rarity_a == "Divine ❄️" or rarity_b == "Divine ❄️":
        return rarity_a == "Divine ❄️" and rarity_b == "Divine ❄️"
    return True


def _check_action_cooldown(uid: str) -> bool:
    """Returns True if user is on cooldown (should block), False if allowed."""
    now = time.time()
    last = _action_cooldowns.get(uid, 0)
    if now - last < ACTION_COOLDOWN_SECS:
        return True
    _action_cooldowns[uid] = now
    return False


# ==========================================
# CHAT-AWARE RESPONSE HELPERS
# In groups: reply (quoted) to the user's command.
# In DMs: plain answer, no quote banner.
# ==========================================
async def smart_reply(message: Message, *args, **kwargs):
    if message.chat.type == ChatType.PRIVATE:
        return await message.answer(*args, **kwargs)
    return await message.reply(*args, **kwargs)


async def smart_reply_photo(message: Message, *args, **kwargs):
    if message.chat.type == ChatType.PRIVATE:
        return await message.answer_photo(*args, **kwargs)
    return await message.reply_photo(*args, **kwargs)


async def has_bot_in_bio(user_id: int) -> bool:
    try:
        bot_info = await bot.get_me()
        bot_username = f"@{bot_info.username}".lower()
        user_chat = await bot.get_chat(user_id)
        if user_chat.bio:
            return bot_username in user_chat.bio.lower()
    except Exception:
        pass
    return False

# ==========================================
# ANTI-CHEAT REFERRAL CONVERSION ENGINE
# ==========================================
async def check_and_reward_referral(user_id: str, db: dict):
    user_data = db["users"].get(user_id)
    if not user_data: return

    referrer_id = user_data.get("referred_by")
    if not referrer_id or user_data.get("referral_rewarded", False):
        return

    total_cards = sum(c.get("amount", 0) for c in user_data.get("cards", {}).values())
    if total_cards < 1:
        return

    # Mark as rewarded immediately to prevent double-payout
    user_data["referral_rewarded"] = True
    ensure_user(referrer_id, "User")

    db["users"][referrer_id]["nexus_shards"] = db["users"][referrer_id].get("nexus_shards", 0) + 100
    db["users"][user_id]["nexus_shards"]     = db["users"][user_id].get("nexus_shards", 0) + 50

    referrals = db["users"][referrer_id].setdefault("referrals", [])
    if user_id not in referrals:
        referrals.append(user_id)

    ref_count     = len(referrals)
    milestone_msg = ""

    def _give_card(rarity_filter):
        locked_animes = db.get("settings", {}).get("locked_animes", [])
        locked_animes_lower = [a.lower().strip() for a in locked_animes]

        pool = {k: v for k, v in db["global_cards"].items() 
                if format_rarity(v["rarity"]) == rarity_filter
                and v["anime"].lower().strip() not in locked_animes_lower}
                
        if pool:
            cid, cdata = random.choice(list(pool.items()))
            db["users"][referrer_id].setdefault("cards", {}).setdefault(
                cid, {"name": cdata["name"], "rarity": cdata["rarity"], "amount": 0}
            )["amount"] += 1
            return cdata
        return None

    if ref_count == 5:
        db["users"][referrer_id]["nexus_shards"] += 200
        card = _give_card("Basic 🃏")
        if card:
            milestone_msg = f"\n🎉 <b>5 Referrals Milestone!</b>\n🎁 Earned: 1x Basic card (<b>{card['name']}</b>) &amp; <b>+200 Shards</b>!"
    elif ref_count == 10:
        db["users"][referrer_id]["nexus_shards"] += 500
        card = _give_card("Elite ⚓")
        if card:
            milestone_msg = f"\n🎉 <b>10 Referrals Milestone!</b>\n🎁 Earned: 1x Elite card (<b>{card['name']}</b>) &amp; <b>+500 Shards</b>!"
    elif ref_count == 20:
        db["users"][referrer_id]["nexus_shards"] += 1500
        card = _give_card("Divine ❄️")
        if card:
            milestone_msg = f"\n🎉 <b>20 Referrals Milestone!</b>\n🎁 Earned: 1x Divine card (<b>{card['name']}</b>) &amp; <b>+1,500 Shards</b>!"
    elif ref_count > 20 and (ref_count - 20) % 20 == 0:
        db["users"][referrer_id]["nexus_shards"] += 2000
        card = _give_card("Divine ❄️")
        if card:
            milestone_msg = f"\n🎉 <b>+{ref_count} Referrals Milestone Loop!</b>\n🎁 Earned: 1x Divine card (<b>{card['name']}</b>) &amp; <b>+2,000 Shards</b>!"

    save_db()

    try:
        referred_name    = db["users"][user_id].get("name", "User")
        referred_mention = get_mention(user_id, referred_name)
        referrer_alert = (
            f"<b>「 👥 REFERRAL CONVERTED! 」</b>\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"👤 {referred_mention} seized their first card and became active!\n"
            f"🎁 Awarded: <b>+100 Shards</b>\n"
            f"📊 Successful Referrals: <b>{ref_count}</b>"
            f"{milestone_msg}"
        )
        await bot.send_message(chat_id=int(referrer_id), text=referrer_alert, parse_mode=ParseMode.HTML)
    except Exception:
        pass

    try:
        await bot.send_message(
            chat_id=int(user_id),
            text="<b>「 🎉 REFERRAL BONUS ACTIVATED! 」</b>\n━━━━━━━━━━━━━━━━━\n"
                 "You claimed your first card! Your referral link is now active.\n"
                 "🎁 Awarded: <b>+50 welcome Shards!</b>",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass


# ==========================================
# DAILY REWARDS CLAIM SYSTEM (/daily)
# ==========================================
_daily_locks: dict[str, asyncio.Lock] = {}

@main_router.message(Command("daily"))
async def daily_reward_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)

    # Serialize per-user so rapid-fire /daily spam can't slip multiple
    # claims through before last_daily is saved — has_bot_in_bio() below
    # awaits a Telegram call, which yields control long enough for a second
    # /daily to sneak past the "already claimed today?" check otherwise.
    lock = _daily_locks.setdefault(user_id, asyncio.Lock())
    if lock.locked():
        return
    async with lock:
        db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

        now_dt     = datetime.now(timezone.utc)
        today_date = now_dt.date()
        last_claim = db["users"][user_id].get("last_daily", 0)
        last_date  = datetime.fromtimestamp(last_claim, tz=timezone.utc).date() if last_claim else None

        if last_date == today_date:
            tomorrow_midnight = datetime.combine(today_date, datetime.min.time(), tzinfo=timezone.utc) + timedelta(days=1)
            rem  = int((tomorrow_midnight - now_dt).total_seconds())
            h, r = divmod(rem, 3600)
            m, _ = divmod(r, 60)
            await message.reply(f"⏳ <b>Daily already claimed!</b>\nResets at midnight UTC — return in <b>{h}h {m}m</b>.", parse_mode=ParseMode.HTML)
            return

        # Mark claimed and save BEFORE the bio-bonus check below, which awaits
        # a Telegram API call — closing the race at its source, not just
        # relying on the lock (a restart mid-await would otherwise still let
        # a second process claim before this save happened).
        db["users"][user_id]["last_daily"] = int(now_dt.timestamp())
        save_db()

        bio_bonus    = await has_bot_in_bio(uid_int)
        base_reward  = 150
        bonus_reward = 150 if bio_bonus else 0
        total_reward = base_reward + bonus_reward

        db["users"][user_id]["nexus_shards"] = db["users"][user_id].get("nexus_shards", 0) + total_reward
        save_db()

        msg = (
            "<b>「 💠 DAILY SHARDS CLAIMED ぁ 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            f"٠࣪⭑ Daily Reward  <b>+{base_reward} Shards</b>\n"
        )
        if bio_bonus:
            msg += f"⟡ ݁₊ . Bio Bonus  <b>+{bonus_reward} Shards</b> (Bot username verified!)\n"
        else:
            msg += "💡 <i>Tip: Put our bot username in your profile Bio for an extra +100 Shards daily!</i>\n"
        msg += f"━━━━━━━━━━━━━━━━━\n── Total Claimed <b>+{total_reward} Shards 💠</b>"
        await message.reply(msg, parse_mode=ParseMode.HTML)


# ==========================================
# WEEKLY REWARDS CLAIM SYSTEM (/weekly)
# ==========================================
_weekly_locks: dict[str, asyncio.Lock] = {}

@main_router.message(Command("weekly"))
async def weekly_reward_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)

    # Serialize per-user so rapid-fire /weekly spam can't slip multiple
    # claims through before the cooldown timestamp is saved.
    lock = _weekly_locks.setdefault(user_id, asyncio.Lock())
    if lock.locked():
        return
    async with lock:
        db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

        now       = int(time.time())
        last_claim = db["users"][user_id].get("last_weekly", 0)
        cooldown  = 7 * 24 * 3600

        if now - last_claim < cooldown:
            rem  = cooldown - (now - last_claim)
            d, r = divmod(rem, 86400)
            h, r = divmod(r, 3600)
            m, _ = divmod(r, 60)
            await message.reply(f"⏳ <b>Weekly already claimed!</b>\nReturn in <b>{d}d {h}h {m}m</b> to claim again.", parse_mode=ParseMode.HTML)
            return

        valid_rarities = ["Basic 🃏", "Elite ⚓"]
        locked_animes = db.get("settings", {}).get("locked_animes", [])
        locked_animes_lower = [a.lower().strip() for a in locked_animes]

        tier_pool = {k: v for k, v in db.get("global_cards", {}).items()
                     if format_rarity(v["rarity"]) in valid_rarities
                     and v["anime"].lower().strip() not in locked_animes_lower}

        if not tier_pool:
            await message.reply("Weekly reward system is temporarily unavailable because no unlocked Basic or Elite cards are currently registered in the database.", parse_mode=ParseMode.HTML)
            return

        card_id, card_data = random.choice(list(tier_pool.items()))

        bio_bonus    = await has_bot_in_bio(uid_int)
        base_reward  = 500
        bonus_reward = 300 if bio_bonus else 0
        total_reward = base_reward + bonus_reward

        db["users"][user_id]["nexus_shards"] = db["users"][user_id].get("nexus_shards", 0) + total_reward
        db["users"][user_id]["last_weekly"]  = now

        user_cards = db["users"][user_id].setdefault("cards", {})
        if card_id not in user_cards:
            user_cards[card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
        user_cards[card_id]["amount"] += 1
        db["users"][user_id]["total_claimed"] = db["users"][user_id].get("total_claimed", 0) + 1
        save_db()

        log_action(db, user_id, {
            "type": "weekly_claim",
            "amount": total_reward,
            "bio_bonus": bio_bonus,
            "chat_id": message.chat.id,
            "chat_title": message.chat.title or message.chat.first_name or "DM"
        })

        display_rarity = format_rarity(card_data["rarity"])
        bonus_line = f" +{bonus_reward} Shards" if bio_bonus else " "
        msg = (
            "<b>「 💠 WEEKLY CLAIM REWARDS ぁ 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            f"<b>Card :</b> {card_data['name']}<b>〔{display_rarity}〕</b>\n"
            f"<b>Anime : </b> {card_data.get('anime', 'Unknown')}\n"
            f"<b>Base Shards : </b> +{base_reward} Shards 💠[<b>Bio Bonus:</b>{bonus_line}]\n"
        )
        if not bio_bonus:
            msg += f"<b>Note : </b> Add bot Usernames (@Animenx_bot) to your Bio To get Bonus .\n"
        msg += (
            "━━━━━━━━━━━━━━━━━\n"
            f"<blockquote><b>Total Balance </b>: {db['users'][user_id]['nexus_shards']} Shards 💠</blockquote>"
        )
        try:
            await message.reply_photo(photo=card_data["file_id"], caption=msg, parse_mode=ParseMode.HTML, has_spoiler=True)
        except Exception:
            await message.reply(msg, parse_mode=ParseMode.HTML)


# ==========================================
# 10-ROLL BOWLING SYSTEM COMMAND (/roll)
# ==========================================
@main_router.message(Command("roll"))
async def bowling_roll_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id   = str(uid_int)
    db        = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    user_data = db["users"][user_id]
    now       = int(time.time())

    if user_data.get("roll_reset", 0) != 0 and now >= user_data.get("roll_reset", 0):
        user_data["roll_count"] = 0
        user_data["roll_reset"] = 0

    if user_data.get("roll_count", 0) >= 10:
        rem  = user_data["roll_reset"] - now
        h, r = divmod(rem, 3600)
        m, _ = divmod(r, 60)
        await message.reply(
            f"⏳ <b>Out of rolls!</b>\n━━━━━━━━━━━━━━━━━\n"
            f"Your pins are resetting.\nReturn in <b>{h}h {m}m</b>.",
            parse_mode=ParseMode.HTML
        )
        return

    if user_data.get("roll_count", 0) == 0:
        user_data["roll_reset"] = now + (8 * 3600)

    user_data["roll_count"] += 1
    rolls_left = 10 - user_data["roll_count"]
    # Save the spent roll immediately, before any Telegram call that could
    # fail (flood control, missing send rights, etc.). Previously this only
    # saved at the very end, so a failed/unhandled send meant the roll was
    # never actually deducted — letting a user retry for free and hammer
    # the same flood-controlled chat over and over.
    save_db()

    try:
        dice_msg = await message.answer_dice(emoji="🎳")
    except (TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest):
        return
    await asyncio.sleep(4)

    shards_won = 0
    if dice_msg.dice.value == 6:
        shards_won = random.randint(40, 60)
        user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + shards_won

    save_db()

    if shards_won:
        log_action(db, user_id, {
            "type": "bowling_win",
            "amount": shards_won,
            "chat_id": message.chat.id,
            "chat_title": message.chat.title or message.chat.first_name or "DM"
        })

    try:
        if shards_won:
            await message.reply(
                f"<b>「 STRIKE! ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
                f"🎉 You knocked down all the pins!\n"
                f"💠 Earned: <b>{shards_won} Shards</b>\n"
                f"🎳 Rolls left: <b>{rolls_left}/10</b>",
                parse_mode=ParseMode.HTML
            )
        else:
            await message.reply(
                f"<b>「 MISS ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
                f"You didn't clear the pins. Keep trying!\n"
                f"🎳 Rolls left: <b>{rolls_left}/10</b>",
                parse_mode=ParseMode.HTML
            )
    except (TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest):
        pass


# ==========================================
# 10-THROW BASKETBALL SYSTEM COMMAND (/throw)
# ==========================================
@main_router.message(Command("throw"))
async def basketball_throw_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id   = str(uid_int)
    db        = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    user_data = db["users"][user_id]
    now       = int(time.time())

    if user_data.get("throw_reset", 0) != 0 and now >= user_data.get("throw_reset", 0):
        user_data["throw_count"] = 0
        user_data["throw_reset"] = 0

    if user_data.get("throw_count", 0) >= 10:
        rem  = user_data["throw_reset"] - now
        h, r = divmod(rem, 3600)
        m, _ = divmod(r, 60)
        await message.reply(
            f"⏳ <b>Out of stamina!</b>\n━━━━━━━━━━━━━━━━━\n"
            f"You need to rest your arms.\nReturn in <b>{h}h {m}m</b>.",
            parse_mode=ParseMode.HTML
        )
        return

    if user_data.get("throw_count", 0) == 0:
        user_data["throw_reset"] = now + (8 * 3600)

    user_data["throw_count"] += 1
    throws_left = 10 - user_data["throw_count"]
    # See bowling_roll_cmd — save the spent throw immediately, before any
    # Telegram call that could fail (flood control, missing send rights,
    # etc.), so a failed send can't be retried for free.
    save_db()

    try:
        dice_msg = await message.answer_dice(emoji="🏀")
    except (TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest):
        return
    await asyncio.sleep(4)

    shards_won = 0
    if dice_msg.dice.value >= 4:
        shards_won = random.randint(40, 60)
        user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + shards_won

    save_db()

    if shards_won:
        log_action(db, user_id, {
            "type": "basketball_win",
            "amount": shards_won,
            "chat_id": message.chat.id,
            "chat_title": message.chat.title or message.chat.first_name or "DM"
        })

    try:
        if shards_won:
            await message.reply(
                f"<b>「 SWISH! ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
                f"🎉 Nothing but net!\n"
                f"💠 Earned: <b>{shards_won} Shards</b>\n"
                f"🏀 Throws left: <b>{throws_left}/10</b>",
                parse_mode=ParseMode.HTML
            )
        else:
            await message.reply(
                f"<b>「 MISS ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n"
                f"You missed the shot. Keep practicing!\n"
                f"🏀 Throws left: <b>{throws_left}/10</b>",
                parse_mode=ParseMode.HTML
            )
    except (TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest):
        pass


# ==========================================
# SHARDS TRANSFER SYSTEM (/sgive)
# ==========================================
@main_router.message(Command("sgive"))
async def sgive_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    sender_id = str(uid_int)
    sender_name = message.from_user.first_name

    # Cooldown check for regular users to prevent double-spending/rapid spam
    now = time.time()
    if uid_int not in ADMIN_IDS:
        last_sgive = _sgive_cooldowns.get(sender_id, 0)
        if now - last_sgive < SGIVE_COOLDOWN_SECS:
            rem = int(SGIVE_COOLDOWN_SECS - (now - last_sgive))
            await message.reply(f"⏳ <b>Transfer cooldown active!</b>\nPlease wait <b>{format_wait_mmss(rem)}</b>.", parse_mode=ParseMode.HTML)
            return

    if not command.args:
        await message.reply("<b>Usage:</b> Reply to a user with <code>/sgive &lt;amount&gt;</code>", parse_mode=ParseMode.HTML)
        return

    args = command.args.split()
    target_id = None
    target_name = "User"
    amount_str = ""

    # Check if replying to a message
    if message.reply_to_message and message.reply_to_message.sender_chat:
        # Message was posted by a channel (e.g. an anonymous admin posting
        # "as the channel", or a linked-channel post) — there's no real user
        # account behind it to credit shards to.
        await message.reply("You cannot transfer shards to a channel.", parse_mode=ParseMode.HTML)
        return

    if message.reply_to_message and message.reply_to_message.from_user:
        if message.reply_to_message.from_user.is_bot:
            await message.reply("You cannot transfer shards to a bot.", parse_mode=ParseMode.HTML)
            return
        target_id = str(message.reply_to_message.from_user.id)
        target_name = message.reply_to_message.from_user.first_name
        amount_str = args[0]
    else:
        await message.reply("<b>Usage:</b> Reply to a user with <code>/sgive &lt;amount&gt;</code>", parse_mode=ParseMode.HTML)
        return

    if not target_id:
        await message.reply("Could not resolve target user.", parse_mode=ParseMode.HTML)
        return

    if target_id == sender_id:
        await message.reply("You cannot transfer shards to yourself.", parse_mode=ParseMode.HTML)
        return

    try:
        amount = int(amount_str)
        if amount <= 0:
            raise ValueError()
    except ValueError:
        await message.reply("Amount must be a valid positive integer.", parse_mode=ParseMode.HTML)
        return

    if amount < SGIVE_MIN_AMOUNT:
        await message.reply(f"Minimum transfer amount is <b>{SGIVE_MIN_AMOUNT:,}</b> 💠.", parse_mode=ParseMode.HTML)
        return

    if amount > SGIVE_MAX_AMOUNT:
        await message.reply(f"Maximum transfer amount is <b>{SGIVE_MAX_AMOUNT:,}</b> 💠 per transfer.", parse_mode=ParseMode.HTML)
        return

    db = ensure_user(sender_id, sender_name, message.from_user.username)
    db = ensure_user(target_id, target_name)

    sender_bal = db["users"][sender_id].get("nexus_shards", 0)
    if sender_bal < amount:
        await message.reply(f"You do not have enough shards. Your balance: <b>{sender_bal:,}</b> 💠", parse_mode=ParseMode.HTML)
        return

    # ── Execute transfer ──────────────────────────────────────────────────────
    db["users"][sender_id]["nexus_shards"] = sender_bal - amount
    db["users"][target_id]["nexus_shards"] = db["users"][target_id].get("nexus_shards", 0) + amount

    chat_title = message.chat.title or "Private DM"
    log_action(db, sender_id, {
        "type": "sgive_sent", "amount": amount,
        "cp_id": target_id, "cp_name": target_name,
        "chat_id": message.chat.id, "chat_title": chat_title,
    })
    log_action(db, target_id, {
        "type": "sgive_received", "amount": amount,
        "cp_id": sender_id, "cp_name": sender_name,
        "chat_id": message.chat.id, "chat_title": chat_title,
    })
    save_db()

    # Update cooldown state
    _sgive_cooldowns[sender_id] = now

    target_mention = get_mention(target_id, target_name)
    sender_mention = get_mention(sender_id, sender_name)

    # ── Public Transfer Log ───────────────────────────────────────────────────
    log_text = (
        "↑↓ <b>SHARD TRANSFERRED</b>\n\n"
        f"<b>FROM:</b> {sender_id}\n"
        f"<b>TO:</b> {target_id}\n"
        f"<b>AMOUNT:</b> {amount:,} Shards 💠"
    )
    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=log_text,
            message_thread_id=config.LOG_THREAD_TRANSFER,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[LOG] Failed to send public transfer log to Topic {config.LOG_THREAD_TRANSFER}: {e}")

    # ── Public confirmation ───────────────────────────────────────────────────
    confirm_text = f"You gave <b>{amount:,} Shards 💠</b> to {target_mention}"
    await message.reply(confirm_text, parse_mode=ParseMode.HTML)
    

# ==========================================
# /setspawn - MESSAGE THRESHOLD CONFIG
# ==========================================
@main_router.message(Command("setspawn"))
async def set_spawn_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if message.chat.type not in [ChatType.GROUP, ChatType.SUPERGROUP]:
        await message.reply("This command can only be used in groups.")
        return

    member = await bot.get_chat_member(message.chat.id, message.from_user.id)
    if member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR] and message.from_user.id not in ADMIN_IDS:
        await message.reply("Only group admins can use this command.")
        return

    db  = ensure_group(message.chat.id, message.chat.title)
    cid = str(message.chat.id)
    s_min = db["groups"][cid].get("spawn_min", 100)
    s_max = db["groups"][cid].get("spawn_max", 110)

    if command.args and "-" in command.args:
        parts = command.args.split("-")
        try:
            new_min = int(parts[0].strip())
            new_max = int(parts[1].strip())
            if new_min >= 100 and new_max <= 500 and new_min < new_max:
                s_min = new_min
                s_max = new_max
                db["groups"][cid]["spawn_min"] = s_min
                db["groups"][cid]["spawn_max"] = s_max
                save_db()
                config.group_counters[cid] = {"count": 0, "target": random.randint(s_min, s_max)}
            else:
                await message.reply("Invalid ranges! Minimum is 100, maximum is 500, and min must be less than max.")
                return
        except ValueError:
            pass

    text = (
        "<b>⚙️ Spawn Configuration</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"📉 <b>Min messages</b> - <code>{s_min}</code>\n"
        f"📈 <b>Max messages</b> - <code>{s_max}</code>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<i>Rules: Min 100, Max 500. Min must be &lt; Max.</i>"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="➖ Min -10", callback_data=f"spbtn_min_sub_{cid}"),
            InlineKeyboardButton(text="➕ Min +10", callback_data=f"spbtn_min_add_{cid}")
        ],
        [
            InlineKeyboardButton(text="➖ Max -10", callback_data=f"spbtn_max_sub_{cid}"),
            InlineKeyboardButton(text="➕ Max +10", callback_data=f"spbtn_max_add_{cid}")
        ],
        [InlineKeyboardButton(text="✅ Save & Close", callback_data=f"spbtn_save_none_{cid}")]
    ])
    await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("spbtn_"))
async def spawn_config_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return

    parts       = cq.data.split("_")
    action_type = parts[1]
    op          = parts[2]
    cid         = "_".join(parts[3:])

    member = await bot.get_chat_member(int(cid), cq.from_user.id)
    if member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR] and cq.from_user.id not in ADMIN_IDS:
        await cq.answer("Only group admins can adjust this.", show_alert=True)
        return

    if action_type == "save":
        try:
            await cq.message.delete()
        except Exception:
            pass
        await cq.answer("✅ Spawn settings saved!", show_alert=True)
        return

    db = load_db()
    if cid not in db["groups"]: return

    s_min = db["groups"][cid].get("spawn_min", 100)
    s_max = db["groups"][cid].get("spawn_max", 110)
    current_min = s_min
    current_max = s_max

    if action_type == "min":
        if op == "sub": s_min -= 10
        elif op == "add": s_min += 10
    elif action_type == "max":
        if op == "sub": s_max -= 10
        elif op == "add": s_max += 10

    if s_min < 100: s_min = 100
    if s_max > 500: s_max = 500
    if s_min >= s_max:
        if action_type == "min": s_min = s_max - 10
        if action_type == "max": s_max = s_min + 10
    if s_min < 100: s_min = 100

    if s_min == current_min and s_max == current_max:
        await cq.answer("Limit reached!", show_alert=False)
        return

    db["groups"][cid]["spawn_min"] = s_min
    db["groups"][cid]["spawn_max"] = s_max
    save_db()
    config.group_counters[cid] = {"count": 0, "target": random.randint(s_min, s_max)}

    text = (
        "<b>⚙️ Spawn Configuration</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"📉 <b>Min messages</b> - <code>{s_min}</code>\n"
        f"📈 <b>Max messages</b> - <code>{s_max}</code>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<i>Rules: Min 100, Max 500. Min must be &lt; Max.</i>"
    )
    await cq.message.edit_text(text, reply_markup=cq.message.reply_markup, parse_mode=ParseMode.HTML)
    await cq.answer()


async def expire_drop(chat_id: str, msg_id: int):
    await asyncio.sleep(600)
    if chat_id in active_drops and active_drops[chat_id].get("message_id") == msg_id:
        del active_drops[chat_id]
        try:
            await bot.delete_message(chat_id=int(chat_id), message_id=msg_id)
        except Exception:
            pass


async def trigger_drop(chat_id: int):
    db = load_db()
    if not db["global_cards"]: return

    # Check for locked anime parameters from Settings DB
    locked_animes = db.get("settings", {}).get("locked_animes", [])
    locked_animes_lower = [a.lower().strip() for a in locked_animes]

    roll = random.randint(1, 100)
    if roll <= 78:   target_rarity = "Basic 🃏"    # 78%
    elif roll <= 98: target_rarity = "Elite ⚓"    # 20%
    else:            target_rarity = "Divine ❄️"  # 2%

    # Filter our drop pool to exclude cards belonging to locked anime series
    pool = {k: v for k, v in db["global_cards"].items() 
            if format_rarity(v["rarity"]) == target_rarity 
            and v["anime"].lower().strip() not in locked_animes_lower}
            
    # Fallback to any unlocked cards if the current rarity pool has been locked out entirely
    if not pool:
        pool = {k: v for k, v in db["global_cards"].items() 
                if v["anime"].lower().strip() not in locked_animes_lower}

    # Absolute fallback (ignores locks) to protect execution state if ALL registered cards in DB are locked
    if not pool:
        pool = db["global_cards"]

    card_id, card_data = random.choice(list(pool.items()))
    display_rarity     = format_rarity(card_data["rarity"])

    caption = (
        "<b>「 CARD DROP ぁ 」\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<i>A wild card has appeared!</i></b>\n\n"
        f"<b>⟡ Rarity ⁝〔 {display_rarity}〕</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<b>◈ Use</b> /seize [character name] <b>to claim it!</b>"
    )

    try:
        original_file_id = card_data["file_id"]
        if original_file_id in spoiler_cache:
            msg = await bot.send_photo(
                chat_id=chat_id, photo=spoiler_cache[original_file_id],
                caption=caption, parse_mode=ParseMode.HTML, has_spoiler=True
            )
        else:
            file_info  = await bot.get_file(original_file_id)
            file_bytes = await bot.download_file(file_info.file_path)
            photo_input = BufferedInputFile(file_bytes.getvalue(), filename="card.jpg")
            msg = await bot.send_photo(
                chat_id=chat_id, photo=photo_input,
                caption=caption, parse_mode=ParseMode.HTML, has_spoiler=True
            )
            spoiler_cache[original_file_id] = msg.photo[-1].file_id

        active_drops[str(chat_id)] = {"card_id": card_id, "time": time.time(), "message_id": msg.message_id}
        asyncio.create_task(expire_drop(str(chat_id), msg.message_id))

        cid = str(chat_id)
        if cid in db["groups"]:
            db["groups"][cid]["drops"] = db["groups"][cid].get("drops", 0) + 1
            save_db()

        # ── DB-Group log: card spawn ────────────────────────────────────────
        try:
            group_title = db["groups"].get(cid, {}).get("title", str(chat_id))
            await bot.send_message(
                chat_id=config.DATABASE_BACKUP_ID,
                text=(
                    f"<b>「 🎴 CARD SPAWNED 」</b>\n"
                    f"━━━━━━━━━━━━━━━━━\n"
                    f"• 🆔 <b>Card ID:</b> <code>{card_id}</code>\n"
                    f"• 👤 <b>Card:</b> <b>{card_data['name']}</b>\n"
                    f"• 🌟 <b>Rarity:</b> {display_rarity}\n"
                    f"• 🏘️ <b>Group:</b> {group_title} (<code>{chat_id}</code>)\n"
                    f"• 🕐 <b>Time:</b> {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
                    f"━━━━━━━━━━━━━━━━━"
                ),
                parse_mode=ParseMode.HTML
            )
        except Exception as log_err:
            print(f"[SPAWN LOG] Failed: {log_err}")
    except Exception as e:
        print(f"[DROP] Error: {e}")


def _drop_message_link(chat_id: int, message_id: int):
    """Builds a t.me/c/... deep link to a card-drop message, so a failed
    guess can offer a button back to it. Only works for supergroups
    (chat_id starting with -100) — regular basic groups don't support
    stable message links, so this returns None for those."""
    if not message_id:
        return None
    gid = str(chat_id)
    if gid.startswith("-100"):
        return f"https://t.me/c/{gid[4:]}/{message_id}"
    return None


def _seize_name_matches(query: str, target_name: str) -> bool:
    """Word-level /seize matching. A guess is correct if:
      - the whole query is a substring of (or close-fuzzy to) the full
        name — the original behavior, still handles guessing the full
        name or a multi-word span typed in the right order, or
      - EVERY word in the query individually matches some word in the
        name, in any order — so for "Gojo Satoru" all of /seize gojo,
        /seize satoru, and /seize gojo satoru (or satoru gojo) now work,
        while a guess containing an unrelated word still fails since
        that word won't match anything.
    Words under 3 characters must match a target word exactly (same
    short-fragment guard the original whole-string check had) so tiny
    fragments can't loosely fuzzy-match their way in."""
    query  = query.lower().strip()
    target = target_name.lower().strip()
    if not query:
        return False

    if len(query) >= 3 and query in target:
        return True
    if difflib.SequenceMatcher(None, query, target).ratio() > 0.70:
        return True

    target_words = target.split()
    query_words  = query.split()
    if not query_words:
        return False

    def word_ok(qw: str) -> bool:
        if len(qw) < 3:
            return qw in target_words
        for tw in target_words:
            if qw in tw or tw in qw:
                return True
            if difflib.SequenceMatcher(None, qw, tw).ratio() > 0.70:
                return True
        return False

    return all(word_ok(qw) for qw in query_words)


@main_router.message(Command("seize"))
async def seize_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    chat_id = message.chat.id
    cid_str = str(chat_id)

    if cid_str not in active_drops: return
    if not command.args:
        await message.reply("Provide the character name!\nFormat: <code>/seize</code> [name]", parse_mode=ParseMode.HTML)
        return

    drop_data   = active_drops[cid_str]
    card_id     = drop_data["card_id"]
    drop_time   = drop_data["time"]

    db          = load_db()
    global_card = db["global_cards"].get(card_id)
    if not global_card:
        # The card was deleted from the database after this drop spawned.
        # Previously this just silently returned, leaving the drop stuck
        # in active_drops forever — nobody could ever seize it (every
        # future /seize hit this same dead end) until the 10-minute
        # auto-expiry finally deleted the message. Clear it immediately
        # instead so a fresh, claimable drop can appear right away.
        del active_drops[cid_str]
        try:
            await bot.delete_message(chat_id=chat_id, message_id=drop_data.get("message_id"))
        except Exception:
            pass
        await message.reply(
            "This card was removed from the database and can no longer be claimed.",
            parse_mode=ParseMode.HTML
        )
        return

    target_name = global_card["name"].lower()
    query       = command.args.lower().strip()

    matched = _seize_name_matches(query, target_name)

    if not matched:
        link = _drop_message_link(chat_id, drop_data.get("message_id"))
        wrong_kb = None
        if link:
            wrong_kb = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="View Again", url=link)]
            ])
        await message.reply(
            "🚫「 𝗪𝗥𝗢𝗡𝗚 𝗚𝗨𝗘𝗦𝗦 ぁ 」\n\n➜ 𝗧𝗿𝘆 𝗔𝗴𝗮𝗶𝗻",
            parse_mode=ParseMode.HTML,
            reply_markup=wrong_kb
        )
        return

    time_taken = round(time.time() - drop_time, 2)
    del active_drops[cid_str]

    try:
        await bot.set_message_reaction(
            chat_id=chat_id,
            message_id=message.message_id,
            reaction=[ReactionTypeEmoji(emoji="🎉")]
        )
    except Exception:
        pass

    user_id = str(uid_int)
    name    = message.from_user.first_name
    uname   = message.from_user.username
    db      = ensure_user(user_id, name, uname)

    rarity_normalized = format_rarity(global_card["rarity"])
    base_shards       = 10
    if rarity_normalized == "Elite ⚓":   base_shards = 25
    elif rarity_normalized == "Divine ❄️": base_shards = 100

    speed_bonus  = 15 if time_taken <= 3.0 else 0
    is_duplicate = card_id in db["users"][user_id]["cards"]
    dupe_bonus   = 10 if is_duplicate else 0
    total_earned = base_shards + speed_bonus + dupe_bonus

    db["users"][user_id]["nexus_shards"] = db["users"][user_id].get("nexus_shards", 0) + total_earned

    if card_id not in db["users"][user_id]["cards"]:
        db["users"][user_id]["cards"][card_id] = {"name": global_card["name"], "rarity": global_card["rarity"], "amount": 0}
    db["users"][user_id]["cards"][card_id]["amount"] += 1
    db["users"][user_id]["total_claimed"] = db["users"][user_id].get("total_claimed", 0) + 1

    if cid_str in db["groups"]:
        db["groups"][cid_str]["claims"] = db["groups"][cid_str].get("claims", 0) + 1

    await check_and_reward_referral(user_id, db)
    save_db()

    display_rarity     = format_rarity(global_card["rarity"])
    bonus_breakdown    = f" (+{speed_bonus} Speed⚡)" if speed_bonus else ""
    if dupe_bonus:
        bonus_breakdown += " (+10 Dupe♻️)"

    winner_text = (
        "<b>「 🎊 CARD SEIZED ぁ 」\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"🎊 <i>{get_mention(user_id, name)} seized the card in {time_taken}s!</i>\n\n"
        f"Character : </b>{global_card['name']} <b>《{display_rarity}》</b>\n"
        f"<b>Anime :</b> {global_card['anime']}\n"
        f"<b>Economy :</b> Earned <b>{total_earned} Nexus Shards{bonus_breakdown}!</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Use /deck to <b>view your collection</b>"
    )
    seize_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="View Collection 🫧", switch_inline_query_current_chat=f"card_user.{user_id}")]
    ])
    try:
        await message.reply(winner_text, parse_mode=ParseMode.HTML, reply_markup=seize_kb)
    except Exception:
        pass


# ==========================================
# /gift (Spoiler + Confirmation with Daily Limits)
# ==========================================
@main_router.message(Command("gift"))
async def gift_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if not message.reply_to_message or not message.reply_to_message.from_user:
        await message.reply("Reply to a user's message to gift them a card.", parse_mode=ParseMode.HTML)
        return

    target_user = message.reply_to_message.from_user
    if target_user.is_bot:
        await message.reply("You cannot gift cards to bots.", parse_mode=ParseMode.HTML)
        return
    if str(target_user.id) == str(message.from_user.id):
        await message.reply("You cannot gift a card to yourself.", parse_mode=ParseMode.HTML)
        return
    if not command.args:
        await message.reply("<b>Usage:</b> <code>/gift &lt;card name&gt;</code>", parse_mode=ParseMode.HTML)
        return

    user_id   = str(message.from_user.id)
    target_id = str(target_user.id)

    # Cooldown check (non-admins)
    now = time.time()
    if uid_int not in ADMIN_IDS:
        last_gift = _gift_cooldowns.get(user_id, 0)
        if now - last_gift < GIFT_COOLDOWN:
            rem  = int(GIFT_COOLDOWN - (now - last_gift))
            m, s = divmod(rem, 60)
            await message.reply(
                f"⏳ <b>Gift cooldown active!</b>\nYou can gift another card in <b>{m}m {s}s</b>.",
                parse_mode=ParseMode.HTML
            )
            return

    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    db = ensure_user(target_id, target_user.first_name, target_user.username)

    today = config.get_shop_rotation_seed()

    # Dynamic Sender daily check schema normalization
    sender_gift_data = db["users"][user_id].setdefault("daily_gifts", {})
    if not isinstance(sender_gift_data, dict):
        db["users"][user_id]["daily_gifts"] = {"date": today, "sent": 0, "received": 0}
        sender_gift_data = db["users"][user_id]["daily_gifts"]
    else:
        if sender_gift_data.get("date") != today:
            sender_gift_data["date"] = today
            sender_gift_data["sent"] = 0
            sender_gift_data["received"] = 0
        else:
            if "sent" not in sender_gift_data: sender_gift_data["sent"] = 0
            if "received" not in sender_gift_data: sender_gift_data["received"] = 0

    if uid_int not in ADMIN_IDS and sender_gift_data["sent"] >= DAILY_GIFT_SEND_LIMIT:
        await message.reply(
            f"<b>Daily limit reached!</b>\nYou have already sent your limit of <b>{DAILY_GIFT_SEND_LIMIT}</b> gifts today.",
            parse_mode=ParseMode.HTML
        )
        return

    # Dynamic Receiver daily check schema normalization
    receiver_gift_data = db["users"][target_id].setdefault("daily_gifts", {})
    if not isinstance(receiver_gift_data, dict):
        db["users"][target_id]["daily_gifts"] = {"date": today, "sent": 0, "received": 0}
        receiver_gift_data = db["users"][target_id]["daily_gifts"]
    else:
        if receiver_gift_data.get("date") != today:
            receiver_gift_data["date"] = today
            receiver_gift_data["sent"] = 0
            receiver_gift_data["received"] = 0
        else:
            if "sent" not in receiver_gift_data: receiver_gift_data["sent"] = 0
            if "received" not in receiver_gift_data: receiver_gift_data["received"] = 0

    if int(target_id) not in ADMIN_IDS and receiver_gift_data["received"] >= DAILY_GIFT_RECEIVE_LIMIT:
        await message.reply(
            f"<b>Recipient limit reached!</b>\nThis user has already received their maximum of <b>{DAILY_GIFT_RECEIVE_LIMIT}</b> gifts today.",
            parse_mode=ParseMode.HTML
        )
        return

    query    = command.args.lower().strip()
    my_cards = db["users"][user_id].get("cards", {})

    if not my_cards:
        await message.reply("You don't own any cards yet!", parse_mode=ParseMode.HTML)
        return

    best_match = None
    best_ratio = 0.0

    for cid, cdata in my_cards.items():
        name_lower = cdata["name"].lower()
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
    display_rarity = format_rarity(matched_data["rarity"])

    caption = (
        "<b>「 GIFT CARD ぁ 」\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"Character : </b>{matched_data['name']}\n"
        f"<b>Rarity :</b> {display_rarity}\n\n"
        f"<blockquote><b>⤿ Are you sure you want to gift this to {get_mention(target_user.id, target_user.first_name)}?</b></blockquote>"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎁 Yes, Gift Card", callback_data=f"cfgift_{user_id}_{target_id}_{matched_cid}")],
        [InlineKeyboardButton(text="Cancel", callback_data=f"cancel_action_{user_id}")]
    ])
    await message.reply_photo(
        photo=global_data.get("file_id"), caption=caption,
        reply_markup=kb, parse_mode=ParseMode.HTML, has_spoiler=True
    )


@main_router.callback_query(F.data.startswith("cfgift_"))
async def confirm_gift_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return

    parts     = cq.data.split("_", 3)
    sender_id = parts[1]
    target_id = parts[2]
    card_id   = parts[3]
    user_id   = str(cq.from_user.id)

    if user_id != sender_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    # Double check cooldown before processing gift (non-admins)
    now = time.time()
    if uid_int not in ADMIN_IDS:
        last_gift = _gift_cooldowns.get(user_id, 0)
        if now - last_gift < GIFT_COOLDOWN:
            rem  = int(GIFT_COOLDOWN - (now - last_gift))
            m, s = divmod(rem, 60)
            await cq.answer(f"⏳ Cooldown active! Wait {m}m {s}s.", show_alert=True)
            return

    db = load_db()

    # Double-check daily counts on execution
    today = config.get_shop_rotation_seed()

    # Sender daily count check and robust normalization
    sender_gift_data = db["users"][user_id].setdefault("daily_gifts", {})
    if not isinstance(sender_gift_data, dict):
        db["users"][user_id]["daily_gifts"] = {"date": today, "sent": 0, "received": 0}
        sender_gift_data = db["users"][user_id]["daily_gifts"]
    else:
        if sender_gift_data.get("date") != today:
            sender_gift_data["date"] = today
            sender_gift_data["sent"] = 0
            sender_gift_data["received"] = 0
        else:
            if "sent" not in sender_gift_data: sender_gift_data["sent"] = 0
            if "received" not in sender_gift_data: sender_gift_data["received"] = 0

    if uid_int not in ADMIN_IDS and sender_gift_data["sent"] >= DAILY_GIFT_SEND_LIMIT:
        await cq.answer("Daily sending limit reached!", show_alert=True)
        return

    # Receiver daily count check and robust normalization
    receiver_gift_data = db["users"][target_id].setdefault("daily_gifts", {})
    if not isinstance(receiver_gift_data, dict):
        db["users"][target_id]["daily_gifts"] = {"date": today, "sent": 0, "received": 0}
        receiver_gift_data = db["users"][target_id]["daily_gifts"]
    else:
        if receiver_gift_data.get("date") != today:
            receiver_gift_data["date"] = today
            receiver_gift_data["sent"] = 0
            receiver_gift_data["received"] = 0
        else:
            if "sent" not in receiver_gift_data: receiver_gift_data["sent"] = 0
            if "received" not in receiver_gift_data: receiver_gift_data["received"] = 0

    if int(target_id) not in ADMIN_IDS and receiver_gift_data["received"] >= DAILY_GIFT_RECEIVE_LIMIT:
        await cq.answer("Recipient daily receipt limit reached!", show_alert=True)
        return

    my_cards = db["users"].get(user_id, {}).get("cards", {})

    if card_id not in my_cards or my_cards[card_id]["amount"] <= 0:
        await cq.answer("You don't own this card anymore!", show_alert=True)
        return

    if _check_action_cooldown(f"gift_{user_id}"):
        await cq.answer("⏳ Please wait a moment before gifting again.", show_alert=True)
        return

    card_data = my_cards[card_id]
    my_cards[card_id]["amount"] -= 1
    if my_cards[card_id]["amount"] <= 0:
        del my_cards[card_id]
        if db["users"][user_id].get("special_card") == card_id:
            db["users"][user_id]["special_card"] = None

    target_cards = db["users"][target_id].setdefault("cards", {})
    if card_id not in target_cards:
        target_cards[card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
    target_cards[card_id]["amount"] += 1

    # Record limit parameters on successful execution (Cooldown is only for regular users)
    if uid_int not in ADMIN_IDS:
        _gift_cooldowns[user_id] = now
        
    # We now increment parameters for both admins and regular users to show accurate visual tracking
    sender_gift_data["sent"] += 1
    receiver_gift_data["received"] += 1

    rarity_normalized = format_rarity(card_data["rarity"])
    target_name_for_log = db["users"][target_id].get("name", "User")
    chat_title = cq.message.chat.title or "Private DM"
    log_action(db, user_id, {
        "type": "gift_sent", "card_name": card_data["name"], "rarity": rarity_normalized,
        "cp_id": target_id, "cp_name": target_name_for_log,
        "chat_id": cq.message.chat.id, "chat_title": chat_title,
    })
    log_action(db, target_id, {
        "type": "gift_received", "card_name": card_data["name"], "rarity": rarity_normalized,
        "cp_id": user_id, "cp_name": cq.from_user.first_name,
        "chat_id": cq.message.chat.id, "chat_title": chat_title,
    })

    await check_and_reward_referral(target_id, db)
    save_db()

    target_name    = db["users"][target_id].get("name", "User")
    display_rarity = format_rarity(card_data["rarity"])

    caption = (
        f"<b>「 CARD GIFTED 🎁 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"You successfully gifted <b>{card_data['name']}</b> [{display_rarity}] to {get_mention(target_id, target_name)}!\n\n"
        f"📊 Daily Gifts Sent: <b>{sender_gift_data['sent']}/{DAILY_GIFT_SEND_LIMIT}</b>"
    )
    await cq.message.edit_caption(caption=caption, parse_mode=ParseMode.HTML, reply_markup=None)
    await cq.answer("🎁 Gift sent successfully!")


# ==========================================
# /trade CARD-FOR-CARD TRADING SYSTEM
# ==========================================
def _find_card_match(query: str, pool: dict):
    """Requires an EXACT (case-insensitive, whitespace-trimmed) full card
    name match against a {cid: cdata} pool.

    Trade previously reused the fuzzy/partial matcher shared with /gift and
    /burn, but that caused false matches whenever two cards shared a common
    substring — e.g. typing "Goku" could silently resolve to "Ultra Instinct
    Goku" (or vice versa) instead of the plain "Goku" card. Trades move real
    inventory both ways, so we require the full, exact name here rather than
    guessing which card was meant.
    """
    query = query.strip().lower()
    for cid, cdata in pool.items():
        if cdata.get("amount", 0) <= 0:
            continue
        if cdata["name"].strip().lower() == query:
            return (cid, cdata)
    return None


async def _expire_trade(trade_id: str):
    await asyncio.sleep(TRADE_EXPIRY_SECS)
    trade = active_trades.get(trade_id)
    if not trade or trade.get("status") != "pending":
        return
    trade["status"] = "expired"
    try:
        await bot.edit_message_text(
            chat_id=trade["chat_id"], message_id=trade["message_id"],
            text="<b>「 TRADE EXPIRED ⌛ 」</b>\n━━━━━━━━━━━━━━━━━\nThis trade offer went unanswered and has expired.",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass
    active_trades.pop(trade_id, None)


@main_router.message(Command("trade"))
async def trade_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if not message.reply_to_message or not message.reply_to_message.from_user:
        await message.reply("Reply to a user's message to propose a trade.", parse_mode=ParseMode.HTML)
        return

    target_user = message.reply_to_message.from_user
    if target_user.is_bot:
        await message.reply("You cannot trade with bots.", parse_mode=ParseMode.HTML)
        return
    if str(target_user.id) == str(message.from_user.id):
        await message.reply("You cannot trade with yourself.", parse_mode=ParseMode.HTML)
        return

    if not command.args or "|" not in command.args:
        await message.reply(
            "<b>Usage:</b> <code>/trade your card name | their card name</code>\n"
            "<i>Reply to the user you want to trade with.</i>",
            parse_mode=ParseMode.HTML
        )
        return

    raw_my, raw_their = command.args.split("|", 1)
    my_query    = raw_my.strip().lower()
    their_query = raw_their.strip().lower()
    if not my_query or not their_query:
        await message.reply(
            "<b>Usage:</b> <code>/trade your card name | their card name</code>",
            parse_mode=ParseMode.HTML
        )
        return

    user_id   = str(message.from_user.id)
    target_id = str(target_user.id)

    # Trade cooldown (non-admins) — 1 minute between offers
    now = time.time()
    if uid_int not in ADMIN_IDS:
        last_trade = _trade_cooldowns.get(user_id, 0)
        if now - last_trade < TRADE_COOLDOWN_SECS:
            rem = int(TRADE_COOLDOWN_SECS - (now - last_trade))
            await message.reply(f"⏳ <b>Trade cooldown active!</b>\nPlease wait <b>{rem}s</b> before offering another trade.", parse_mode=ParseMode.HTML)
            return

    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    db = ensure_user(target_id, target_user.first_name, target_user.username)

    my_cards    = db["users"][user_id].get("cards", {})
    their_cards = db["users"][target_id].get("cards", {})

    if not my_cards:
        await message.reply("You don't own any cards yet!", parse_mode=ParseMode.HTML)
        return
    if not their_cards:
        await message.reply(f"{get_mention(target_id, target_user.first_name)} doesn't own any cards yet!", parse_mode=ParseMode.HTML)
        return

    my_match    = _find_card_match(my_query, my_cards)
    their_match = _find_card_match(their_query, their_cards)

    if not my_match:
        await message.reply(
            f"You don't own a card named exactly <b>{raw_my.strip()}</b>.\n"
            f"<i>Trades need the full card name (e.g. \"Ultra Instinct Goku\", not just \"Goku\").</i>",
            parse_mode=ParseMode.HTML
        )
        return
    if not their_match:
        await message.reply(
            f"{get_mention(target_id, target_user.first_name)} doesn't own a card named exactly <b>{raw_their.strip()}</b>.\n"
            f"<i>Trades need the full card name (e.g. \"Ultra Instinct Goku\", not just \"Goku\").</i>",
            parse_mode=ParseMode.HTML
        )
        return

    my_cid, my_cdata       = my_match
    their_cid, their_cdata = their_match

    my_rarity    = format_rarity(my_cdata["rarity"])
    their_rarity = format_rarity(their_cdata["rarity"])

    if not _trade_rarities_compatible(my_rarity, their_rarity):
        await message.reply(
            "<b>Invalid trade!</b>\n\n"
            "🃏 <b>Basic</b> can trade for 🃏 Basic / ⚓ Elite\n"
            "⚓ <b>Elite</b> can trade for 🃏 Basic / ⚓ Elite\n"
            "❄️ <b>Divine</b> can trade for ❄️ Divine only",
            parse_mode=ParseMode.HTML
        )
        return

    trade_id = uuid.uuid4().hex[:12]
    active_trades[trade_id] = {
        "initiator_id": user_id, "initiator_name": message.from_user.first_name,
        "target_id": target_id, "target_name": target_user.first_name,
        "my_cid": my_cid, "their_cid": their_cid,
        "status": "pending", "created": now,
    }

    caption = (
        "<b>「 TRADE OFFER 🔄 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"{get_mention(user_id, message.from_user.first_name)} wants to trade with {get_mention(target_id, target_user.first_name)}!\n\n"
        f"Offering ― <b>{my_cdata['name']}</b> [{my_rarity}]\n"
        f"Wants ― <b>{their_cdata['name']}</b> [{their_rarity}]\n\n"
        f"{get_mention(target_id, target_user.first_name)} choose your actions !"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="✅ Accept", callback_data=f"trd_acc_{trade_id}"),
            InlineKeyboardButton(text="❌ Decline", callback_data=f"trd_dec_{trade_id}")
        ]
    ])
    sent = await message.reply(caption, reply_markup=kb, parse_mode=ParseMode.HTML)
    active_trades[trade_id]["message_id"] = sent.message_id
    active_trades[trade_id]["chat_id"]    = sent.chat.id

    if uid_int not in ADMIN_IDS:
        _trade_cooldowns[user_id] = now

    asyncio.create_task(_expire_trade(trade_id))


@main_router.callback_query(F.data.startswith("trd_acc_"))
async def accept_trade_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return

    trade_id = cq.data.split("trd_acc_", 1)[1]
    trade = active_trades.get(trade_id)
    if not trade or trade.get("status") != "pending":
        await cq.answer("This trade offer is no longer active.", show_alert=True)
        return

    if str(uid_int) != trade["target_id"]:
        await cq.answer("This trade offer is not for you!", show_alert=True)
        return

    if _check_action_cooldown(f"trade_{trade['target_id']}"):
        await cq.answer("⏳ Please wait a moment before responding again.", show_alert=True)
        return

    db = load_db()
    sender_id, target_id = trade["initiator_id"], trade["target_id"]
    my_cid, their_cid = trade["my_cid"], trade["their_cid"]

    sender_cards = db["users"].get(sender_id, {}).get("cards", {})
    target_cards = db["users"].get(target_id, {}).get("cards", {})

    # Re-validate ownership at accept-time — inventories may have changed since the offer was made
    if my_cid not in sender_cards or sender_cards[my_cid].get("amount", 0) <= 0 or \
       their_cid not in target_cards or target_cards[their_cid].get("amount", 0) <= 0:
        trade["status"] = "cancelled"
        active_trades.pop(trade_id, None)
        await cq.answer("One of the cards is no longer available!", show_alert=True)
        try:
            await cq.message.edit_text(
                "<b>「 TRADE CANCELLED 」</b>\n━━━━━━━━━━━━━━━━━\nOne of the cards is no longer available.",
                parse_mode=ParseMode.HTML
            )
        except Exception:
            pass
        return

    my_data    = dict(sender_cards[my_cid])
    their_data = dict(target_cards[their_cid])

    # Remove offered card from sender, add it to target
    sender_cards[my_cid]["amount"] -= 1
    if sender_cards[my_cid]["amount"] <= 0:
        del sender_cards[my_cid]
        if db["users"][sender_id].get("special_card") == my_cid:
            db["users"][sender_id]["special_card"] = None
    target_cards.setdefault(my_cid, {"name": my_data["name"], "rarity": my_data["rarity"], "amount": 0})
    target_cards[my_cid]["amount"] += 1

    # Remove requested card from target, add it to sender
    target_cards[their_cid]["amount"] -= 1
    if target_cards[their_cid]["amount"] <= 0:
        del target_cards[their_cid]
        if db["users"][target_id].get("special_card") == their_cid:
            db["users"][target_id]["special_card"] = None
    sender_cards.setdefault(their_cid, {"name": their_data["name"], "rarity": their_data["rarity"], "amount": 0})
    sender_cards[their_cid]["amount"] += 1

    chat_title = cq.message.chat.title or "Private DM"
    log_action(db, sender_id, {
        "type": "trade_sent", "card_name": my_data["name"], "rarity": format_rarity(my_data["rarity"]),
        "cp_id": target_id, "cp_name": db["users"][target_id].get("name", "User"),
        "chat_id": cq.message.chat.id, "chat_title": chat_title,
    })
    log_action(db, target_id, {
        "type": "trade_sent", "card_name": their_data["name"], "rarity": format_rarity(their_data["rarity"]),
        "cp_id": sender_id, "cp_name": db["users"][sender_id].get("name", "User"),
        "chat_id": cq.message.chat.id, "chat_title": chat_title,
    })
    save_db()
    await config.flush_db_now()

    trade["status"] = "completed"
    active_trades.pop(trade_id, None)

    my_rarity_disp    = format_rarity(my_data["rarity"])
    their_rarity_disp = format_rarity(their_data["rarity"])

    caption = (
        "<b>「 TRADE COMPLETED ✅ 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"{get_mention(sender_id, trade['initiator_name'])} traded away <b>{my_data['name']}</b> [{my_rarity_disp}]\n"
        f"{get_mention(target_id, trade['target_name'])} traded away <b>{their_data['name']}</b> [{their_rarity_disp}]\n\n"
        f"Trade Successfully completed !"
    )
    try:
        await cq.message.edit_text(caption, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer("🔄 Trade completed!")

    # ── Public Trade Log ──────────────────────────────────────────────────
    my_emoji    = my_rarity_disp.split()[-1]
    their_emoji = their_rarity_disp.split()[-1]
    log_text = (
        "⇄ <b>CARD TRADE COMPLETED</b>\n\n"
        f"<b>FROM:</b> {sender_id}\n"
        f"<b>CARD:</b> {my_data['name']} {my_emoji}\n\n"
        f"<b>TO:</b> {target_id}\n"
        f"<b>CARD:</b> {their_data['name']} {their_emoji}"
    )
    try:
        await bot.send_message(
            chat_id=config.PUBLIC_LOG_GROUP_ID,
            text=log_text,
            message_thread_id=config.LOG_THREAD_TRADE,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"[LOG] Failed to send public trade log to Topic {config.LOG_THREAD_TRADE}: {e}")


@main_router.callback_query(F.data.startswith("trd_dec_"))
async def decline_trade_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id

    trade_id = cq.data.split("trd_dec_", 1)[1]
    trade = active_trades.get(trade_id)
    if not trade or trade.get("status") != "pending":
        await cq.answer("This trade offer is no longer active.", show_alert=True)
        return

    # Either side can back out of a pending offer
    if str(uid_int) not in (trade["target_id"], trade["initiator_id"]):
        await cq.answer("This trade offer is not for you!", show_alert=True)
        return

    trade["status"] = "declined"
    active_trades.pop(trade_id, None)

    try:
        await cq.message.edit_text(
            "<b>「 TRADE DECLINED ❌ 」</b>\n━━━━━━━━━━━━━━━━━\nThis trade offer was declined.",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass
    await cq.answer("Trade declined.")



# ==========================================
# GLOBAL CANCELLATION & CLOSE HANDLERS
# ==========================================
@main_router.callback_query(F.data.startswith("cancel_action_"))
async def cancel_action_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    owner_id = cq.data[len("cancel_action_"):]
    if str(uid_int) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    try:
        await cq.message.edit_caption(caption="Action cancelled.", reply_markup=None)
    except Exception:
        await cq.message.edit_text("Action cancelled.", reply_markup=None)
    await cq.answer()


@main_router.callback_query(F.data.startswith("close_msg"))
async def close_msg_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    parts = cq.data.split("|")
    if len(parts) > 1:
        owner_id = parts[1]
        if str(uid_int) != owner_id:
            await cq.answer("This menu is not for you!", show_alert=True)
            return

    try:
        await cq.message.delete()
    except Exception:
        pass
    await cq.answer()



# ==========================================
# /sortcards INTERFACE PRESETS
# ==========================================
@main_router.message(Command("sortcards"))
async def sort_cards(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id      = str(message.from_user.id)
    db           = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    current_sort = db["users"][user_id].get("sort_pref", "default").title()

    text = (
        f"<b>「 SORTING ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"🌟 Rarity  — Divine → Elite → Basic\n"
        f"🔤 Name    — A → Z\n"
        f"📦 Amount  — Most owned first\n"
        f"🔄 Default — Claim order\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<b>Current sorting order </b>- {current_sort}"
    )
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🌟 Rarity", callback_data=f"setsort_{user_id}_rarity"),
            InlineKeyboardButton(text="🔤 Name",   callback_data=f"setsort_{user_id}_name")
        ],
        [
            InlineKeyboardButton(text="📦 Amount",  callback_data=f"setsort_{user_id}_amount"),
            InlineKeyboardButton(text="🔄 Default", callback_data=f"setsort_{user_id}_default")
        ]
    ])
    await message.reply(text, reply_markup=keyboard, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("setsort_"))
async def set_sort_cb(callback_query: CallbackQuery):
    uid_int = callback_query.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await callback_query.answer("🔇 You are currently restricted.", show_alert=True)
        return

    parts    = callback_query.data.split("_")
    owner_id = parts[1]
    mode     = parts[2]
    if str(callback_query.from_user.id) != owner_id: return

    db = load_db()
    db["users"][owner_id]["sort_pref"] = mode
    save_db()
    await callback_query.answer(f"✅ Sorting order saved: {mode.title()}")

    text = (
        f"<b>「 SORTING ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"🌟 Rarity  — Divine → Elite → Basic\n"
        f"🔤 Name    — A → Z\n"
        f"📦 Amount  — Most owned first\n"
        f"🔄 Default — Claim order\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<b>Current sorting order </b>- {mode.title()}"
    )
    await callback_query.message.edit_text(text, reply_markup=callback_query.message.reply_markup, parse_mode=ParseMode.HTML)


# ==========================================
# /profile ENGINE PARSER DESIGN LAYOUTS
# ==========================================
async def _build_profile_payload(from_user):
    """Builds the /profile text, keyboard, and banner image for a given
    Telegram user. Shared by the /profile command and the "Back" button
    on the banner picker, so both always render an identical card.
    `from_user` is an aiogram User object — Message.from_user and
    CallbackQuery.from_user both satisfy this, exposing the same fields."""
    uid_int  = from_user.id
    user_id  = str(uid_int)
    name     = from_user.first_name
    username = from_user.username
    db       = ensure_user(user_id, name, username)
    user_data = db["users"][user_id]
    cards     = user_data.get("cards", {})

    # Total copies owned, broken down by rarity (dupes counted, not just unique cards)
    rarity_counts = {"Divine ❄️": 0, "Elite ⚓": 0, "Basic 🃏": 0}
    for cdata in cards.values():
        r = format_rarity(cdata.get("rarity", ""))
        if r in rarity_counts:
            rarity_counts[r] += cdata.get("amount", 0)
    total_cards = sum(rarity_counts.values())

    shards = user_data.get("nexus_shards", 0)

    sorted_users = sorted(db["users"].items(), key=lambda x: len(x[1].get("cards", {})), reverse=True)
    rank = 9999
    for i, (uid, udata) in enumerate(sorted_users):
        if uid == user_id:
            rank = i + 1
            break

    now = time.time()

    # Global (ghost) ban status — reuses is_ghost_banned() which also auto-clears expired bans
    is_gbanned_now = is_ghost_banned(uid_int)
    if is_gbanned_now:
        meta = config.gban_meta.get(uid_int, {})
        expires_at = meta.get("expires_at")
        if expires_at:
            remaining = expires_at - now
            gban_line = f"{is_gbanned_now} [Wait : {format_wait_mmss(remaining)} min]"
        else:
            gban_line = f"{is_gbanned_now} [Permanent]"
    else:
        gban_line = f"{is_gbanned_now}"

    is_shadow_banned_now = bool(int(user_id) in config.shadow_banned and config.shadow_banned[int(user_id)] > now)
    if is_shadow_banned_now:
        remaining = config.shadow_banned[int(user_id)] - now
        shadow_ban_line = f"{is_shadow_banned_now} [Wait : {format_wait_mmss(remaining)} min]"
    else:
        shadow_ban_line = f"{is_shadow_banned_now}"

    full_name  = from_user.full_name
    first_name = name
    safe_full_name  = str(full_name).replace("<", "&lt;").replace(">", "&gt;")
    safe_first_name = str(first_name).replace("<", "&lt;").replace(">", "&gt;")
    name_link = f'<a href="tg://user?id={user_id}">{safe_full_name}</a>'

    profile_text = (
        "<b>「 𝗡𝗘𝗫𝗨𝗦 : 𝗣𝗥𝗢𝗙𝗜𝗟𝗘 ぁ」</b>\n\n"
        f"<b>Name</b> - {name_link}\n"
        f"<b>ID</b> - {safe_first_name} [{user_id}]\n\n"
        f"<b>Total Shards</b> - {shards} 💠\n"
        f"<b>Total Cards</b> - {total_cards}\n"
        f"• <b>Total Divine</b> - {rarity_counts['Divine ❄️']}\n"
        f"• <b>Total Elite</b> - {rarity_counts['Elite ⚓']}\n"
        f"• <b>Total Basic</b> - {rarity_counts['Basic 🃏']}\n"
        f"<b>Global Rank</b> - #{rank}\n\n"
        f"<b>Global Ban</b> - {gban_line}\n"
        f"<b>Shadow Ban</b> - {shadow_ban_line}"
    )

    keyboard  = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="Change Banner", callback_data=f"mb_open|{user_id}"),
        InlineKeyboardButton(text="Close", callback_data=f"close_msg|{user_id}")
    ]])

    # Composite the shared default banner with this user's own profile
    # picture pasted into its circle. Falls back (raw pfp, then text-only)
    # if no default banner is set or the compositing fails.
    try:
        banner_buf = await banners.build_profile_banner(uid_int, first_name)
    except Exception:
        banner_buf = None

    return profile_text, keyboard, banner_buf, user_id


@main_router.message(Command("profile"))
async def view_profile(message: Message):
    profile_text, keyboard, banner_buf, user_id = await _build_profile_payload(message.from_user)
    photo_sent = False

    if banner_buf:
        try:
            photo_file = BufferedInputFile(banner_buf.read(), filename="profile.jpg")
            await smart_reply_photo(message, photo=photo_file, caption=profile_text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
            photo_sent = True
        except Exception:
            pass

    if not photo_sent:
        try:
            file_id = await banners.get_current_profile_photo_file_id(int(user_id), big=False)
            if file_id:
                await smart_reply_photo(message, photo=file_id, caption=profile_text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                photo_sent = True
        except Exception:
            pass

    if not photo_sent:
        try:
            await smart_reply(message, profile_text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
        except Exception:
            pass


@main_router.callback_query(F.data.startswith("mb_back|"))
async def profile_back_cb(cq: CallbackQuery):
    # "Back" button shown on the banner picker when it was opened from
    # /profile (see banners.py's _show_my_banners origin="profile").
    # Rebuilds the profile card fresh (stats may have changed) and edits
    # it back in place over the banner-picker message.
    owner_id = cq.data.split("|")[1]
    if str(cq.from_user.id) != owner_id:
        await cq.answer("This isn't your profile!", show_alert=True)
        return
    await cq.answer()

    profile_text, keyboard, banner_buf, user_id = await _build_profile_payload(cq.from_user)
    edited = False

    if banner_buf:
        try:
            photo_file = BufferedInputFile(banner_buf.read(), filename="profile.jpg")
            await cq.message.edit_media(
                InputMediaPhoto(media=photo_file, caption=profile_text, parse_mode=ParseMode.HTML),
                reply_markup=keyboard
            )
            edited = True
        except Exception:
            pass

    if not edited:
        try:
            file_id = await banners.get_current_profile_photo_file_id(int(user_id), big=False)
            if file_id:
                await cq.message.edit_media(
                    InputMediaPhoto(media=file_id, caption=profile_text, parse_mode=ParseMode.HTML),
                    reply_markup=keyboard
                )
                edited = True
        except Exception:
            pass

    if not edited:
        try:
            await cq.message.edit_caption(caption=profile_text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
            edited = True
        except Exception:
            pass

    if not edited:
        try:
            await cq.message.edit_text(profile_text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
        except Exception:
            pass


# ==========================================
# /leaderboard WRAPPERS
# ==========================================
LEADERBOARD_SYMBOLS = ["✦", "✧", "❖"] + ["◈"] * 7


@main_router.message(Command("leaderboard", "top"))
async def leaderboard(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    db      = load_db()
    top     = sorted(db["users"].items(), key=lambda x: len(x[1].get("cards", {})), reverse=True)
    user_id = str(uid_int)

    user_rank = 0
    for i, (uid, ud) in enumerate(top):
        if uid == user_id:
            user_rank = i + 1
            break
    rank_text = f"#{user_rank}" if user_rank > 0 else "Unranked"

    text = "<b>「 🌐 𝗧𝗢𝗣 𝗖𝗔𝗥𝗗 𝗖𝗢𝗟𝗟𝗘𝗖𝗧𝗢𝗥 ぁ 」</b>\n━━━━━━━━━━━━━━━━━\n\n"
    if not top:
        text += "<i>No collectors found yet.</i>\n"
    else:
        for i, (uid, ud) in enumerate(top[:10]):
            sym       = LEADERBOARD_SYMBOLS[i % 10]
            safe_name = str(ud.get("name", "Unknown")).replace("<", "&lt;").replace(">", "&gt;")
            text += f"{sym} <b>{safe_name}</b> ― 🎴 {len(ud.get('cards', {}))}\n"
    text += "\n━━━━━━━━━━━━━━━━━"

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"❖ Your Rank - {rank_text}", callback_data="noop")],
        [InlineKeyboardButton(text="✕ Close", callback_data=f"close_msg|{uid_int}")]
    ])

    pic = db.get("settings", {}).get("leaderboard_pic")
    if pic: await smart_reply_photo(message, photo=pic, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
    else:   await smart_reply(message, text, reply_markup=kb, parse_mode=ParseMode.HTML)


# ==========================================
# INLINE BROWSER EXECUTION
# ==========================================
@main_router.inline_query()
async def inline_query_handler(inline_query: InlineQuery):
    uid_int = inline_query.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    query_raw      = inline_query.query.strip()
    target_user_id = str(inline_query.from_user.id)
    query          = ""

    if query_raw.lower().startswith("card_user."):
        rest  = query_raw[len("card_user."):]
        parts = rest.split(maxsplit=1)
        if parts and parts[0].isdigit():
            target_user_id = parts[0]
            query = parts[1].lower() if len(parts) > 1 else ""
        else:
            # "card_user." prefix present but no valid numeric id followed —
            # fall back to treating everything after the prefix as a plain
            # search query against the requester's own collection.
            query = rest.lower()
    else:
        # BUG THIS FIXES: a bare query (no "card_user." prefix), e.g.
        # "@Animenx_bot Goku", was previously discarded entirely — `query`
        # stayed "" so it silently showed the requester's whole unfiltered
        # collection no matter what they typed. Now it's used as-is to
        # search the requester's own collection by card name or anime.
        query = query_raw.lower()

    db           = ensure_user(str(inline_query.from_user.id), inline_query.from_user.first_name, inline_query.from_user.username)
    cards        = db["users"].get(target_user_id, {}).get("cards", {})
    global_cards = db.get("global_cards", {})
    results      = []

    items     = list(cards.items())
    sort_pref = db["users"].get(target_user_id, {}).get("sort_pref", "default")
    if sort_pref == "rarity":   items.sort(key=lambda x: RARITY_ORDER.get(format_rarity(x[1]["rarity"]), 99))
    elif sort_pref == "amount": items.sort(key=lambda x: x[1]["amount"], reverse=True)
    else:                       items.sort(key=lambda x: x[1]["name"].lower())

    # BUG THIS FIXES: previously sliced to the first 50 cards BEFORE
    # applying the search filter, and never told Telegram there were more
    # results to page through. That meant (a) any card past the 50th in
    # sort order was invisible to search no matter the query, and (b) any
    # collection over 50 cards was permanently capped at 50 in inline mode
    # — the rest were unreachable no matter how far you scrolled.
    # Fix: filter first, then paginate the FILTERED list using Telegram's
    # inline offset mechanism so scrolling further actually fetches more.
    if query:
        filtered = [
            (cid, cdata) for cid, cdata in items
            if query in cdata["name"].lower()
            or query in cdata["rarity"].lower()
            or query in global_cards.get(cid, {}).get("anime", "").lower()
        ]
    else:
        filtered = items

    try:
        offset = int(inline_query.offset) if inline_query.offset else 0
    except ValueError:
        offset = 0

    PAGE_SIZE = 50
    page_slice = filtered[offset:offset + PAGE_SIZE]
    next_offset = str(offset + PAGE_SIZE) if offset + PAGE_SIZE < len(filtered) else ""

    for cid, cdata in page_slice:
        full    = global_cards.get(cid, {})
        file_id = full.get("file_id", "")
        if not file_id or len(file_id) < 10: continue

        disp_rarity  = format_rarity(cdata["rarity"])
        user_name    = db["users"].get(target_user_id, {}).get("name", "User")
        safe_name    = str(user_name).replace("<", "&lt;").replace(">", "&gt;")
        mention      = f'<a href="tg://user?id={target_user_id}">{safe_name}</a>'
        
        caption_text = (
            f"<i><b>Ooooh! Check out {mention}'s card!</b></i>\n\n"
            f"<b>⦿ <i>Character </i>» {cdata['name']} ⟪ {full.get('anime', '?')} ⟫ \n"
            f"⦾ <i>Rarity </i>» {disp_rarity}\n"
            f"⬤ <i>Owned</i>  » x{cdata['amount']}</b>"
        )

        if file_id.startswith("http://") or file_id.startswith("https://"):
            results.append(InlineQueryResultPhoto(id=cid, photo_url=file_id, thumbnail_url=file_id, caption=caption_text, parse_mode=ParseMode.HTML))
        else:
            results.append(InlineQueryResultCachedPhoto(id=cid, photo_file_id=file_id, caption=caption_text, parse_mode=ParseMode.HTML))

    if not results:
        next_offset = ""  # no results at all — don't offer further pagination
        results.append(InlineQueryResultArticle(
            id="empty", title="No cards found",
            description="Try a different search or claim cards first!",
            input_message_content=InputTextMessageContent(
                message_text="No cards match your search. Claim some in the group!",
                parse_mode=ParseMode.HTML
            )
        ))

    try:
        await inline_query.answer(results, cache_time=10, is_personal=True, next_offset=next_offset)
    except Exception as e:
        print(f"[INLINE] Error: {e}")


# ==========================================
# WELCOME CONTROLLERS (/start & /help)
# ==========================================
def build_help_text() -> str:
    return (
        "<b>「 𝘊𝘖𝘔𝘔𝘈𝘕𝘋𝘚 ぁ 」\n"
        "━━━━━━━━━━━━━━━━━</b>\n\n"
        "<b>➷ /profile\n〻 View your profile &amp; stats\n\n"
        "➷ /deck\n〻 View your card deck\n\n"
        "➷ /flex [Name]\n〻 Showcase your cards\n\n"
        "➷ /gift [Name] (reply to msg)\n〻 Gift a card to a user\n\n"
        "➷ /trade [Your Card] | [Their Card] (reply to msg)\n〻 Propose a card-for-card trade\n\n"
        "➷ /leaderboard\n〻 Global collector ranking\n\n"
        "➷ /special [Name]\n〻 Set featured card\n\n"
        "➷ /daily\n〻 Claim daily shard allowance\n\n"
        "➷ /weekly\n〻 Claim weekly shards &amp; a Basic or Elite card!\n\n"
        "➷ /roll\n〻 Play bowling for 10 tries!\n\n"
        "➷ /throw\n〻 Play basketball for 10 tries!\n\n"
        "➷ /burn [Name]\n〻 Burn a card for quick Shards!\n\n"
        "➷ /referral\n〻 View your referral status and link!\n\n"
        "➷ /redeem [Code]\n〻 Redeem active promotional codes!\n\n"
        "➷ /mybanners\n〻 Browse your owned banners &amp; pick one as your profile's current banner!\n\n"
        "━━━━━━━━━━━━━━━━━\n"
        "々 Cards randomly appear in chats\n"
        "々 Type <code>/seize</code> [name] before others to grab them!</b>\n"
        "━━━━━━━━━━━━━━━━━"
    )


@main_router.message(Command("help"))
async def help_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    db  = load_db()
    pic = db.get("settings", {}).get("help_pic")
    kb  = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="メ Close", callback_data=f"close_msg|{uid_int}")]])
    if pic: await smart_reply_photo(message, photo=pic, caption=build_help_text(), reply_markup=kb, parse_mode=ParseMode.HTML)
    else:   await smart_reply(message, build_help_text(), reply_markup=kb, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data == "show_help")
async def show_help_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return
    await cq.answer()
    db  = load_db()
    pic = db.get("settings", {}).get("help_pic")
    kb  = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="メ Close", callback_data=f"close_msg|{uid_int}")]])
    await cq.message.delete()
    if pic: await cq.message.answer_photo(photo=pic, caption=build_help_text(), reply_markup=kb, parse_mode=ParseMode.HTML)
    else:   await cq.message.answer(build_help_text(), reply_markup=kb, parse_mode=ParseMode.HTML)


def build_start_text(user_id: int, first_name: str) -> str:
    safe_name = str(first_name).replace("<", "&lt;").replace(">", "&gt;")
    mention   = f'<a href="tg://user?id={user_id}">{safe_name}</a>'
    return (
        f"<b>Hҽყ {mention} ✨\n\n"
        f"I Aɱ <a href='https://t.me/Animenx_bot'>「 ANIME NEXUS ぁ 」</a> 🍫</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"➜ 🍜 Cσʅʅҽƈƚ   ԃιϝϝҽɾɳƚ Aɳιɱҽ ƈαɾԃʂ 🎴\n"
        f"➜ 🥂 Bυιʅԃ   ყσυɾ υɳιϙυҽ Cαɾԃ Dҽƈƙ ✦\n"
        f"➜ ⛺ Cσɱρҽƚҽ ωιƚԋ ƈσʅʅҽƈƚσɾʂ ɠʅσႦαʅʅყ 🌍\n\n"
        f"╰➤ Tσ υʂҽ ɱҽ, <a href='https://t.me/Animenx_bot?startgroup=true'> αԃԃ   ɱҽ ƚσ   ყσυɾ ɠɾσυρ </a>."
    )


def build_start_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Aԃԃ Tσ Gɾσυρ", url="https://t.me/Animenx_bot?startgroup=true")],
        [InlineKeyboardButton(text="🌐 Mαιɳ Gɾσυρ", url=config.MAIN_GROUP_LINK),
         InlineKeyboardButton(text="📖 Hҽʅρ", callback_data="show_help")],
        [InlineKeyboardButton(text="WҽႦ", url="https://t.me/Animenx_bot/webdeck")]
    ])


@main_router.message(Command("start"))
async def start_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    # ── Guide deep-link handler ──────────────────────────────────────────────
    # Reached via the "Click here 🪼" button /guide shows in groups.
    if command.args == "guide":
        await _send_guide_miniapp(message)
        return

    # ── Mine web app deep-link handler ───────────────────────────────────────
    # Reached via the "💬 Open in DM" button /webmine shows when run in a group.
    # Deferred import to avoid a circular import (mines.py imports from handlers.py).
    if command.args == "webmine":
        from mines import webmine_cmd
        await webmine_cmd(message)
        return

    # ── Referral deep-link handler ──────────────────────────────────────────
    if command.args and command.args.startswith("ref_"):
        referrer_id = command.args.split("_", 1)[1]
        buyer_id    = str(message.from_user.id)
        db          = load_db()

        if referrer_id != buyer_id and buyer_id not in db.get("users", {}):
            ensure_user(buyer_id,    message.from_user.first_name, message.from_user.username)
            ensure_user(referrer_id, "User")
            db = load_db()

            if not db["users"][buyer_id].get("referred_by"):
                db["users"][buyer_id]["referred_by"] = referrer_id
                save_db()

                buyer_mention = get_mention(buyer_id, message.from_user.first_name)
                try:
                    await bot.send_message(
                        chat_id=int(referrer_id),
                        text=(
                            "<b>「 👥 REFERRAL SYSTEM UPDATE 」</b>\n"
                            "━━━━━━━━━━━━━━━━━\n"
                            f"👤 {buyer_mention} registered with your link!\n"
                            "💡 They'll activate your reward once they seize their first card."
                        ),
                        parse_mode=ParseMode.HTML
                    )
                except Exception:
                    pass

    # ── Offline store deep-link handler ─────────────────────────────────────
    if command.args and command.args.startswith("buy_"):
        lid      = command.args.split("_", 1)[1]
        buyer_id = str(message.from_user.id)
        db       = ensure_user(buyer_id, message.from_user.first_name, message.from_user.username)

        if lid not in db.get("offline_store", {}):
            await smart_reply(message, "This listing does not exist or has already been sold.", parse_mode=ParseMode.HTML)
            return

        listing     = db["offline_store"][lid]
        card_id     = listing["card_id"]
        global_card = db["global_cards"].get(card_id)

        if not global_card:
            await smart_reply(message, "The card for this listing no longer exists.", parse_mode=ParseMode.HTML)
            return

        if listing["seller_id"] == buyer_id:
            await smart_reply(message, "You cannot buy your own listing.", parse_mode=ParseMode.HTML)
            return

        price       = listing["price"]
        rarity_str  = format_rarity(global_card["rarity"])
        rarity_name, _, rarity_icon = rarity_str.rpartition(" ")

        caption = (
            f"<b>「 PURCHASE CONFIRMATION 」\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"Name :</b> {global_card['name']}\n"
            f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
            f"<b>Anime :</b> {global_card.get('anime', 'Unknown')}\n"
            f"<b>Price :</b> {price} Shards\n\n"
            f"Do you wish to proceed with this purchase?"
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="Confirm", callback_data=f"cboff_{buyer_id}_{lid}"),
                InlineKeyboardButton(text="Cancel", callback_data="cancel_action")
            ]
        ])
        await smart_reply_photo(message, photo=global_card["file_id"], caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)
        return

    # ── Default start ────────────────────────────────────────────────────────
    db  = load_db()
    pic = db.get("settings", {}).get("start_pic")
    if pic:
        await message.reply_photo(
            photo=pic, caption=build_start_text(message.from_user.id, message.from_user.first_name),
            reply_markup=build_start_keyboard(), parse_mode=ParseMode.HTML
        )
    else:
        await message.reply(
            build_start_text(message.from_user.id, message.from_user.first_name),
            reply_markup=build_start_keyboard(), parse_mode=ParseMode.HTML
        )


@main_router.callback_query(F.data == "show_start")
async def show_start_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer("🔇 You are currently restricted.", show_alert=True)
        return
    await cq.answer()
    db  = load_db()
    pic = db.get("settings", {}).get("start_pic")
    await cq.message.delete()
    if pic: await cq.message.answer_photo(photo=pic, caption=build_start_text(cq.from_user.id, cq.from_user.first_name), reply_markup=build_start_keyboard(), parse_mode=ParseMode.HTML)
    else:   await cq.message.answer(build_start_text(cq.from_user.id, cq.from_user.first_name), reply_markup=build_start_keyboard(), parse_mode=ParseMode.HTML)


# ==========================================
# SHARDS BALANCE (/shards)
# ==========================================
@main_router.message(Command("shards"))
async def shards_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    db     = ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
    shards = db["users"][str(uid_int)].get("nexus_shards", 0)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Your Shards", url="https://t.me/Animenx_bot/webdeck")]
    ])
    await message.reply(
        f"<b>「 💠 NEXUS SHARDS ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<b>Your Current Shards ⦂ {shards} </b>💠 ",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )




# ==========================================
# REFERRAL OVERVIEW MENU (/referral)
# ==========================================
@main_router.message(Command("referral", "refer"))
async def referral_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id  = str(uid_int)
    db       = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    bot_info = await bot.get_me()

    ref_link       = f"https://t.me/{bot_info.username}?start=ref_{user_id}"
    referred_users = db["users"][user_id].get("referrals", [])
    ref_count      = len(referred_users)

    if ref_count < 5:
        next_milestone = "<b><i>5</i></b> (Reward: 1x Basic Card 🃏 &amp; 200 Shards)"
        progress       = f"<b><i>{ref_count}/5</i></b>"
    elif ref_count < 10:
        next_milestone = "<b><i>10</i></b> (Reward: 1x Elite Card ⚓ &amp; 500 Shards)"
        progress       = f"<b><i>{ref_count}/10</i></b>"
    elif ref_count < 20:
        next_milestone = "<b><i>20</i></b> (Reward: 1x Divine Card ❄️ &amp; 1500 Shards)"
        progress       = f"<b><i>{ref_count}/20</i></b>"
    else:
        target_loop    = 20 + (((ref_count - 20) // 20) + 1) * 20
        next_milestone = f"<b><i>{target_loop}</i></b> (Reward: 1x Divine Card ❄️ &amp; 2000 Shards)"
        progress       = f"<b><i>{ref_count}/{target_loop}</i></b>"

    msg = (
        f"<b>「 👥 REFERRAL PROGRAM ぁ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"<b><i>Verification Rule:</i></b> Invited users must seize <b>at least 1 card</b> to validate and trigger payouts.\n\n"
        f"🔗 <b><i>Your Unique Invite Link:</i></b>\n"
        f"<code>{ref_link}</code>\n\n"
        f"📊 <b><i>Your Referral Stats:</i></b>\n"
        f"  ├ Successful Invites: <b>{ref_count}</b>\n"
        f"  ├ Next Milestone: {next_milestone}\n"
        f"  └ Progress: {progress}\n\n"
        f"<blockquote expandable> 🏆 <b><i>Reward Milestone Rules:</i></b>\n"
        f"◍ Per Successful Invite: <b><i>+100 Shards</i></b> (Invited gets <b><i>+50</i></b>)\n"
        f"◍ Reach 5 Invites: <b><i>Basic Card 🃏 + 200 💠</i></b>\n"
        f"◍ Reach 10 Invites: <b><i>Elite Card ⚓ + 500 💠</i></b>\n"
        f"◍ Reach 20 Invites: <b><i>Divine Card ❄️ + 1,500 💠</i></b>\n"
        f"◍ Every 20 Invites after: <b><i>Divine Card ❄️ + 2,000 💠</i></b></blockquote>\n"
        f"━━━━━━━━━━━━━━━━━"
    )
    
    # "Copy Link" launches Telegram's share portal allowing mobile users to copy to clipboard in 1 tap
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="Share Link",
                    url=f"https://t.me/share/url?url={ref_link}&text=Join%20the%20Anime%20Nexus%20card%20collection%20adventure!"
                ),
                InlineKeyboardButton(
                    text=" Copy Link",
                    copy_text=CopyTextButton(text=ref_link)
                )
            ],
            [
                InlineKeyboardButton(
                    text="✕ Close",
                    callback_data=f"close_msg|{uid_int}"
                )
            ]
        ]
    )

    await message.reply(
        msg,
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )

# ==========================================
# PROMOTIONAL CODES ENGINE (/redeem)
# ==========================================
@main_router.message(Command("redeem"))
async def redeem_promo_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    # Small local helper: a promo redemption already updated the database by
    # the time most of these replies fire, so a send failure (flood control,
    # or the bot lacking permission to post text in this chat) shouldn't
    # blow up as an unhandled exception — just drop the confirmation text.
    async def safe_reply(text, **kwargs):
        try:
            await message.reply(text, **kwargs)
        except (TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest):
            pass

    if not command.args:
        await safe_reply("<b>Usage:</b> <code>/redeem &lt;CODE&gt;</code>\nExample: <code>/redeem SUMMERSHARDS</code>", parse_mode=ParseMode.HTML)
        return

    code = command.args.upper().strip()
    db   = load_db()
    promos = db.setdefault("promos", {})

    if code not in promos:
        await safe_reply("Invalid, expired, or incorrect promo code.", parse_mode=ParseMode.HTML)
        return

    promo   = promos[code]
    user_id = str(uid_int)

    if user_id in promo.setdefault("claimed_by", []):
        await safe_reply("You have already claimed this promo code!", parse_mode=ParseMode.HTML)
        return

    if len(promo["claimed_by"]) >= promo["max_claims"]:
        await safe_reply("This promo code has reached its maximum claim limit and is expired.", parse_mode=ParseMode.HTML)
        return

    ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    rewards_to_process = []
    if "rewards" in promo:
        rewards_to_process = promo["rewards"]
    else:
        legacy_type = promo.get("type", "shards")
        if legacy_type == "shards":
            rewards_to_process = [{"type": "shards", "shards": promo.get("shards", 0)}]
        elif legacy_type == "card":
            rewards_to_process = [{"type": "card", "rarity": promo.get("rarity", "Basic 🃏"), "amount": promo.get("amount", 1)}]

    shards_awarded  = 0
    cards_awarded   = []
    banners_awarded = []

    locked_animes = db.get("settings", {}).get("locked_animes", [])
    locked_animes_lower = [a.lower().strip() for a in locked_animes]

    for reward in rewards_to_process:
        if reward["type"] == "shards":
            shards_awarded += reward["shards"]
            db["users"][user_id]["nexus_shards"] = db["users"][user_id].get("nexus_shards", 0) + reward["shards"]

        elif reward["type"] == "card":
            target_rarity = format_rarity(reward["rarity"])
            card_pool     = {k: v for k, v in db.get("global_cards", {}).items()
                             if format_rarity(v["rarity"]) == target_rarity
                             and v["anime"].lower().strip() not in locked_animes_lower}

            if card_pool:
                quantity = reward.get("amount", 1)

                # `quantity` is how many separate cards to draw, not a stack
                # count on one card — card:Divine:2 means two independent
                # pulls (each its own card id, each its own line in the
                # confirmation), the same as running the reward twice. Not
                # "one Divine card x2".
                user_cards = db["users"][user_id].setdefault("cards", {})
                for _ in range(quantity):
                    # 20% chance to allow a duplicate (a card the user already
                    # owns, including ones just drawn earlier in this same
                    # loop). The other 80% of the time, pick from cards they
                    # don't have yet so redeems usually feel like real
                    # progress instead of just stacking a card they already
                    # hold.
                    user_owned_cards = db["users"][user_id].get("cards", {})
                    allow_duplicate  = random.randint(1, 100) <= 20
                    eligible_pool    = card_pool
                    if not allow_duplicate:
                        fresh_pool = {k: v for k, v in card_pool.items() if k not in user_owned_cards}
                        if fresh_pool:
                            eligible_pool = fresh_pool
                        # If they already own every card in this rarity's pool, fall
                        # back to the full pool — a duplicate is unavoidable anyway.

                    card_id, card_data = random.choice(list(eligible_pool.items()))

                    if card_id not in user_cards:
                        user_cards[card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
                    user_cards[card_id]["amount"] += 1
                    db["users"][user_id]["total_claimed"] = db["users"][user_id].get("total_claimed", 0) + 1
                    cards_awarded.append((card_data, 1))

        elif reward["type"] == "banner":
            # The global default is always excluded here — everyone gets it
            # free on /profile already, so nobody should be able to "win"
            # it from a promo. If nothing eligible is left (e.g. the target
            # banner was removed, or only the default remains), this reward
            # is silently skipped rather than falling back to the default.
            target_bid = banners.pick_redeemable_banner_id(db, reward.get("banner_id", "r"))
            if target_bid:
                user_banners = db["users"][user_id].setdefault("banners", {})
                if target_bid not in user_banners:
                    user_banners[target_bid] = {"amount": 0}
                qty = reward.get("amount", 1)
                user_banners[target_bid]["amount"] += qty
                banner_meta = db.get("banners", {}).get(target_bid, {})
                banners_awarded.append((banner_meta.get("name", "Unnamed"), target_bid, qty))

    promo["claimed_by"].append(user_id)
    await check_and_reward_referral(user_id, db)
    save_db()

    if shards_awarded > 0:
        log_action(db, user_id, {
            "type": "promo_shards",
            "amount": shards_awarded,
            "code": code,
            "chat_id": message.chat.id,
            "chat_title": message.chat.title or message.chat.first_name or "DM"
        })

    msg_lines = [
        f"<b>「 🎁 PROMO CODE REDEEMED 」</b>",
        f"━━━━━━━━━━━━━━━━━",
        f"🎫 Code: <code>{code}</code>\n",
        f"📦 <b>Acquired Rewards:</b>"
    ]
    if shards_awarded > 0:
        msg_lines.append(f" • 💠 <b>Nexus Shards:</b> +{shards_awarded}")
    for cdata, qty in cards_awarded:
        disp_rarity = format_rarity(cdata["rarity"])
        msg_lines.append(f" • 🎴 <b>{cdata['name']}</b> ({disp_rarity}) x{qty}")
    for bname, bid, qty in banners_awarded:
        msg_lines.append(f" • 🖼️ <b>{bname}</b> Banner (ID {bid}) x{qty} — check /mybanners")
    msg_lines.append("\n━━━━━━━━━━━━━━━━━")
    caption = "\n".join(msg_lines)

    if cards_awarded:
        first_card_data = cards_awarded[0][0]
        try:
            await message.reply_photo(photo=first_card_data["file_id"], caption=caption, parse_mode=ParseMode.HTML, has_spoiler=True)
        except Exception:
            await safe_reply(caption, parse_mode=ParseMode.HTML)
    elif banners_awarded:
        first_bid = banners_awarded[0][1]
        banner_meta = db.get("banners", {}).get(first_bid, {})
        photo_ok = bool(banner_meta) and await banners.ensure_banner_file(first_bid, banner_meta)
        if photo_ok:
            try:
                await message.reply_photo(photo=FSInputFile(banner_meta["file_path"]), caption=caption, parse_mode=ParseMode.HTML)
            except Exception:
                await safe_reply(caption, parse_mode=ParseMode.HTML)
        else:
            await safe_reply(caption, parse_mode=ParseMode.HTML)
    else:
        await safe_reply(caption, parse_mode=ParseMode.HTML)


# ==========================================
# CARD LOOKUP + OWNERSHIP SEARCH (/search)
# ==========================================
WHOOWNS_COST = 200


def _find_owned_card(db: dict, user_id: str, query: str):
    """Fuzzy-matches a query against cards the user themself owns."""
    query      = query.lower().strip()
    user_cards = db["users"].get(user_id, {}).get("cards", {})
    best_match = None
    best_ratio = 0.0

    for cid, cdata in user_cards.items():
        if cdata.get("amount", 0) <= 0:
            continue
        name_lower = cdata["name"].lower()
        if query == name_lower:
            return cid
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = cid
        else:
            ratio = difflib.SequenceMatcher(None, query, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = cid

    return best_match


def _get_owners(db: dict, card_id: str):
    """Returns a list of (user_id, name, amount) for every user owning the card, sorted by amount desc."""
    owners = [
        (uid, udata.get("name", "Unknown"), udata["cards"][card_id].get("amount", 0))
        for uid, udata in db.get("users", {}).items()
        if card_id in udata.get("cards", {}) and udata["cards"][card_id].get("amount", 0) > 0
    ]
    owners.sort(key=lambda x: x[2], reverse=True)
    return owners


def _build_card_lookup_caption(global_card: dict) -> str:
    display_rarity = format_rarity(global_card["rarity"])
    return (
        "<b>「 Card Lookup 🔍 」\n"
        "<blockquote>╺╺╺╺╺╺╺╺╺╺╺╺╺╺╺</blockquote>\n"
        f"⦿ <i>Character </i>» {global_card['name']} ⟪ {global_card['anime']} ⟫\n"
        f"⦾ <i>Rarity</i> » {display_rarity}\n"
        "<blockquote>╺╺╺╺╺╺╺╺╺╺╺╺╺╺╺</blockquote></b>"
    )


@main_router.message(Command("search"))
async def search_card_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if not command.args:
        await message.reply("<b>Usage:</b> <code>/search &lt;card name&gt;</code>\nExample: <code>/search Makima</code>", parse_mode=ParseMode.HTML)
        return

    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    if not db["users"].get(user_id, {}).get("cards"):
        await message.reply("You don't own any cards yet. Collect some first!", parse_mode=ParseMode.HTML)
        return

    card_id = _find_owned_card(db, user_id, command.args)
    if not card_id:
        await message.reply(f"You don't own any card matching <b>{command.args}</b>.", parse_mode=ParseMode.HTML)
        return

    global_data = db["global_cards"][card_id]
    caption     = _build_card_lookup_caption(global_data)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"🌐 𝗪𝗵𝗼 𝗼𝘄𝗻? ({WHOOWNS_COST} 💠)", callback_data=f"whoowns_{user_id}_{card_id}")]
    ])

    try:
        await message.reply_photo(
            photo=global_data.get("file_id"),
            caption=caption,
            reply_markup=kb,
            parse_mode=ParseMode.HTML,
            has_spoiler=True
        )
    except Exception:
        await message.reply(caption, reply_markup=kb, parse_mode=ParseMode.HTML)


DATA_CARD_AUTODELETE_SECS = 60


def _find_global_card(db: dict, query: str):
    """Fuzzy-matches a query against every card in the global pool, regardless of ownership."""
    query      = query.lower().strip()
    best_match = None
    best_ratio = 0.0

    for cid, cdata in db.get("global_cards", {}).items():
        name_lower = cdata["name"].lower()
        if query == name_lower:
            return cid
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = cid
        else:
            ratio = difflib.SequenceMatcher(None, query, name_lower).ratio()
            if ratio > 0.6 and ratio > best_ratio:
                best_ratio = ratio
                best_match = cid

    return best_match


def _build_data_caption(global_card: dict) -> str:
    display_rarity = format_rarity(global_card["rarity"])
    return (
        "<b>╭─────〔 Card Data 〕─────╮</b>\n\n"
        f"<b>⦿ Character » </b>{global_card['name']} ⟪ {global_card['anime']} ⟫\n"
        f"<b>⦾ Rarity » </b>{display_rarity}"
    )


async def _autodelete_data_card(chat_id: int, msg_id: int):
    await asyncio.sleep(DATA_CARD_AUTODELETE_SECS)
    try:
        await bot.delete_message(chat_id, msg_id)
    except Exception:
        pass


@main_router.message(Command("data"))
async def data_card_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if message.chat.type != ChatType.PRIVATE:
        bot_info = await bot.get_me()
        dm_link = f"https://t.me/{bot_info.username}"
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Come here", url=dm_link)]
        ])
        await message.reply(
            "🔒 This command can only be used in the bot's DM.",
            parse_mode=ParseMode.HTML,
            reply_markup=kb
        )
        return

    if not command.args:
        await message.reply("<b>Usage:</b> <code>/data &lt;card name&gt;</code>\nExample: <code>/data Makima</code>", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    card_id = _find_global_card(db, command.args)
    if not card_id:
        await message.reply(f"No card found matching <b>{command.args}</b>.", parse_mode=ParseMode.HTML)
        return

    global_data = db["global_cards"][card_id]
    caption = _build_data_caption(global_data)

    try:
        sent = await message.reply_photo(
            photo=global_data.get("file_id"),
            caption=caption,
            parse_mode=ParseMode.HTML,
            protect_content=True,
            has_spoiler=True
        )
    except Exception:
        sent = await message.reply(caption, parse_mode=ParseMode.HTML, protect_content=True)

    asyncio.create_task(_autodelete_data_card(sent.chat.id, sent.message_id))


@main_router.callback_query(F.data.startswith("whoowns_"))
async def who_owns_cb(cq: CallbackQuery):
    parts          = cq.data.split("_", 2)
    searcher_id    = parts[1]
    card_id        = parts[2]

    if str(cq.from_user.id) != searcher_id:
        await cq.answer("This isn't your search!", show_alert=True)
        return

    db          = load_db()
    global_card = db.get("global_cards", {}).get(card_id)
    if not global_card:
        await cq.answer("This card no longer exists.", show_alert=True)
        return

    user_data = db["users"].get(searcher_id, {})
    balance   = user_data.get("nexus_shards", 0)
    if balance < WHOOWNS_COST:
        await cq.answer(f"You need {WHOOWNS_COST} 💠 Shards to check owners. You have {balance} 💠.", show_alert=True)
        return

    owners = _get_owners(db, card_id)
    if not owners:
        await cq.answer("Nobody owns this card yet!", show_alert=True)
        return

    # Build the owner list as its own text message rather than stuffing it
    # into the photo caption — Telegram caps photo captions at 1024 chars,
    # and with enough owners that limit gets blown past, edit_caption throws,
    # and (since shards were deducted first) the user was charged for a
    # list that never rendered. Text messages allow up to 4096 chars, so
    # paginate defensively at a much higher owner count instead.
    OWNERS_PER_MSG = 80
    owner_lines_all = [f"{name} ({uid}) - {amount}" for uid, name, amount in owners]

    header = _build_card_lookup_caption(global_card)
    chunks = []
    for i in range(0, len(owner_lines_all), OWNERS_PER_MSG):
        chunk_lines = owner_lines_all[i:i + OWNERS_PER_MSG]
        chunks.append("\n".join(chunk_lines))

    try:
        # Remove the button but leave the original caption/text untouched —
        # this never risks a length error since we're not rewriting the caption.
        await cq.message.edit_reply_markup(reply_markup=None)

        first_text = f"{header}\n\n👥 <b>{len(owners)} owner(s):</b>\n{chunks[0]}"
        await cq.message.reply(first_text, parse_mode=ParseMode.HTML)
        for chunk in chunks[1:]:
            await cq.message.reply(chunk, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[WHOOWNS] Failed to deliver owner list for {card_id}: {e}")
        await cq.answer("Something went wrong showing the owner list — you weren't charged.", show_alert=True)
        return

    # Only deduct shards after the list has actually been delivered.
    db["users"][searcher_id]["nexus_shards"] = balance - WHOOWNS_COST
    save_db()
    await cq.answer(f"{WHOOWNS_COST} 💠 Shards deducted.")


# ==========================================
# USER CARD BROWSER (/cardlists)
# Anime -> Rarity -> owned/not-owned card names. Same hashing trick as the
# admin /cards browser (anime names can be long/contain "|", so callback_data
# carries a short stable hash instead of the raw title).
# ==========================================
import hashlib as _cl_hashlib

def _cl_anime_hash_key(anime_name: str) -> str:
    return _cl_hashlib.md5(anime_name.encode("utf-8")).hexdigest()[:12]


def _cl_anime_key_lookup(db: dict, anime_key: str):
    cards = db.get("global_cards", {})
    anime_titles = set(c["anime"] for c in cards.values())
    for anime in anime_titles:
        if _cl_anime_hash_key(anime) == anime_key:
            return anime
    return None


CARDLISTS_PER_PAGE = 10  # laid out as 4 + 4 + 2 button rows


async def _show_cardlists_anime_page(event, edit=False, page=0, owner_id=None):
    if owner_id is None:
        owner_id = event.from_user.id

    db = load_db()
    cards = db.get("global_cards", {})
    hidden_animes = db.get("settings", {}).get("hidden_animes", [])
    hidden_lower = [a.lower().strip() for a in hidden_animes]
    anime_titles = sorted(
        a for a in set(c["anime"] for c in cards.values())
        if a.lower().strip() not in hidden_lower
    )

    if not anime_titles:
        text = "<b>「 Anime List 🪐 」</b>\n━━━━━━━━━━━━━━━━━\nNo cards are registered yet."
        if edit and isinstance(event, CallbackQuery):
            try:
                await event.message.edit_text(text, parse_mode=ParseMode.HTML)
            except Exception:
                pass
        else:
            target = event.message if isinstance(event, CallbackQuery) else event
            await target.reply(text, parse_mode=ParseMode.HTML)
        return

    total = len(anime_titles)
    total_pages = max(1, (total - 1) // CARDLISTS_PER_PAGE + 1)
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0

    start = page * CARDLISTS_PER_PAGE
    end = min(start + CARDLISTS_PER_PAGE, total)
    sliced = anime_titles[start:end]

    lines = []
    for i, anime in enumerate(sliced):
        idx = start + i + 1
        connector = "╰─" if i == len(sliced) - 1 else "├─"
        lines.append(f"{connector} [{idx}] {anime}")

    text = (
        "<b>「 Anime List 🪐 」\n"
        "━━━━━━━━━━━━━━━━━\n"
        + "\n".join(lines) +
        "\n━━━━━━━━━━━━━━━━━\n"
        f"<blockquote>Page {page+1}/{total_pages}</blockquote></b>"
    )

    # Number buttons laid out 4 + 4 + 2
    number_buttons = [
        InlineKeyboardButton(text=str(start + i + 1), callback_data=f"cl_an|{owner_id}|{_cl_anime_hash_key(anime)}")
        for i, anime in enumerate(sliced)
    ]
    rows = []
    for chunk_size in (4, 4, 2):
        if not number_buttons: break
        rows.append(number_buttons[:chunk_size])
        number_buttons = number_buttons[chunk_size:]

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="« Prev", callback_data=f"cl_page|{owner_id}|{page-1}"))
    if end < total:
        nav.append(InlineKeyboardButton(text="Next »", callback_data=f"cl_page|{owner_id}|{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="✕ Close", callback_data=f"close_msg|{owner_id}")])

    markup = InlineKeyboardMarkup(inline_keyboard=rows)

    if edit and isinstance(event, CallbackQuery):
        try:
            await event.message.edit_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)
        except Exception:
            pass
    else:
        target = event.message if isinstance(event, CallbackQuery) else event
        await target.reply(text, reply_markup=markup, parse_mode=ParseMode.HTML)


def _cl_find_anime(db: dict, query: str):
    """Fuzzy-resolves a typed anime name to the exact title stored in
    global_cards. Exact match first, then substring, then similarity ratio —
    same approach _find_owned_card uses for card names. Anime hidden via
    /hide are excluded so they can't be reached by typing the name directly."""
    cards = db.get("global_cards", {})
    hidden_lower = [a.lower().strip() for a in db.get("settings", {}).get("hidden_animes", [])]
    anime_titles = sorted(
        a for a in set(c["anime"] for c in cards.values())
        if a.lower().strip() not in hidden_lower
    )
    query_lower = query.lower().strip()

    for anime in anime_titles:
        if anime.lower() == query_lower:
            return anime

    best_match, best_ratio = None, 0.0
    for anime in anime_titles:
        anime_lower = anime.lower()
        if query_lower in anime_lower:
            ratio = 0.8 + (len(query_lower) / len(anime_lower)) * 0.1
        else:
            ratio = difflib.SequenceMatcher(None, query_lower, anime_lower).ratio()
        if ratio > best_ratio:
            best_ratio = ratio
            best_match = anime

    return best_match if best_ratio > 0.6 else None


@main_router.message(Command("cardlists"))
async def cardlists_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if command.args:
        db = load_db()
        anime_name = _cl_find_anime(db, command.args)
        if not anime_name:
            await message.reply(f"No anime matching <b>{command.args}</b> was found.", parse_mode=ParseMode.HTML)
            return
        await _show_cardlists_rarity_picker(message, anime_name)
        return

    await _show_cardlists_anime_page(message)


@main_router.callback_query(F.data.startswith("cl_page|"))
async def cardlists_page_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id):
        await cq.answer()
        return

    parts = cq.data.split("|")
    owner_id = parts[1]
    page = int(parts[2])

    if str(cq.from_user.id) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    await cq.answer()
    await _show_cardlists_anime_page(cq, edit=True, page=page, owner_id=owner_id)


async def _show_cardlists_rarity_picker(event, anime_name: str, edit=False, owner_id=None):
    """Renders the rarity-choice screen for a given anime. `event` is either
    a Message (fresh reply, e.g. from /cardlists <anime>) or a CallbackQuery
    (edit in place, e.g. from tapping an anime number button)."""
    if owner_id is None:
        owner_id = event.from_user.id

    anime_key = _cl_anime_hash_key(anime_name)

    db = load_db()
    anime_cards = {cid: c for cid, c in db.get("global_cards", {}).items() if c["anime"] == anime_name}
    owned_cards = db.get("users", {}).get(str(owner_id), {}).get("cards", {})

    def _owned_total(match_fn):
        total = owned = 0
        for cid, c in anime_cards.items():
            if match_fn(format_rarity(c["rarity"])):
                total += 1
                if cid in owned_cards and owned_cards[cid].get("amount", 0) > 0:
                    owned += 1
        return owned, total

    divine_owned, divine_total = _owned_total(lambda r: "Divine" in r)
    elite_owned, elite_total   = _owned_total(lambda r: "Elite" in r)
    basic_owned, basic_total   = _owned_total(lambda r: "Basic" in r)
    total_owned = divine_owned + elite_owned + basic_owned
    total_all   = divine_total + elite_total + basic_total

    text = (
        f"<b>Anime - 「 {anime_name} 」\n"
        f"Total Cards: ({total_owned}/{total_all})\n"
        f"[❄️] Total divine : ({divine_owned}/{divine_total})\n"
        f"[⚓] Total elite : ({elite_owned}/{elite_total})\n"
        f"[🎴] Total Basic: ({basic_owned}/{basic_total})</b>\n\n"
        "<blockquote>Choose a rarity:</blockquote>"
    )

    top_row = [r for r in RARITIES if r != "Basic 🃏"]
    bottom_row = [r for r in RARITIES if r == "Basic 🃏"]

    rarity_rows = []
    if top_row:
        rarity_rows.append([
            InlineKeyboardButton(text=r, callback_data=f"cl_r|{owner_id}|{anime_key}|{RARITY_SAFE[r]}|0")
            for r in top_row
        ])
    if bottom_row:
        rarity_rows.append([
            InlineKeyboardButton(text=r, callback_data=f"cl_r|{owner_id}|{anime_key}|{RARITY_SAFE[r]}|0")
            for r in bottom_row
        ])

    kb = InlineKeyboardMarkup(inline_keyboard=rarity_rows + [
        [InlineKeyboardButton(text="« Back to Anime List", callback_data=f"cl_page|{owner_id}|0")],
        [InlineKeyboardButton(text="✕ Close", callback_data=f"close_msg|{owner_id}")]
    ])

    if edit and isinstance(event, CallbackQuery):
        try:
            await event.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception:
            pass
    else:
        target = event.message if isinstance(event, CallbackQuery) else event
        await target.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("cl_an|"))
async def cardlists_rarity_picker_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id):
        await cq.answer()
        return

    parts = cq.data.split("|")
    owner_id = parts[1]
    anime_key = parts[2]

    if str(cq.from_user.id) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    db = load_db()
    anime_name = _cl_anime_key_lookup(db, anime_key)
    if not anime_name:
        await cq.answer("This anime no longer exists. Please reopen /cardlists.", show_alert=True)
        return

    hidden_lower = [a.lower().strip() for a in db.get("settings", {}).get("hidden_animes", [])]
    if anime_name.lower().strip() in hidden_lower:
        await cq.answer("This anime is no longer available. Please reopen /cardlists.", show_alert=True)
        return

    await _show_cardlists_rarity_picker(cq, anime_name, edit=True, owner_id=owner_id)
    await cq.answer()


@main_router.callback_query(F.data.startswith("cl_r|"))
async def cardlists_card_view_cb(cq: CallbackQuery):
    uid_int = cq.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        await cq.answer()
        return

    parts = cq.data.split("|")
    owner_id     = parts[1]
    anime_key    = parts[2]
    rarity_safe  = parts[3]
    page         = int(parts[4])

    if str(uid_int) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    db = load_db()
    anime_name = _cl_anime_key_lookup(db, anime_key)
    if not anime_name:
        await cq.answer("This anime no longer exists. Please reopen /cardlists.", show_alert=True)
        return

    rarity_display = SAFE_RARITY.get(rarity_safe)
    if not rarity_display:
        await cq.answer("Unknown rarity.", show_alert=True)
        return

    all_cards = db.get("global_cards", {})
    filtered = [
        (cid, c) for cid, c in all_cards.items()
        if c["anime"] == anime_name and RARITY_SAFE.get(format_rarity(c["rarity"])) == rarity_safe
    ]

    if not filtered:
        await cq.answer(f"No {rarity_display} cards available for {anime_name}.", show_alert=True)
        return

    user_id = str(uid_int)
    owned_cards = db.get("users", {}).get(user_id, {}).get("cards", {})

    per_page = BROWSE_PER_PAGE
    total = len(filtered)
    total_pages = max(1, (total - 1) // per_page + 1)
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0

    start = page * per_page
    end = start + per_page
    sliced = filtered[start:end]

    owned_count = sum(1 for cid, _ in filtered if cid in owned_cards and owned_cards[cid].get("amount", 0) > 0)

    lines = []
    for cid, c in sliced:
        is_owned = cid in owned_cards and owned_cards[cid].get("amount", 0) > 0
        dot = "⬤" if is_owned else "◯"
        lines.append(f"{dot} {c['name']}")

    text = (
        f"<b>「 {anime_name} — {rarity_display} 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        + "\n".join(lines) +
        "\n━━━━━━━━━━━━━━━━━\n"
        f"<blockquote><b>Collected: ({owned_count}/{total})\n⬤  - Owned \n◯  - not owned</b></blockquote>"
    )
    if total_pages > 1:
        text += f"\nPage <b>{page+1}/{total_pages}</b>"

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="« Prev", callback_data=f"cl_r|{owner_id}|{anime_key}|{rarity_safe}|{page-1}"))
    if end < total:
        nav.append(InlineKeyboardButton(text="Next »", callback_data=f"cl_r|{owner_id}|{anime_key}|{rarity_safe}|{page+1}"))

    rows = []
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="« Back to Rarities", callback_data=f"cl_an|{owner_id}|{anime_key}")])
    rows.append([InlineKeyboardButton(text="✕ Close", callback_data=f"close_msg|{owner_id}")])

    kb = InlineKeyboardMarkup(inline_keyboard=rows)
    try:
        await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()


# ==========================================
# GUIDE WEBSITE (/guide)
# ==========================================
GUIDE_URL = "https://animated-cajeta-10b450.netlify.app/"


async def _send_guide_miniapp(message: Message):
    """Sends the actual guide message with the Open Guide Mini App button.
    Only valid in private chats — web_app buttons don't work in groups."""
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📖 Open Guide", web_app=WebAppInfo(url=GUIDE_URL))]
    ])
    await message.reply(
        "<b>「 📖 GUIDE ぁ 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<b>Everything about collecting, trading, and the shard economy — "
        "commands, drops, the store, stock market, mines, and more, all in one place</b>.\n"
        "━━━━━━━━━━━━━━━━━",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )


@main_router.message(Command("guide"))
async def guide_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    if message.chat.type == ChatType.PRIVATE:
        await _send_guide_miniapp(message)
        return

    # In groups: web_app buttons aren't allowed on a normal message, so
    # instead point the user to DM the bot — clicking the button deep-links
    # straight into /start?guide, which auto-opens the guide there.
    bot_info = await bot.get_me()
    deep_link = f"https://t.me/{bot_info.username}?start=guide"

    # If used as a reply, tag whoever was replied to — unless that's a bot
    # account or an anonymous channel post (sender_chat set, no real
    # from_user), in which case there's no one sensible to tag/DM, so it
    # just falls back to tagging the person who ran the command.
    reply_msg = message.reply_to_message
    if reply_msg and reply_msg.from_user and not reply_msg.from_user.is_bot:
        target_mention = get_mention(reply_msg.from_user.id, reply_msg.from_user.first_name)
    else:
        target_mention = get_mention(message.from_user.id, message.from_user.first_name)

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Click here ", url=deep_link)]
    ])
    await message.reply(
        f" {target_mention}, <b>Guide available on DM!</b>",
        reply_markup=kb,
        parse_mode=ParseMode.HTML
    )


# ==========================================
# SUPPORT QUERY SYSTEM — SUBMISSION (/qry)
# Users submit a question by replying to a message (reply is mandatory).
# It's logged to QUERY_GROUP_ID with a ticket number (Qry01, Qry02, ...).
# Admin answering (/aq) and listing unanswered tickets (/nansq) live in
# a_handlers.py.
# ==========================================
_QUERY_MEDIA_ATTRS = ("photo", "document", "video", "animation", "sticker", "voice", "audio", "video_note")


def _next_query_id(db: dict) -> str:
    settings = db.setdefault("settings", {})
    counter = settings.get("query_counter", 0) + 1
    settings["query_counter"] = counter
    return f"Qry{counter:02d}"


QUERY_USAGE_TEXT = "<b>Usage:</b> Reply to a message with <b>/qry</b> to submit it as your question."


@main_router.message(Command("qry"))
async def submit_query_cmd(message: Message, command: CommandObject):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    reply_msg = message.reply_to_message
    if not reply_msg:
        await message.reply(QUERY_USAGE_TEXT, parse_mode=ParseMode.HTML)
        return

    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)

    # Question text: typed args take priority; otherwise use the text/caption
    # of the message being replied to.
    question_text = (command.args or "").strip()
    if not question_text:
        question_text = (reply_msg.text or reply_msg.caption or "").strip()

    if not question_text:
        await message.reply("<b>That message has no text to use as a question.</b> Add your question after <b>/qry</b> instead.", parse_mode=ParseMode.HTML)
        return

    if len(question_text) < QUERY_MIN_LEN:
        await message.reply("<b>Your query is too short.</b> Please describe your issue in more detail.", parse_mode=ParseMode.HTML)
        return
    if len(question_text) > QUERY_MAX_LEN:
        await message.reply(f"<b>Your query is too long</b> (max {QUERY_MAX_LEN} characters).", parse_mode=ParseMode.HTML)
        return

    # --- Anti-spam: per-user cooldown ---
    now = time.time()
    last = _query_cooldowns.get(user_id, 0.0)
    if uid_int not in ADMIN_IDS and now - last < QUERY_COOLDOWN_SECS:
        rem = QUERY_COOLDOWN_SECS - (now - last)
        await message.reply(f"<b>Slow down!</b> You can submit another query in <b>{format_wait_mmss(rem)}</b>.", parse_mode=ParseMode.HTML)
        return

    # --- Anti-spam: daily submission cap ---
    user_data = db["users"][user_id]
    daily = get_query_daily_tracker(user_data)
    if uid_int not in ADMIN_IDS and daily["count"] >= QUERY_DAILY_LIMIT:
        await message.reply(f"<b>Daily limit reached.</b> You can submit up to <b>{QUERY_DAILY_LIMIT}</b> queries per day — please try again tomorrow.", parse_mode=ParseMode.HTML)
        return

    # --- Anti-spam: cap on open/unanswered tickets ---
    pending_count = sum(
        1 for q in db.get("queries", {}).values()
        if q.get("user_id") == user_id and q.get("status") == "pending"
    )
    if uid_int not in ADMIN_IDS and pending_count >= QUERY_MAX_PENDING:
        await message.reply(f"<b>Too many open queries.</b> You already have <b>{pending_count}</b> unanswered — please wait for a response before submitting more.", parse_mode=ParseMode.HTML)
        return

    # --- Create the ticket ---
    qry_id = _next_query_id(db)
    db["queries"][qry_id] = {
        "user_id": user_id,
        "name": message.from_user.first_name,
        "username": message.from_user.username,
        "question": question_text,
        "status": "pending",
        "created_at": int(time.time()),
        "log_msg_id": None,
        "answer": None,
        "answered_by": None,
        "answered_at": None
    }

    _query_cooldowns[user_id] = now
    daily["count"] += 1
    save_db()

    # --- Log to the query group ---
    asker_mention = get_mention(uid_int, message.from_user.first_name)
    safe_question = question_text.replace("<", "&lt;").replace(">", "&gt;")
    log_text = (
        "<b><u>New Query</u></b>\n\n"
        f"🎫 <b>Ticket :</b> {qry_id}\n"
        f"<b>From :</b> {asker_mention} ({uid_int})\n"
        f"<b>Question ❓:</b>\n"
        f"<blockquote>{safe_question}</blockquote>\n\n"
        f"<b>↳ Reply With : </b> /aq {qry_id}"
    )

    try:
        # Only forward the replied message itself when it carries media the
        # text log can't represent (a plain-text reply is already quoted
        # above, so copying it too would just post the same content twice).
        if any(getattr(reply_msg, attr, None) for attr in _QUERY_MEDIA_ATTRS):
            try:
                await bot.copy_message(chat_id=QUERY_GROUP_ID, from_chat_id=message.chat.id, message_id=reply_msg.message_id)
            except Exception:
                pass
        sent = await bot.send_message(chat_id=QUERY_GROUP_ID, text=log_text, parse_mode=ParseMode.HTML)
        db["queries"][qry_id]["log_msg_id"] = sent.message_id
        save_db()
    except Exception as e:
        print(f"[QUERY] Failed to log {qry_id} to group: {e}")

    await message.reply(
        f"✅ <b>Query submitted.</b>\n"
        f"🎫 <b>Ticket ID</b>: {qry_id}\n\n"
        f"<i>An admin will reply to you here in DM once it's answered.</i>",
        parse_mode=ParseMode.HTML
    )

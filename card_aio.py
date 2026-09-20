import logging
import logging.handlers
import os
import random
import asyncio
import signal
import sys
import time
from contextlib import asynccontextmanager

import uvicorn
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from aiogram import BaseMiddleware
from aiogram.types import Message, CallbackQuery, ChatMemberUpdated
from aiogram.enums import ChatType, ParseMode
from aiogram.filters import ChatMemberUpdatedFilter, JOIN_TRANSITION
from aiogram.exceptions import TelegramNetworkError, TelegramRetryAfter
from aiohttp import ClientConnectionError, ServerDisconnectedError

# ==========================================
# LOGGING CONFIGURATION
# =========================================
os.makedirs("logs", exist_ok=True)
_log_formatter = logging.Formatter(
    "%(asctime)s - %(levelname)s - %(name)s - %(message)s"
)

_console_handler = logging.StreamHandler()
_console_handler.setFormatter(_log_formatter)

_file_handler = logging.handlers.RotatingFileHandler(
    "logs/bot.log", maxBytes=5_000_000, backupCount=5, encoding="utf-8"
)
_file_handler.setFormatter(_log_formatter)

logging.basicConfig(level=logging.INFO, handlers=[_console_handler, _file_handler])
logger = logging.getLogger("AnimeNexus")

logging.getLogger("aiogram.event").setLevel(logging.WARNING)


def _log_uncaught_exceptions(exc_type, exc_value, exc_traceback):
    """Catch-all for exceptions to prevent unhandled process crashes."""
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_traceback)
        return
    logger.critical("UNCAUGHT EXCEPTION - process would have crashed:",
                    exc_info=(exc_type, exc_value, exc_traceback))


sys.excepthook = _log_uncaught_exceptions


def create_logged_task(coro, name: str):
    """Wrap asyncio task creation to catch and log task crashes."""
    task = asyncio.create_task(coro, name=name)

    def _on_done(t: asyncio.Task):
        if t.cancelled():
            return
        exc = t.exception()
        if exc is not None:
            logger.critical(f"Background task '{name}' crashed:", exc_info=exc)

    task.add_done_callback(_on_done)
    return task


# ==========================================
# SYSTEM IMPORTS & CONFIGURATION
# ==========================================
import config
from config import (
    bot, dp, main_router, check_autoleave, is_ghost_banned, check_spam,
    is_shadow_banned, ensure_group, periodic_save, backup_to_group,
    load_from_group, load_settings, _flush_db
)

# Import module handlers to register routing
import handlers
import deck
import a_handlers
import vlog
import store
import market
import mines
import gcard

from handlers import trigger_drop
from market import market_engine_loop
from versus import active_versus, versus_router
from vlog import vlog_cleanup_loop
from mines import mines_router
from deck import deck_api  # <--- IMPORT DECK API ROUTER
from store import store_api  # <--- IMPORT STORE API ROUTER


# ==========================================
# BOT ADDED TO GROUP LOG
# ==========================================
@dp.my_chat_member(ChatMemberUpdatedFilter(JOIN_TRANSITION))
async def bot_added_to_group(event: ChatMemberUpdated):
    chat = event.chat
    added_by = event.from_user

    if chat.type not in [ChatType.GROUP, ChatType.SUPERGROUP]:
        return

    config.ensure_group(chat.id, chat.title or str(chat.id))

    if added_by:
        try:
            await bot.send_message(
                chat_id=added_by.id,
                text=(
                    f"🌸 Thanks for adding me to <b>{chat.title}</b> (<code>{chat.id}</code>)!\n\n"
                    f"Keep supporting 🤍"
                ),
                parse_mode="HTML"
            )
        except Exception as e:
            logger.warning(f"[DM] Could not message adder {added_by.id}: {e}")

    try:
        added_mention = (
            f'<a href="tg://user?id={added_by.id}">'
            f'{str(added_by.first_name).replace("<","&lt;").replace(">","&gt;")}</a>'
            if added_by else "Unknown"
        )
        from datetime import datetime, timezone as _tz
        await bot.send_message(
            chat_id=config.DATABASE_BACKUP_ID,
            text=(
                f"<b>「 ➕ BOT ADDED TO GROUP 」</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"• 🏘️ <b>Group:</b> {chat.title} (<code>{chat.id}</code>)\n"
                f"• 👤 <b>Added By:</b> {added_mention} (<code>{added_by.id if added_by else '?'}</code>)\n"
                f"• 🕐 <b>Time:</b> {datetime.now(_tz.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
                f"━━━━━━━━━━━━━━━━━━━━━━"
            ),
            parse_mode="HTML"
        )
    except Exception as e:
        logger.warning(f"[LOG] bot_added_to_group log failed: {e}")


# ==========================================
# GLOBAL GUARD MIDDLEWARE
# ==========================================
_cb_cooldown: dict[int, float] = {}
CB_COOLDOWN_SEC = 1.2


class GlobalGuardMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data: dict):
        is_msg = isinstance(event, Message)
        is_callback = isinstance(event, CallbackQuery)

        if not is_msg and not is_callback:
            return await handler(event, data)

        user = event.from_user
        uid = user.id if user else None
        if not uid:
            return await handler(event, data)

        if is_msg:
            if not user.is_bot:
                config.total_messages += 1
            if event.chat.type in [ChatType.GROUP, ChatType.SUPERGROUP]:
                if await check_autoleave(event.chat.id):
                    return

        # ADMIN IMMUNITY
        if uid not in config.ADMIN_IDS:

            if is_ghost_banned(uid):
                if is_msg and event.text and event.text.startswith("/profile"):
                    pass
                else:
                    return

            if check_spam(uid):
                if is_msg:
                    try:
                        safe_name = str(user.first_name).replace("<", "&lt;").replace(">", "&gt;")
                        await event.reply(
                            f"⚠️ <b><a href='tg://user?id={uid}'>{safe_name}</a></b>, you have been shadow-banned for spamming.\n"
                            f"🔇 You are muted for 10 minutes.",
                            parse_mode=ParseMode.HTML
                        )
                    except Exception:
                        pass
                elif is_callback:
                    try:
                        await event.answer("⚠️ You have been shadow-banned for 10 minutes due to button spamming!", show_alert=True)
                    except Exception:
                        pass
                return

            if is_shadow_banned(uid):
                if is_msg and event.text and event.text.startswith("/profile"):
                    pass
                else:
                    if is_callback:
                        try:
                            await event.answer("🔇 You are currently shadow-banned. Please wait.", show_alert=True)
                        except Exception:
                            pass
                    return

            if is_callback and not event.data.startswith("vs_"):
                now = time.time()
                last = _cb_cooldown.get(uid, 0.0)
                if now - last < CB_COOLDOWN_SEC:
                    try:
                        await event.answer("⏳ Slow down a little!", show_alert=False)
                    except Exception:
                        pass
                    return
                _cb_cooldown[uid] = now

        # CARD DROP SPAWNER ENGINE (Groups) — bot messages (other bots in
        # the group, service integrations, etc.) don't count toward a
        # spawn; only real users advance the counter.
        if is_msg and not user.is_bot and event.chat.type in [ChatType.GROUP, ChatType.SUPERGROUP]:
            chat_id = str(event.chat.id)
            ensure_group(chat_id, event.chat.title)

            db_ref = config.load_db()
            s_min = db_ref["groups"].get(chat_id, {}).get("spawn_min", 100)
            s_max = db_ref["groups"].get(chat_id, {}).get("spawn_max", 110)

            config.group_counters.setdefault(chat_id, {"count": 0, "target": random.randint(s_min, s_max)})
            config.group_counters[chat_id]["count"] += 1
            if config.group_counters[chat_id]["count"] >= config.group_counters[chat_id]["target"]:
                config.group_counters[chat_id] = {"count": 0, "target": random.randint(s_min, s_max)}
                create_logged_task(trigger_drop(event.chat.id), name=f"trigger_drop:{chat_id}")

        try:
            return await handler(event, data)
        except Exception as e:
            kind = "message" if is_msg else "callback"
            logger.error(f"Unhandled exception in {kind} handler for user {uid}: {e}", exc_info=True)
            return


# ==========================================
# RESILIENT POLLING LOOP
# ==========================================
_shutting_down = False


async def run_polling_resilient():
    backoff = 5
    max_backoff = 60
    while not _shutting_down:
        try:
            await bot.delete_webhook(drop_pending_updates=True)
            logger.info("Establishing connection with Telegram API...")
            await dp.start_polling(bot)
            break
        except (TelegramNetworkError, TelegramRetryAfter,
                ServerDisconnectedError, ClientConnectionError,
                asyncio.TimeoutError, ConnectionError) as e:
            if _shutting_down:
                break
            logger.warning(f"Telegram API unresponsive ({type(e).__name__}: {e}). Reconnecting in {backoff}s...")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, max_backoff)
        except Exception as e:
            if _shutting_down:
                break
            logger.critical(f"Unexpected polling error: {e}", exc_info=True)
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, max_backoff)
        else:
            backoff = 5


# ==========================================
# FASTAPI LIFESPAN & APPLICATION SETUP
# ==========================================
@asynccontextmanager
async def lifespan(app: FastAPI):
    # --- STARTUP LOGIC ---
    logger.info("Initializing system settings...")
    logger.info("Verifying cloud database backup integrity...")
    await load_from_group()
    load_settings()

    # Register Aiogram Middlewares & Routers
    dp.message.outer_middleware(GlobalGuardMiddleware())
    dp.callback_query.outer_middleware(GlobalGuardMiddleware())
    dp.include_router(main_router)

    # Start Background Microtasks
    logger.info("Starting background persistence cycles...")
    create_logged_task(periodic_save(), name="periodic_save")
    create_logged_task(backup_to_group(), name="backup_to_group")

    logger.info("Launching stock market exchange loop...")
    create_logged_task(market_engine_loop(), name="market_engine_loop")

    logger.info("Starting vault-log auto-purge cycle...")
    create_logged_task(vlog_cleanup_loop(), name="vlog_cleanup_loop")

    logger.info("Launching Telegram Bot Resilient Polling...")
    create_logged_task(run_polling_resilient(), name="bot_polling")

    yield

    # --- SHUTDOWN LOGIC ---
    logger.info("Closing active connection sessions...")
    global _shutting_down
    _shutting_down = True
    try:
        await dp.stop_polling()
    except Exception as e:
        logger.warning(f"Error stopping polling: {e}")

    try:
        logger.info("Flushing database to disk before shutdown...")
        await asyncio.to_thread(_flush_db, force=True)
        if vlog._vlogs_dirty:
            await asyncio.to_thread(vlog._flush_vlogs, force=True)
    except Exception as e:
        logger.critical(f"Failed to flush database on shutdown: {e}", exc_info=True)

    await bot.session.close()


# Initialize FastAPI Web Application
app = FastAPI(
    title="Anime Nexus Web API & Mines/Deck Mini App",
    lifespan=lifespan
)

# Enable CORS for Telegram Mini App frontend (Netlify/GitHub Pages)
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Mount REST Routers
app.include_router(mines_router)
app.include_router(deck_api)  # <--- MOUNT DECK API ROUTER
app.include_router(store_api)  # <--- MOUNT STORE API ROUTER
app.include_router(versus_router)  # <--- MOUNT VERSUS WEB APP ROUTER


@app.get("/")
async def root_health_check():
    """Health check endpoint for Railway / Render web hosting."""
    return {
        "status": "online",
        "service": "Anime Nexus Bot & Web API",
        "system": "Operational"
    }


# ==========================================
# MAIN EXECUTION ENTRY POINT
# ==========================================
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    logger.info(f"Starting Web API server listening on 0.0.0.0:{port}...")
    uvicorn.run(app, host="0.0.0.0", port=port)

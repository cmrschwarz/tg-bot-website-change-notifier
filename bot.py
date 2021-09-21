#!/usr/bin/python3
from sqlite3 import dbapi2
from textwrap import dedent
import requests
import json
import base64
import hashlib
import time
import threading
import telegram
import imgkit
import urllib
import sqlite3

from enum import Enum
from telegram import (MessageEntity, ParseMode, InlineKeyboardButton)
from telegram.ext import (Updater, CommandHandler, MessageHandler, Filters,
                          PollAnswerHandler)

class DiffMode(Enum):
    HTML = (0, "html")
    RENDER = (1, "render")

    def to_string(self):
        return self.value[1]

    def to_int(self):
        return self.value[0]

    def from_int(i):
        for dm in DiffMode:
            if dm.to_int() == i:
                return dm

    def from_string(s):
        s = s.lower()
        for dm in DiffMode:
            if dm.to_string() == s:
                return dm

class Database:
    def __init__(self, url):
        self.db = sqlite3.connect(url, check_same_thread=False)
        self.lock = threading.RLock()
        self.count = 0
        self.commit = False
        self.rollback = False
        self.cursor = self.db.cursor()

    def aquire(self):
        self.lock.acquire()
        self.count += 1
        return self.cursor

    def release(self):
        self.count -= 1
        if self.count == 0:
            if self.rollback:
                self.db.rollback()
                self.rollback = False
                self.commit = False
            elif self.commit:
                self.db.commit()
                self.commit = False
        self.lock.release()

    def commit_release(self):
        self.commit = True
        self.release()

    def rollback_release(self):
        self.rollback = True
        self.release()


global DB
global CONFIG

def get_site_hash(url, diff_mode):
    if diff_mode == DiffMode.RENDER:
        content = imgkit.from_url(url, False)
    else:
    	content = requests.get(url)
    digest = hashlib.sha512(content).digest()
    digest = base64.b64encode(digest).decode("ascii")
    return digest

def cutoff(txt, rem_len_needed=0):
    txt_len = len(txt)
    max_txt_len = telegram.MAX_MESSAGE_LENGTH - rem_len_needed
    if max_txt_len >= txt_len: return txt
    if max_txt_len > 5: return txt[0:max_txt_len-4] + " ..."
    if max_txt_len < 0: return ""
    return "....."[0:max_txt_len]

def reply_to_msg(message, explicit_reply, txt):
    message.reply_text(cutoff(txt), reply_to_message_id=message.message_id if explicit_reply else None)

def get_user_id(message):
    global DB
    if message.from_user:
        tg_id = message.from_user.id
        col_name = "tg_user_id"
    else:
        tg_id = message.chat.id
        col_name = "tg_chat_id"

    cur = DB.aquire()
    try:
        select_query = lambda: cur.execute(f"SELECT id FROM users WHERE {col_name} = ?", [tg_id]).fetchmany(2)
        res = select_query()
        if res:
            DB.release()
        else:
            cur.execute(f"INSERT INTO users ({col_name}) VALUES (?)", [tg_id])
            res = select_query()
            DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    assert(len(res) == 1)
    return res[0][0]


def cmd_help(update, context):
    text = dedent("""\
        COMMANDS:
            /help               print this menu
            /list               list all currently tracked sites
            /add <url>          add a new site to track
            /remove <id>        remove a site
            /mode <MODE> <id>   change update detection method for url

        MODES:
            render              the diff is based on an image of the site rendered using imgkit
            html                the diff is based on the raw html of the site (default)

    """)
    update.message.reply_text(
        text,
        entities=[MessageEntity(MessageEntity.CODE, 0, len(text))],
        reply_to_message_id=update.message.message_id
    )


def cmd_list(update, context):
    cur = DB.aquire()
    try:
        uid = get_user_id(update.message)
        sites = cur.execute(
            """
                SELECT id, url, mode
                    FROM sites
                    INNER JOIN notifications ON sites.id = notifications.site_id
                    WHERE notifications.user_id = ?
            """,
            [uid]
        ).fetchmany(CONFIG["max_sites_per_user"])
        DB.release()
    except Exception as ex:
        DB.release()
        raise ex

    if not sites:
        update.message.reply_text("currently not tracking any sites", reply_to_message_id=update.message.id)
        return

    sites_by_mode = {}
    longest_id = 0
    for site in sites:
        id, url, mode = str(site[0]), site[1], DiffMode.from_int(site[2])
        longest_id = max(longest_id, len(id))
        if mode not in sites_by_mode:
            sites_by_mode[mode] = [(id, url)]
        else:
            sites_by_mode[mode].append((id, url))

    reply_to_msg_id = update.message.message_id
    sitelist = ""
    for mode, sites in sites_by_mode.items():
        sitelist += mode.to_string() + " mode:\n"
        for id, url in sites:
            line = f"    {' ' * (longest_id - len(id)) + id}: {cutoff(url, longest_id + 7)}\n"
            line_len = len(line)
            if len(sitelist) + line_len > telegram.MAX_MESSAGE_LENGTH:
                update.message.reply_text(sitelist, entities=[MessageEntity(MessageEntity.CODE, 0, len(sitelist))])
                reply_to_msg_id = None
                sitelist = line
            else:
                sitelist +=  line
    if sitelist != "":
        update.message.reply_text(
            sitelist,
            reply_to_message_id=reply_to_msg_id,
            entities=[MessageEntity(MessageEntity.CODE, 0, len(sitelist))]
        )


def cmd_add(update, context):
    global DB
    global CONFIG
    url = update.message.text
    try:
        assert(url[0:5] == "/add ")
        url = url[5:].strip()
        if len(url) > CONFIG["max_url_len"]:
            reply_to_msg(update.message, True, f'url is too long, refusing to track')
            return
        parsed = urllib.parse.urlparse(url)
    except Exception as e:
        reply_to_msg(update.message, True, f'failed to parse url')
        return

    diff_mode = DiffMode.from_string(CONFIG["default_diff_mode"])

    cur = DB.aquire()
    select_query = lambda: cur.execute(
            "SELECT id FROM sites WHERE url = ? AND mode = ?",
            [url, diff_mode.to_int()]
        ).fetchmany(2)

    try:
        uid = get_user_id(update.message)
        res = select_query()
    except Exception as ex:
        DB.release()
        raise ex

    site_added = False
    if not res:
        DB.release()
        try:
            hash = get_site_hash(url, diff_mode)
        except Exception as ex:
            reply_to_msg(
                update.message, True,
                f'error while loading the page, refusing to track this url',
            )
            return
        cur = DB.aquire()
        try:
            res = select_query()
            if not res:
                cur.execute("INSERT INTO sites (url, mode, hash) VALUES (?, ?, ?)", [url, diff_mode.to_int(), hash])
                site_added = True
                res = select_query()
        except Exception as ex:
            DB.rollback_release()
            raise ex

    try:
        assert(len(res) == 1)
        site_id = res[0][0]
        res = None
        notif_added = False
        if not site_added:
            res = cur.execute("SELECT * FROM notifications where site_id = ? AND user_id = ?", [site_id, uid]).fetchmany(2)

        if not res:
            notif_added = True
            res = cur.execute("INSERT INTO notifications (site_id, user_id) VALUES (?, ?)", [site_id, uid])
    except Exception as ex:
        DB.rollback_release()
        raise ex
    DB.commit_release()
    if notif_added:
        reply_to_msg(update.message, True, f'now tracking this url')
    else:
        reply_to_msg(update.message, True, f'already tracking this url')



def cmd_remove(update, context):
    name = update.message.text
    update.message.reply_text(f'removed url {name}')

def cmd_mode(update, context):
    name = update.message.text
    mode = "html"
    update.message.reply_text(f'set mode to {mode} for url {name}')



def setup_tg_bot():
    global CONFIG
    updater = Updater(CONFIG["bot_token"], use_context=True)

    dp = updater.dispatcher

    dp.add_handler(CommandHandler('help', cmd_help))
    dp.add_handler(CommandHandler('list', cmd_list))
    dp.add_handler(CommandHandler('add', cmd_add))
    dp.add_handler(CommandHandler('remove', cmd_remove))
    dp.add_handler(CommandHandler('mode', cmd_mode))

    updater.start_polling()

def setup_db():
    global DB
    DB = Database("data.sqlite3")
    cur = DB.aquire()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER NOT NULL PRIMARY KEY,
            tg_user_id INTEGER UNIQUE,
            tg_chat_id INTEGER UNIQUE
        );
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS sites (
            id INTEGER NOT NULL PRIMARY KEY,
            url TEXT NOT NULL,
            mode INTEGER NOT NULL,
            hash TEXT NOT NULL
        );
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS notifications (
            site_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            FOREIGN KEY (site_id) REFERENCES sites(id),
            FOREIGN KEY (user_id) REFERENCES users(id),
            PRIMARY KEY (site_id, user_id)
        ) WITHOUT ROWID;
    """)
    DB.commit_release()

if __name__ == '__main__':
    with open("config.json", "r") as f:
	    CONFIG = json.load(f)
    setup_db()
    setup_tg_bot()
    time.sleep(3600)


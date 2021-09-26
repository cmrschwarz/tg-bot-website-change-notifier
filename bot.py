#!/usr/bin/python3
from math import ceil
from re import match
from sqlite3 import dbapi2
from textwrap import dedent, indent
import requests
import json
import base64
import hashlib
import datetime
import threading
import telegram #pip3 install python-telegram-bot
import imgkit
import urllib
import time
import random
import sqlite3
import os
import sys
import contextlib

from enum import Enum
from telegram import (MessageEntity, ParseMode, InlineKeyboardButton)
from telegram.constants import MESSAGEENTITY_URL
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
        self.url = url
        self.db = sqlite3.connect(url, check_same_thread=False)
        self.lock = threading.RLock()
        self.count = 0
        self.commit = False
        self.rollback = False

    def aquire(self):
        self.lock.acquire()
        self.count += 1
        if self.count == 1:
            self.cursor = self.db.cursor()
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
            self.cursor.close()
        self.lock.release()

    def commit_release(self):
        self.commit = True
        self.release()

    def rollback_release(self):
        self.rollback = True
        self.release()


global DB
global CONFIG
global BOT
global SCRIPT_DIR_PATH
global STDIO_SUPPRESSION_FILE
# the maximum number of characters before the url in /list
MAX_URL_PREFIX_LEN = 4 + len(str((2**32))) + 1 + 1 # 4 spaces + id name + colon + space
# this limit ensures that each line in /list is a clickable url
MAX_URL_LEN = telegram.MAX_MESSAGE_LENGTH - MAX_URL_PREFIX_LEN

def get_site_hash(url, diff_mode):
    global STDIO_SUPPRESSION_FILE
    try:
        if diff_mode == DiffMode.RENDER:
            # suppress uselesss 'Rendering...' etc. console output
            # from imgkit
            with contextlib.redirect_stdout(STDIO_SUPPRESSION_FILE):
                content = imgkit.from_url(url, False)
        else:
            assert(diff_mode == DiffMode.HTML)
            content = requests.get(url).content
        digest = hashlib.sha512(content).digest()
        digest = base64.b64encode(digest).decode("ascii")
        return digest
    except Exception as ex:
        err_msg = str(ex)
        sys.stderr.write(
            f"{datetime.datetime.now().isoformat(sep=' ', timespec='seconds')}: failed to load '{url}':\n"
            + indent(
                (
                    "-" * 80 + "\n"
                    + err_msg
                    + ("\n" if ((" " + err_msg)[-1]) != "\n" else "")
                    + "-" * 80 + "\n"
                ),
                prefix=" " * 4
            )
        )
        return None

def cutoff(txt, rem_len_needed=0):
    txt_len = len(txt)
    max_txt_len = telegram.MAX_MESSAGE_LENGTH - rem_len_needed
    if max_txt_len >= txt_len: return txt
    if max_txt_len > 5: return txt[0:max_txt_len-4] + " ..."
    if max_txt_len < 0: return ""
    return "....."[0:max_txt_len]

def reply_to_msg(message, explicit_reply, txt, monospaced=False, extra_entities=None, disable_web_page_preview=None):
    txt_co = txt.rstrip()
    txt_co_len = len(txt_co)
    entities=[]
    if extra_entities:
        for e in extra_entities:
            if e.offset < txt_co_len:
                e.length = min(txt_co_len - e.offset, e.length)
                entities.append(e)
    if monospaced:
        if extra_entities:
            last_end = 0
            entites_with_ms = []
            for e in entities:
                if e.offset != last_end:
                    entites_with_ms.append(MessageEntity(MessageEntity.CODE, last_end, e.offset - last_end))
                last_end = e.offset + e.length
                entites_with_ms.append(e)
            if last_end != txt_co_len:
                entites_with_ms.append(MessageEntity(MessageEntity.CODE, last_end, txt_co_len - last_end))
            entities = entites_with_ms
        else:
            entities = [MessageEntity(MessageEntity.CODE, 0, txt_co_len)]

    reply_to_message_id=message.message_id if explicit_reply else None

    while txt_co_len > telegram.MAX_MESSAGE_LENGTH:
        relevant_entities = []
        for i in range(len(entities)):
            e = entities[i]
            if e.offset > telegram.MAX_MESSAGE_LENGTH:
                entities = entities[i:]
                break
            if e.offset + e.length > telegram.MAX_MESSAGE_LENGTH:
                if e.type == MessageEntity.URL:
                    # splitting a url, make it not clickable to prevent confusion
                    e.type = MessageEntity.CODE
                relevant_length = telegram.MAX_MESSAGE_LENGTH - e.offset
                relevant_entities.append(MessageEntity(e.type, e.offset, relevant_length))
                e.offset = telegram.MAX_MESSAGE_LENGTH
                e.length -= relevant_length
                entities = entities[i:]
                break
            relevant_entities.append(e)
        message.reply_text(txt_co[0:telegram.MAX_MESSAGE_LENGTH], reply_to_message_id=reply_to_message_id, entities=relevant_entities, disable_web_page_preview=disable_web_page_preview)
        for e in entities:
            e.offset -= telegram.MAX_MESSAGE_LENGTH
        txt_co = txt_co[telegram.MAX_MESSAGE_LENGTH:]
        txt_co_len -= telegram.MAX_MESSAGE_LENGTH

    message.reply_text(txt_co, reply_to_message_id=reply_to_message_id, entities=entities, disable_web_page_preview=disable_web_page_preview)

def random_seed():
    return random.randint(0, 2**31)

def get_user_id(message):
    global DB
    chat_id = message.chat.id
    is_group = (message.from_user is None)

    cur = DB.aquire()
    try:
        select_query = lambda: cur.execute(
            "SELECT id FROM users WHERE tg_chat_id = ?",
            [chat_id]
        ).fetchone()
        res = select_query()
        if res:
            DB.release()
        else:
            cur.execute(
                "INSERT INTO users (tg_chat_id, is_group) VALUES (?,?)",
                [chat_id, is_group]
            )
            res = select_query()
            DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    return res[0]


def cmd_help(update, context):
    text = dedent("""\
        COMMANDS:
            /help               print this menu
            /list               list all currently tracked sites and their ids
            /add <url>          add a new site to track
            /remove <id>        remove a site
            /mode <id> <mode>   change update detection method for url

        MODES:
            render              the diff is based on an image of the site rendered using imgkit (default)
            html                the diff is based on the raw html of the site

    """)
    reply_to_msg(update.message, True, text, monospaced=True)


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
        reply_to_msg(update.message, True, "currently not tracking any sites")
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

    single_reply = True
    sitelist = ""
    first_mode = True
    mode_ends = []
    entity_ends = []
    entities = []
    line_prefix_len = 4 + longest_id + 1 + 1 # 4 spaces + longest_id + colon + space
    for mode, sites in sites_by_mode.items():
        if not single_reply:
            reply_to_msg(update.message, False, sitelist, monospaced=True, extra_entities=entities)
            mode_ends = []
            entity_ends = []
            entities = []
            sitelist = ""
        else:
            if first_mode:
                first_mode = False
            else:
                sitelist += "\n"
                mode_ends.append(len(sitelist))
                entity_ends.append(len(entities))
        sitelist += mode.to_string() + " mode:\n"
        for id, url in sites:
            line = f"    {' ' * (longest_id - len(id)) + id}: {url}\n"
            entities.append(MessageEntity(MessageEntity.URL, len(sitelist) + line_prefix_len, len(line) - line_prefix_len))
            line_len = len(line)
            while len(sitelist) + line_len > telegram.MAX_MESSAGE_LENGTH:
                single_reply = False
                last_me = 0
                last_ee = 0
                for i in range(0,len(mode_ends)):
                    me = mode_ends[i]
                    ee = entity_ends[i]
                    relevant_entities = []
                    for e in entities[last_ee:ee]:
                        e.offset -= last_me
                        relevant_entities.append(e)
                    reply_to_msg(update.message, False, sitelist[last_me:me], monospaced=True, extra_entities=relevant_entities, disable_web_page_preview=True)
                    last_me = me
                    last_ee = ee
                if mode_ends:
                    sitelist = sitelist[last_me:]
                    entities = entities[last_ee:]
                    mode_ends = []
                    entity_ends = []
                    for e in entities:
                        e.offset -= last_me
                    continue
                else:
                    reply_to_msg(update.message, False, sitelist, monospaced=True, disable_web_page_preview=True, extra_entities=entities[:-1])
                    entities = entities[-1:]
                    entities[0].offset -= len(sitelist)
                    sitelist = line
                    break


            else:
                sitelist += line
    if sitelist != "":
        reply_to_msg(update.message, single_reply, sitelist, monospaced=True, extra_entities = entities, disable_web_page_preview=True)


def cmd_add(update, context):
    global DB
    global CONFIG
    global MAX_URL_LEN
    url = update.message.text
    try:
        cmd = "/add"
        assert(url[0:4] == cmd)
        url = url[len(cmd):].strip()
        if len(url) > MAX_URL_LEN:
            reply_to_msg(update.message, True, f'url is too long (limit is set to {MAX_URL_LEN}), refusing to track')
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
        hash = get_site_hash(url, diff_mode)
        if not hash:
            reply_to_msg(
                update.message, True,
                f'error while loading the page, refusing to track this url',
            )
            return
        cur = DB.aquire()
        try:
            res = select_query()
            if not res:
                cur.execute("INSERT INTO sites (url, mode, hash, seed) VALUES (?, ?, ?, ?)", [url, diff_mode.to_int(), hash, random_seed()])
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
    global DB
    cmd = "/remove"
    rm_id_str = update.message.text
    assert(rm_id_str[0:len(cmd)] == cmd)
    rm_id_str = rm_id_str[len(cmd):].strip()
    try:
        rm_id = int(rm_id_str)
    except Exception as ex:
        reply_to_msg(update.message, True, f"invalid <id> '{rm_id_str}'")
        return

    try:
        cur = DB.aquire()
        uid = get_user_id(update.message)
        res = cur.execute("DELETE FROM notifications WHERE site_id = ? AND user_id = ?", [rm_id, uid]).rowcount
        if res == 0:
            DB.release()
            reply_to_msg(update.message, True, f'no site with that id present')
            return
        res = cur.execute("SELECT COUNT(*) FROM notifications WHERE site_id = ?", [rm_id]).fetchall()
        if res[0][0] == 0:
            cur.execute("DELETE FROM sites WHERE id = ?", [rm_id])
    except Exception as ex:
        DB.rollback_release()
        raise ex
    DB.commit_release()
    reply_to_msg(update.message, True, f'site removed')

def update_notification_site(message, cursor, user_id, site_id_old, site_id_new, mode_new):
    res = cursor.execute(
        "SELECT site_id FROM notifications WHERE site_id = ? AND user_id = ?",
        [site_id_new, user_id]
    ).fetchone()
    if res:
        reply_to_msg(
            message, True,
            f'already tracking this url in {mode_new.to_string()} mode with id {res[0]}',
        )
        return False
    cursor.execute(
        "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
        [site_id_new, site_id_old]
    ).rowcount
    return True

def cmd_mode(update, context):
    global DB
    cmd = "/mode"
    args = update.message.text
    assert(args[0:len(cmd)] == cmd)
    args = args[len(cmd):].strip()
    id_str = args.split()[0]
    try:
        site_id = int(id_str)
    except Exception as ex:
        reply_to_msg(update.message, True, f"invalid <id> '{id_str}'")
        return

    mode_str = args[len(id_str):].strip()
    diff_mode = DiffMode.from_string(mode_str)
    if not diff_mode:
        reply_to_msg(
            update.message, True,
            f"unknown <mode> '{mode_str}'"
        )
        return

    cur = DB.aquire()
    try:
        uid = get_user_id(update.message)
        res = cur.execute(
            "SELECT url, mode FROM notifications INNER JOIN sites ON id = site_id WHERE site_id = ? AND user_id = ?",
            [site_id, uid]
        ).fetchone()
    except Exception as ex:
        DB.release()
        raise ex

    if not res:
        DB.release()
        reply_to_msg(update.message, True, f'no site with that id present')
        return

    url, mode = res
    if mode == diff_mode.to_int():
        reply_to_msg(update.message, True, f'site is already in this mode')
        return

    search_for_tgt_site = lambda: (
        cur.execute(
            "SELECT id FROM sites WHERE url = ? AND mode = ?",
            [url, diff_mode.to_int()]
        ).fetchone()
    )

    try:
        res = search_for_tgt_site()
        if res:
            if not update_notification_site(update.message, cur, uid, site_id, res[0], diff_mode): return
    except Exception as ex:
        DB.rollback_release()
        raise ex

    if not res:
        DB.release()
        hash = get_site_hash(url, diff_mode)
        if not hash:
            reply_to_msg(
                update.message, True,
                f'error while loading the page, refusing to change mode',
            )
            return
        cur = DB.aquire()
        try:
            res = search_for_tgt_site()
            if res:
                if not update_notification_site(update.message, cur, uid, site_id, res[0], diff_mode): return
            else:
                res = cur.execute("SELECT COUNT(*) FROM notifications WHERE site_id = ?", [site_id]).fetchone()
                if res[0] == 1:
                    res = cur.execute(
                        "UPDATE sites SET mode = ? , hash = ? WHERE id = ?",
                        [diff_mode.to_int(), hash, site_id]
                    ).rowcount
                    assert(res == 1)
                else:
                    cur.execute(
                        "INSERT INTO sites(url, mode, hash, seed) VALUES (?,?,?,?)",
                        [url, diff_mode.to_int(), hash, random_seed()]
                    )
                    res = search_for_tgt_site()
                    assert(res)
                    cur.execute(
                        "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
                        [res[0], site_id, uid]
                    ).rowcount
        except Exception as ex:
            DB.rollback_release()
            raise ex
    DB.commit_release()


    reply_to_msg(update.message, True, f'successfully changed mode')

def setup_tg_bot():
    global CONFIG
    global BOT
    BOT = Updater(CONFIG["bot_token"], use_context=True)

    dp = BOT.dispatcher

    dp.add_handler(CommandHandler('help', cmd_help))
    dp.add_handler(CommandHandler('list', cmd_list))
    dp.add_handler(CommandHandler('add', cmd_add))
    dp.add_handler(CommandHandler('remove', cmd_remove))
    dp.add_handler(CommandHandler('mode', cmd_mode))

    BOT.start_polling()

def setup_db():
    global DB
    global SCRIPT_DIR_PATH
    DB = Database(SCRIPT_DIR_PATH + "/data.sqlite3")
    cur = DB.aquire()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER NOT NULL PRIMARY KEY,
            tg_chat_id INTEGER NOT NULL UNIQUE,
            is_group BOOLEAN
        );
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS sites (
            id INTEGER NOT NULL PRIMARY KEY,
            url TEXT NOT NULL,
            mode INTEGER NOT NULL,
            hash TEXT,
            seed INTEGER NOT NULL
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

def inform_site_changed(db_cur, site_id, mode, new_hash):
    global BOT
    db_cur.execute("""
        SELECT tg_chat_id, url
            FROM notifications
            INNER JOIN sites ON notifications.site_id = sites.id
            INNER JOIN users ON notifications.user_id = users.id
            WHERE sites.id = ?
        """,
        [site_id]
    )
    while True:
        res = db_cur.fetchone()
        if not res: break
        tg_chat_id, url = res
        if new_hash:
            msg = cutoff("site changed:\n" + url)
        else:
            msg = cutoff("site became unavailable:\n" + url)
        BOT.bot.send_message(tg_chat_id, msg)

def poll_sites():
    global CONFIG
    update_interval_secs = float(CONFIG["update_interval_seconds"])
    global DB
    # we use a separate connection for this so we don't stall the bot interaction while
    # our updates are running
    db = sqlite3.connect(DB.url)
    last_poll = datetime.datetime.now()
    curr_seed = 0
    while True:
        now = datetime.datetime.now()
        diff = now - last_poll
        last_poll = now
        secs_since_last = diff.total_seconds()
        cur = db.cursor()
        query = cur.execute(
            f"""
                SELECT id, url, mode, hash, seed, ((seed - ?) % ? + ?) % ? AS delay
                    FROM sites
                    WHERE delay < ?
                    ORDER BY delay ASC
            """,
            [curr_seed, update_interval_secs, update_interval_secs,  update_interval_secs, secs_since_last]
        )
        while True:
            res = query.fetchone()
            if not res: break
            site_id, url, mode, hash, seed, delay = res
            mode = DiffMode.from_int(mode)
            new_hash = get_site_hash(url, mode)
            if hash == new_hash: continue
            notif_cur = db.cursor()
            notif_cur.execute("UPDATE sites SET hash = ? WHERE id = ?", [new_hash, site_id])
            db.commit()
            inform_site_changed(notif_cur, site_id, mode, new_hash)
            notif_cur.close()

        curr_seed = (curr_seed + secs_since_last) % update_interval_secs
        delay_to_next = cur.execute(
            f"""
                SELECT mod(mod(seed - ?, ?) + ?, ?) AS delay
                    FROM sites
                    ORDER BY delay ASC
                    LIMIT 1
            """,
            [curr_seed, update_interval_secs, update_interval_secs,  update_interval_secs]
        ).fetchone()
        if not delay_to_next:
            time.sleep(update_interval_secs * (random.random() * 0.9 + 0.1))
        else:
            delay = max(delay_to_next[0], 1)
            time.sleep(delay)
        cur.close()




if __name__ == '__main__':
    SCRIPT_DIR_PATH = os.path.dirname(os.path.realpath(__file__))
    with open(SCRIPT_DIR_PATH + "/config.json", "r") as f:
        CONFIG = json.load(f)
    if "max_url_len" in CONFIG:
        mul = int(CONFIG["max_url_len"])
        if mul > 0:
            MAX_URL_LEN = mul
    STDIO_SUPPRESSION_FILE = open(os.devnull, "w")
    setup_db()
    setup_tg_bot()
    poll_sites()


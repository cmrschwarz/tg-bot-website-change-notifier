#!/usr/bin/python3
from codecs import replace_errors
from math import ceil
from re import match
from sqlite3 import dbapi2
from textwrap import dedent, indent
import requests
import json
import base64
from enum import Enum
import hashlib
import datetime
import threading
import imgkit
import time
import random
import sqlite3
import math
import os
import sys
from url_normalize import url_normalize
import contextlib
from concurrent.futures import ThreadPoolExecutor

import telegram #pip3 install python-telegram-bot
from telegram import (MessageEntity, InlineKeyboardButton)
from telegram.constants import MESSAGEENTITY_URL
from telegram.ext import (Updater, CommandHandler, CallbackQueryHandler)
from telegram.inline.inlinekeyboardmarkup import InlineKeyboardMarkup

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

class UserState(Enum):
    UNAUTHORIZED = (0, "unauthorized")
    AUTHORIZED = (1, "authorized")
    ADMIN = (2, "admin")
    BLOCKED = (3, "blocked")

    def to_string(self):
        return self.value[1]

    def to_int(self):
        return self.value[0]

    def from_int(i):
        for dm in UserState:
            if dm.to_int() == i:
                return dm

    def from_string(s):
        s = s.lower()
        for dm in UserState:
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

def cutoff(txt, rem_len_needed=0, max_len=telegram.MAX_MESSAGE_LENGTH):
    txt_len = len(txt)
    max_txt_len = max_len - rem_len_needed
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
        reply_to_message_id=None
        for e in entities:
            e.offset -= telegram.MAX_MESSAGE_LENGTH
        txt_co = txt_co[telegram.MAX_MESSAGE_LENGTH:]
        txt_co_len -= telegram.MAX_MESSAGE_LENGTH

    message.reply_text(txt_co, reply_to_message_id=reply_to_message_id, entities=entities, disable_web_page_preview=disable_web_page_preview)

def random_seed():
    global INT_MAX
    return random.randint(0, INT_MAX)

def pretty_name(name, is_group):
    return f"group '{name}'" if is_group else f"@{name}"

def get_user_id(message, need_admin=False):
    #todo update changed usernames
    global DB
    global BOT
    chat_id = message.chat.id
    is_group = (message.from_user is None or message.from_user.id != chat_id)
    if is_group:
        name = message.chat.title
    else:
        name = message.from_user.username

    cur = DB.aquire()
    try:
        select_query = lambda: cur.execute(
            "SELECT id, name, state FROM users WHERE tg_chat_id = ?",
            [chat_id]
        ).fetchone()
        res = select_query()
        id = None
        if res:
            DB.release()
            id, db_name, state = res
            #todo: update name
            assert(db_name == name)
            state = UserState.from_int(state)
            if state == UserState.BLOCKED: return None
            if need_admin and state != UserState.ADMIN: return None
            if state != UserState.UNAUTHORIZED: return id

        if not id:
            if is_admin_message(message):
                assert(not is_group)
                cur.execute(
                    "INSERT INTO users (tg_chat_id, name, is_group, state) VALUES (?,?,?,?)",
                    [chat_id, name, is_group, UserState.ADMIN.to_int()]
                )
                res = select_query()
                DB.commit_release()
                return res[0]
            else:
                if need_admin:
                    DB.release()
                    return None
                cur.execute(
                    "INSERT INTO users (tg_chat_id, name, is_group, state) VALUES (?,?,?,?)",
                    [chat_id, name, is_group, UserState.UNAUTHORIZED.to_int()]
                )
                id, name, state = select_query()
                DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    reply_to_msg(message, True, "unauthorized")

    cur = DB.aquire()
    try:
        res = cur.execute("SELECT tg_chat_id FROM users WHERE state = ?", [UserState.ADMIN.to_int()])
        while True:
            next = res.fetchone()
            if not next: break

            BOT.bot.send_message(
                next[0],
                f"Do you want to authorize {pretty_name(name, is_group)} (chat id {chat_id}) ?",
                reply_markup=InlineKeyboardMarkup(
                    [
                        [
                            InlineKeyboardButton("Authorize", callback_data="/authorize " + str(id)),
                            InlineKeyboardButton("Deny", callback_data="/deny " + str(id)),
                            InlineKeyboardButton("Block", callback_data="/block " + str(id)),
                        ]
                    ]
                )
            )
    except Exception as ex:
        DB.rollback_release()
        raise ex


def cmd_start(update, context):
    reply_to_msg(update.message, True, "Hello! Please use /help for a list of commands.")

def pad(str, length, pad_char=" "):
    assert(length > len(str) and len(pad_char) == 1)
    return str + pad_char * (length - len(str))

def insert_at_heading(str, heading, insert, after=True):
    insert_pos = str.find(heading)
    if after:
        insert_pos += len(heading)
    return str[:insert_pos] + insert + str[insert_pos:]

def is_admin_message(message):
    global ADMIN_USER_NAMES
    if not message.from_user or message.from_user.id != message.chat.id: return False
    return message.from_user.username in ADMIN_USER_NAMES

def cmd_help(update, context):
    uid = get_user_id(update.message)
    if not uid: return

    global ADMIN_USER_NAMES
    global DEFAULT_DIFF_MODE
    global DEFAULT_UPDATE_FREQUENCY
    global MAX_SITES_PER_USER
    global MAX_URL_LEN
    global UPDATE_FREQUENCIES
    default_mode = lambda mode: "(default)" if (mode == DEFAULT_DIFF_MODE) else ""

    text = f"""\
        COMMANDS:
            /help                        print this menu
            /list                        list all currently tracked sites and their ids
            /add <url>                   add a new site to track
            /remove <id>                 remove a site
            /mode <id> <mode>            change the update detection method for a site
            /frequency <id> <frequency>  change the update frequency for a site

        MODES:
            render                       the diff is based on an image of the site rendered using imgkit {default_mode(DiffMode.RENDER)}
            html                         the diff is based on the raw html of the site {default_mode(DiffMode.HTML)}

        FREQUENCIES:

        INSTANCE SETTINGS
            max sites per user           {MAX_SITES_PER_USER}
            max url length               {MAX_URL_LEN}

    """
    text = dedent(text)

    first_column_width = (
        text.find("print this menu") - text.find("/help")
        + len("/help")
        + str(reversed(text[:text.find("/help")])).find("\n")
    )

    frequency_listing = ""
    for (name, freq) in UPDATE_FREQUENCIES.items():
        frequency_listing += (
            pad(" " * 4 + f"{name} ", first_column_width)
            + f"{freq} s"
            + (" (default)" if freq == DEFAULT_UPDATE_FREQUENCY else "")
            + "\n"
        )

    text = insert_at_heading(text, "FREQUENCIES:\n", frequency_listing)
    if is_admin_message(update.message):
        text = insert_at_heading(
            text, "MODES",
            dedent(
                """\
                ADMIN COMMANDS:
                    /listusers                       list all users
                    /userstate <user id> <state>     change the state for a user
                    /listall                         list all tracked sites
                    /siteinfo <id>                   list all users using a site and the respective modes

                """
            ),
            after=False
        )

    reply_to_msg(update.message, True, text, monospaced=True)

def cmd_whoami(update, context):
    uid = get_user_id(update.message)
    if not uid: return

    response = ""
    if update.message.from_user:
        response += f"user id: {update.message.from_user.id}\n"
    response += f"chat id: {update.message.chat.id}\n"
    reply_to_msg(update.message, True, response, monospaced=True)

def cmd_listusers(update, context):
    uid = get_user_id(update.message, need_admin=True)
    if not uid: return

    reply_to_msg(update.message, True, "not implemented yet :/")

def cmd_listall(update, context):
    uid = get_user_id(update.message, need_admin=True)
    if not uid: return

    reply_to_msg(update.message, True, "not implemented yet :/")

def cmd_userstate(update, context):
    uid = get_user_id(update.message, need_admin=True)
    if not uid: return

    reply_to_msg(update.message, True, "not implemented yet :/")

def cmd_siteinfo(update, context):
    uid = get_user_id(update.message, need_admin=True)
    if not uid: return

    reply_to_msg(update.message, True, "not implemented yet :/")


def cmd_list(update, context):
    uid = get_user_id(update.message)
    if not uid: return

    cur = DB.aquire()
    try:
        sites = cur.execute(
            """
                SELECT id, url, mode, frequency
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

    sites_by_type = {}
    longest_id = 0
    for site in sites:
        id, url, mode, freq = str(site[0]), site[1], DiffMode.from_int(site[2]), UPDATE_FREQUENCY_NAMES[site[3]]
        longest_id = max(longest_id, len(id))
        type = (mode, freq)
        if type not in sites_by_type:
            sites_by_type[type] = [(id, url)]
        else:
            sites_by_type[type].append((id, url))

    single_reply = True
    sitelist = ""
    first_mode = True
    mode_ends = []
    entity_ends = []
    entities = []
    line_prefix_len = 4 + longest_id + 1 + 1 # 4 spaces + longest_id + colon + space
    for (mode, freq), sites in sites_by_type.items():
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
        sitelist += mode.to_string() + " mode [" + freq + "]:\n"
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
    global DEFAULT_DIFF_MODE
    global MAX_SITES_PER_USER
    global DEFAULT_UPDATE_FREQUENCY
    global UPDATE_FREQUENCY_NAMES
    uid = get_user_id(update.message)
    if not uid: return

    url = update.message.text
    try:
        cmd = "/add"
        assert(url[0:4] == cmd)
        url = url[len(cmd):].strip()
        url = url_normalize(url)
        if len(url) > MAX_URL_LEN:
            reply_to_msg(update.message, True, f'url is too long (limit is set to {MAX_URL_LEN}), refusing to track')
            return
    except Exception as e:
        reply_to_msg(update.message, True, f'failed to parse url')
        return

    cur = DB.aquire()
    try:
        res = cur.execute("SELECT COUNT(*) FROM notifications WHERE user_id = ?", [uid]).fetchone()
        if res[0] >= MAX_SITES_PER_USER:
            reply_to_msg(
                update.message, True,
                f'the sites per user limit ({MAX_SITES_PER_USER}) would be exceeded. refusing to add this url.',
            )
            return
        site_id = get_site_id(cur, url, DEFAULT_DIFF_MODE, DEFAULT_UPDATE_FREQUENCY)
    except Exception as ex:
        DB.release()
        raise ex

    site_added = False
    if not site_id:
        DB.release()
        hash = get_site_hash(url, DEFAULT_DIFF_MODE)
        if not hash:
            reply_to_msg(
                update.message, True,
                f"error while loading the page, refusing to track {url}",
            )
            return
        cur = DB.aquire()
        try:
            site_id = get_site_id(cur, url, DEFAULT_DIFF_MODE, DEFAULT_UPDATE_FREQUENCY)
            if not site_id:
                cur.execute(
                    "INSERT INTO sites (url, mode, frequency, hash, seed) VALUES (?, ?, ?, ?, ?)",
                    [url, DEFAULT_DIFF_MODE.to_int(), DEFAULT_UPDATE_FREQUENCY, hash, random_seed()]
                )
                site_id = get_site_id(cur, url, DEFAULT_DIFF_MODE, DEFAULT_UPDATE_FREQUENCY)
                assert(site_id)
                site_added = True
        except Exception as ex:
            DB.rollback_release()
            raise ex

    try:
        notif_added = True
        if not site_added:
            res = cur.execute(
                """
                    SELECT mode, frequency
                        FROM notifications
                        INNER JOIN sites
                        ON site_id = id
                        WHERE site_id = ? AND user_id = ?
                """,
                [site_id, uid]
            ).fetchone()
            if res:
                notif_added = False
                prev_mode, prev_freq = res

        if notif_added:
            cur.execute("INSERT INTO notifications (site_id, user_id) VALUES (?, ?)", [site_id, uid])
            DB.commit_release()
        else:
            DB.release()

    except Exception as ex:
        DB.rollback_release()
        raise ex

    if notif_added:
        reply_to_msg(update.message, True, f'now tracking this url')
    else:
        reply_to_msg(
            update.message, True,
            f"already tracking this url in {DiffMode.from_int(prev_mode).to_string()} mode " +
                f"[{UPDATE_FREQUENCY_NAMES[prev_freq]}]"
        )



def cmd_remove(update, context):
    global DB
    uid = get_user_id(update.message)
    if not uid: return

    cmd = "/remove"
    rm_id_str = update.message.text
    assert(rm_id_str[0:len(cmd)] == cmd)
    rm_id_str = rm_id_str[len(cmd):].strip()
    try:
        rm_id = int(rm_id_str)
    except Exception as ex:
        reply_to_msg(update.message, True, f"invalid <id> '{cutoff(rm_id_str, max_len=100)}'")
        return

    try:
        cur = DB.aquire()
        uid = get_user_id(update.message)
        res = cur.execute("DELETE FROM notifications WHERE site_id = ? AND user_id = ?", [rm_id, uid]).rowcount
        if res == 0:
            DB.release()
            reply_to_msg(update.message, True, f'no site with that id present')
            return
        assert(res == 1)
        res = cur.execute("SELECT COUNT(*) FROM notifications WHERE site_id = ?", [rm_id]).fetchone()
        if res[0] == 0:
            cur.execute("DELETE FROM sites WHERE id = ?", [rm_id])
        DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex
    reply_to_msg(update.message, True, f'site removed')

def get_site_id(cur, url, mode, freq):
    res = cur.execute(
        "SELECT id FROM sites WHERE url = ? AND mode = ? AND frequency = ?",
        [url, mode.to_int(), freq]
    ).fetchone()
    return res[0] if res else None

def try_change_mode_for_notification(message, user_id, site_id_curr, url, freq, mode_new):
    global DB
    cur = DB.aquire()
    try:
        # check if site with changed config already exists
        site_id_new = get_site_id(cur, url, mode_new, freq)
        if not site_id_new: return False

        # complain if we already use that site
        res = cur.execute(
            "SELECT site_id FROM notifications WHERE site_id = ? AND user_id = ?",
            [site_id_new, user_id]
        ).fetchone()
        if res:
            reply_to_msg(
                message, True,
                f'already tracking this url in {mode_new.to_string()} mode with id {res[0]}',
            )
            return True

        # swap over to use that site
        cur.execute(
            "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
            [site_id_new, site_id_curr]
        ).rowcount
        # remove old site if no longer used
        any_old_site_user = cur.execute(
            "SELECT site_id FROM notifications WHERE site_id = ? LIMIT 1",
            [site_id_curr]
        ).fetchone()
        if not any_old_site_user:
            cur.execute("DELETE FROM sites WHERE id = ?", [site_id_curr])
        DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    return True

def cmd_mode(update, context):
    uid = get_user_id(update.message)
    if not uid: return

    global DB
    cmd = "/mode"
    args = update.message.text
    assert(args[0:len(cmd)] == cmd)
    args = args[len(cmd):].strip()
    id_str = args.split()[0]
    try:
        site_id = int(id_str)
    except Exception as ex:
        reply_to_msg(update.message, True, f"invalid <id> '{cutoff(id_str, max_len=100)}'")
        return

    mode_str = args[len(id_str):].strip()
    diff_mode = DiffMode.from_string(mode_str)
    if not diff_mode:
        reply_to_msg(
            update.message, True,
            f"unknown <mode> '{cutoff(mode_str, max_len=100)}'"
        )
        return

    cur = DB.aquire()
    try:
        res = cur.execute(
            "SELECT url, mode, frequency FROM notifications INNER JOIN sites ON id = site_id WHERE site_id = ? AND user_id = ?",
            [site_id, uid]
        ).fetchone()
    except Exception as ex:
        DB.release()
        raise ex

    if not res:
        DB.release()
        reply_to_msg(update.message, True, f'no site with that id present')
        return

    url, mode, freq = res
    if mode == diff_mode.to_int():
        reply_to_msg(update.message, True, f'site is already in this mode')
        return

    if try_change_mode_for_notification(update.message, uid, site_id, url, freq, diff_mode): return

    DB.release()
    hash = get_site_hash(url, diff_mode)
    if not hash:
        reply_to_msg(
            update.message, True,
            f'error while loading the page, refusing to change mode',
        )
        return

    if try_change_mode_for_notification(update.message, uid, site_id, url, freq, diff_mode): return
    cur = DB.aquire()
    try:
        old_site_user_count = cur.execute("SELECT COUNT(*) FROM notifications WHERE site_id = ?", [site_id]).fetchone()[0]
        if old_site_user_count == 1:
            # if nobody else uses the old site, change it over to the new mode
            cur.execute(
                "UPDATE sites SET mode = ?, hash = ? WHERE id = ?",
                [diff_mode.to_int(), hash, site_id]
            )
        else:
            # if the old site is used by somebody else we have to create a new one
            cur.execute(
                "INSERT INTO sites(url, mode, frequency, hash, seed) VALUES (?,?,?,?,?)",
                [url, diff_mode.to_int(), freq, hash, random_seed()]
            )
            site_id_new = get_site_id(cur, url, diff_mode, freq)
            assert(site_id_new)
            cur.execute(
                "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
                [site_id_new, site_id, uid]
            )
        DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    reply_to_msg(update.message, True, f'successfully changed mode')

def cmd_frequency(update, context):
    uid = get_user_id(update.message)
    if not uid: return

    global DB
    global UPDATE_FREQUENCIES
    cmd = "/frequency"
    args = update.message.text
    assert(args[0:len(cmd)] == cmd)
    args = args[len(cmd):].strip()
    id_str = args.split()[0]
    try:
        site_id = int(id_str)
    except Exception as ex:
        reply_to_msg(update.message, True, f"invalid <id> '{cutoff(id_str, max_len=100)}'")
        return

    freq_str = args[len(id_str):].strip()
    if freq_str not in UPDATE_FREQUENCIES:
        reply_to_msg(
            update.message, True,
            f"unknown <frequency> '{cutoff(freq_str, max_len=100)}'"
        )
        return

    freq_new = UPDATE_FREQUENCIES[freq_str]

    cur = DB.aquire()
    try:
        uid = get_user_id(update.message)
        site_to_change = cur.execute(
            "SELECT url, mode, frequency, hash FROM notifications INNER JOIN sites ON id = site_id WHERE site_id = ? AND user_id = ?",
            [site_id, uid]
        ).fetchone()
    except Exception as ex:
        DB.release()
        raise ex

    if not site_to_change:
        DB.release()
        reply_to_msg(update.message, True, f'no site with that id present')
        return

    url, mode, freq, hash = site_to_change
    mode = DiffMode.from_int(mode)
    if freq_new == freq:
        reply_to_msg(update.message, True, f'site is already updating with this frequency')
        return

    try:
        site_id_new = get_site_id(cur, url, mode, freq_new)
        if site_id_new:
            notif_to_new_site = cur.execute(
                "SELECT site_id FROM notifications WHERE site_id = ? AND user_id = ?",
                [site_id_new, uid]
            ).fetchone()
    except Exception as ex:
        DB.release()
        raise ex

    if site_id_new and notif_to_new_site:
        cur = DB.release()
        reply_to_msg(
            update.message, True,
            f'already tracking this url with frequency {UPDATE_FREQUENCY_NAMES[freq_new]} with id {site_id_new}',
        )
        return

    if site_id_new:
        try:
            cur.execute(
                "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
                [site_id_new, site_id, uid]
            )
            any_old_site_user = cur.execute("SELECT site_id FROM notifications WHERE site_id = ? LIMIT 1", [site_id]).fetchone()
            if not any_old_site_user:
                cur.execute("DELETE FROM sites WHERE id = ?", [site_id])
            DB.commit_release()
        except Exception as ex:
            DB.release()
            raise ex
    else:
        try:
            old_site_user_count = cur.execute("SELECT COUNT(*) FROM notifications WHERE site_id = ?", [site_id]).fetchone()[0]
            if old_site_user_count == 1:
                # if nobody else uses the old site, change it over to the new frequency
                cur.execute(
                    "UPDATE sites SET frequency = ? WHERE id = ?",
                    [freq_new, site_id]
                )
            else:
                # if the old site is used by somebody else we have to create a new one
                cur.execute(
                    "INSERT INTO sites(url, mode, frequency, hash, seed) VALUES (?,?,?,?,?)",
                    [url, mode.to_int(), freq_new, hash, random_seed()]
                )
                site_id_new = get_site_id(cur, url, mode, freq_new)
                assert(site_id_new)
                cur.execute(
                    "UPDATE notifications SET site_id = ? WHERE site_id = ? AND user_id = ?",
                    [site_id_new, site_id, uid]
                )
            DB.commit_release()
        except Exception as ex:
            DB.rollback_release()
            raise ex
    reply_to_msg(update.message, True, f'successfully changed update frequency')

def authorization_callback(update, cb_cmd, target_state, action_name):
    global ADMIN_USER_NAMES
    global DB
    if update.callback_query.from_user.username not in ADMIN_USER_NAMES: return
    arg = str(update.callback_query.data)[len(cb_cmd):].strip()
    id = int(arg)
    try:
        cur = DB.aquire()
        res = cur.execute("SELECT name, is_group, state FROM users  WHERE id = ?", [id]).fetchone()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    if res:
        name, is_group, state = res
        state = UserState.from_int(state)
    if not res:
        DB.release()
        update.callback_query.answer(f"outdated procedure!")
    elif state != UserState.UNAUTHORIZED:
        DB.release()
        update.callback_query.answer(f"outdated procedure! {pretty_name(name, is_group)} is currently {state.to_string()}")
    else:
        try:
            cur.execute("UPDATE users SET state = ? WHERE id = ?", [target_state.to_int(), id])
            DB.commit_release()
        except Exception as ex:
            DB.rollback_release()
            raise ex
        reply_to_msg(update.callback_query.message, False, f"{action_name} {pretty_name(name, is_group)}")
    update.callback_query.edit_message_reply_markup()


def cb_authorize(update, context):
    authorization_callback(update, "/authorize", UserState.AUTHORIZED, "authorized")

def cb_block(update, context):
    authorization_callback(update, "/block", UserState.BLOCKED, "blocked")

def cb_deny(update, context):
    authorization_callback(update, "/block", UserState.UNAUTHORIZED, "denied")

def inform_site_changed(site_id, mode, new_hash):
    global DB
    global BOT

    cur = DB.aquire()
    try:
        cur.execute("""
            SELECT tg_chat_id, url
                FROM notifications
                INNER JOIN sites ON notifications.site_id = sites.id
                INNER JOIN users ON notifications.user_id = users.id
                WHERE sites.id = ?
            """,
            [site_id]
        )
        while True:
            res = cur.fetchone()
            if not res: break
            tg_chat_id, url = res
            if new_hash:
                msg = cutoff("site changed:\n" + url)
            else:
                msg = cutoff("site became unavailable:\n" + url)
            BOT.bot.send_message(tg_chat_id, msg)
    finally:
        DB.release()

def poll_site(site_id, url, mode, freq, old_hash):
    global DB
    cur = DB.aquire()
    try:
        new_hash = cur.execute(
            """
                SELECT hash
                    FROM sites
                    WHERE url = ? AND mode = ? AND frequency > ?
                    ORDER BY frequency DESC
                    LIMIT 1
            """,
            [url, mode.to_int(), freq]
        ).fetchone()
    finally:
        DB.release()

    if new_hash:
        new_hash = new_hash[0]
    else:
        new_hash = get_site_hash(url, mode)
    if old_hash == new_hash: return

    try:
        cur = DB.aquire()
        cur.execute("UPDATE sites SET hash = ? WHERE id = ?", [new_hash, site_id])
        DB.commit_release()
    except Exception as ex:
        DB.rollback_release()
        raise ex

    inform_site_changed(site_id, mode, new_hash)

def poll_sites():
    global CONFIG
    global DB
    global NUM_WORKER_THREADS
    global UPDATE_INTERVAL_SECONDS
    global TIMESTEP
    smallest_frequency = min(UPDATE_FREQUENCIES.values())
    thread_pool = ThreadPoolExecutor(NUM_WORKER_THREADS)
    last_poll = datetime.datetime.now()
    curr_seed = 0
    while True:
        now = datetime.datetime.now()
        diff = now - last_poll
        last_poll = now
        secs_since_last = diff.total_seconds()
        cur = DB.aquire()
        query = cur.execute(
            f"""
                SELECT id, url, mode, frequency, hash, ((seed - ?) % frequency + frequency) % frequency AS delay
                    FROM sites
                    WHERE delay < ?
                    ORDER BY delay ASC
            """,
            [curr_seed, secs_since_last]
        )
        while True:
            res = query.fetchone()
            if not res: break
            site_id, url, mode, freq, hash, _delay = res
            mode = DiffMode.from_int(mode)
            thread_pool.submit(poll_site, site_id, url, mode, freq, hash)
        curr_seed = (curr_seed + secs_since_last) % TIMESTEP
        # more compact would be mod(mod(seed - curr_seed, update_interval_secs) + update_interval_secs, update_interval_secs)
        # but not all instances of sqlite3 support the mod function
        delay_to_next = cur.execute(
            f"""
                SELECT (CAST(seed - ? AS INTEGER) % frequency + frequency) % frequency + ABS((seed - ?) - CAST(seed - ? AS INTEGER)) AS delay
                    FROM sites
                    ORDER BY delay ASC
                    LIMIT 1
            """,
            [curr_seed, curr_seed, curr_seed]
        ).fetchone()
        DB.release()
        if not delay_to_next:
            time.sleep(smallest_frequency * (random.random() * 0.9 + 0.1))
        else:
            delay = max(delay_to_next[0], 1)
            time.sleep(delay)

def setup_tg_bot():
    global CONFIG
    global BOT
    BOT = Updater(CONFIG["bot_token"], use_context=True, workers=NUM_WORKER_THREADS)

    dp = BOT.dispatcher
    dp.add_handler(CommandHandler('start', cmd_start))
    dp.add_handler(CommandHandler('help', cmd_help))
    dp.add_handler(CommandHandler('list', cmd_list))
    dp.add_handler(CommandHandler('add', cmd_add))
    dp.add_handler(CommandHandler('remove', cmd_remove))
    dp.add_handler(CommandHandler('mode', cmd_mode))
    dp.add_handler(CommandHandler('frequency', cmd_frequency))
    dp.add_handler(CommandHandler('whoami', cmd_whoami))
    dp.add_handler(CommandHandler('listusers', cmd_listusers))
    dp.add_handler(CommandHandler('listall', cmd_listall))
    dp.add_handler(CommandHandler('userstate', cmd_userstate))
    dp.add_handler(CommandHandler('siteinfo', cmd_siteinfo))
    dp.add_handler(CallbackQueryHandler(cb_authorize, pattern="^/authorize"))
    dp.add_handler(CallbackQueryHandler(cb_deny, pattern="^/deny"))
    dp.add_handler(CallbackQueryHandler(cb_block, pattern="^/block"))
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
            name TEXT,
            is_group BOOLEAN NOT NULL,
            state INTEGER NOT NULL
        );
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS sites (
            id INTEGER NOT NULL PRIMARY KEY,
            url TEXT NOT NULL,
            mode INTEGER NOT NULL,
            frequency INTEGER NOT NULL,
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

    # make sure the db doesn't contain frequencies that are not specified by the config
    cur = DB.aquire()
    frequency_check = cur.execute(
        f"SELECT COUNT(*) from sites WHERE frequency NOT IN ({','.join(['?'] * len(UPDATE_FREQUENCIES))})",
        list(UPDATE_FREQUENCIES.values())
    ).fetchone()
    DB.release()
    assert(frequency_check[0] == 0)

# lowest common multiple. not present in math before python 3.9
def lcm(*integers):
    lcm = 1
    for i in integers:
        lcm = (lcm * i) // math.gcd(lcm, i)
    return lcm

def setup_config():
    global INT_MAX
    INT_MAX = 2**31 - 1

    global SCRIPT_DIR_PATH
    SCRIPT_DIR_PATH = os.path.dirname(os.path.realpath(__file__))

    # the maximum number of characters before the url in /list
    global MAX_URL_PREFIX_LEN
    MAX_URL_PREFIX_LEN = 4 + len(str((INT_MAX))) + 1 + 1 # 4 spaces + id name + colon + space

    global STDIO_SUPPRESSION_FILE
    STDIO_SUPPRESSION_FILE = open(os.devnull, "w")

    global CONFIG
    with open(SCRIPT_DIR_PATH + "/config.json", "r") as f:
        CONFIG = json.load(f)

    global MAX_URL_LEN
    # this limit ensures that each line in /list is a clickable url
    MAX_URL_LEN = telegram.MAX_MESSAGE_LENGTH - MAX_URL_PREFIX_LEN
    if "max_url_len" in CONFIG:
        mul = int(CONFIG["max_url_len"])
        if mul > 0:
            MAX_URL_LEN = mul

    global DEFAULT_DIFF_MODE
    DEFAULT_DIFF_MODE = DiffMode.HTML
    if "default_diff_mode" in CONFIG:
        DEFAULT_DIFF_MODE = DiffMode.from_string(CONFIG["default_diff_mode"])

    global MAX_SITES_PER_USER
    MAX_SITES_PER_USER = 100
    if "max_sites_per_user" in CONFIG:
        MAX_SITES_PER_USER = int(CONFIG["max_sites_per_user"])

    global NUM_WORKER_THREADS
    NUM_WORKER_THREADS = 16
    if "num_worker_threads" in CONFIG:
        nwt = int(CONFIG["num_worker_threads"])
        if nwt > 0:
            NUM_WORKER_THREADS = nwt

    global UPDATE_FREQUENCIES
    UPDATE_FREQUENCIES = {}
    for name, val in CONFIG["update_frequencies_seconds"].items():
        UPDATE_FREQUENCIES[name] = int(val)

    global UPDATE_FREQUENCY_NAMES
    UPDATE_FREQUENCY_NAMES = {freq: name for name, freq in UPDATE_FREQUENCIES.items()}

    global DEFAULT_UPDATE_FREQUENCY
    DEFAULT_UPDATE_FREQUENCY = UPDATE_FREQUENCIES[CONFIG["default_update_frequency"]]

    global ADMIN_USER_NAMES
    ADMIN_USER_NAMES = []
    for user in CONFIG["admin_user_names"]:
        assert(isinstance(user, str))
        ADMIN_USER_NAMES.append(str(user))

    global TIMESTEP
    TIMESTEP = lcm(*UPDATE_FREQUENCIES.values())
    assert(TIMESTEP < INT_MAX)

if __name__ == '__main__':
    setup_config()
    setup_db()
    setup_tg_bot()
    poll_sites()


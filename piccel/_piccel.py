# -*- coding: utf-8 -*-

# TODO: DataSheet with no form, fed by external data
# TODO: add lock system for admin/marshall operations

# TODO: reload view qitemlist after plugin update

import io
import base64
import os
from collections import OrderedDict
import json
from pprint import pformat, pprint
# UUID1: MAC addr + current timestamp with nanosec precision
# UUID4: 122 bytes random number
from uuid import uuid1, uuid4
import re
from time import sleep, perf_counter
from datetime import date, datetime, timedelta, time
import os.path as op
from collections import defaultdict
import shutil
from pathlib import PurePath
import importlib
from importlib import import_module, reload as reload_module
import inspect
import csv

from . import sheet_plugin_template
from . import workbook_plugin_template
from .plugin_tools import map_set, And, Or #, Less, LessEqual, Greater, GreaterEqual
from .plugin_tools import (LescaDashboard, InterviewTracker,
                           form_update_or_new, DEFAULT_INTERVIEW_PLAN_SHEET_LABEL,
                           track_emailled_poll, emailled_poll_action,
                           track_participant_status, participant_status_action)
from .form import (Form, FormSection, FormItem, FormEditor, FormEditorSheetIO,
                   NotEditableError, DateTimeCollector, LanguageError)

import unittest
import tempfile
from functools import partial

import numpy as np

import pandas as pd
from pandas.testing import assert_frame_equal

from cryptography.fernet import Fernet
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
import bcrypt
from hashlib import scrypt

import logging
import sys

from io import BytesIO

from PyQt5 import QtCore, QtGui, QtWidgets
from . import ui

from .core import LazyFunc, df_index_from_value

from appdirs import user_data_dir


from .logging import logger, debug2, debug3

# For DataSheet export to pdf:
HTML_TOP = '''
<html>
<head>
<style>
  h2 {
    text-align: center;
    font-family: Helvetica, Arial, sans-serif;
  }
  table {
    margin-left: auto;
    margin-right: auto;
  }
  table, th, td {
    border: 1px solid black;
    border-collapse: collapse;
  }
  th, td {
    padding: 5px;
    text-align: center;
    font-family: Helvetica, Arial, sans-serif;
    font-size: 90%;
  }
  table tbody tr:hover {
    background-color: #dddddd;
  }
  tr:nth-child(even) {
    background-color: Silver;
  }
  .wide {
    width: 90%;
  }
</style>
</head>
<body>
'''

HTML_BOTTOM = '''
</body>
</html>
'''

def protect_fn(fn):
    return ''.join(c if c.isalnum() else "_" for c in fn)


def derive_key_pbkdf2(password_str, salt_bytes):
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt_bytes,
        iterations=100000,
        backend=default_backend()
    )
    key = base64.urlsafe_b64encode(kdf.derive(password_str.encode()))
    return key

def derive_key(password_str, salt_bytes):
    key = scrypt(password_str.encode(), salt=salt_bytes,
                 n=16384, r=8, p=1, dklen=32)
    return base64.urlsafe_b64encode(key)

class Encrypter:

    # TODO: init from key instead of pwd/salt and
    # create other constructor for pwd/salt
    def __init__(self, password, salt_bytes, key=None):
        if key is None:
            self.key = derive_key(password, salt_bytes)
        else:
            self.key = key
        self.fernet = Fernet(self.key)

    def get_key(self):
        return self.key.decode()

    @staticmethod
    def from_key(key_str):
        return Encrypter(None, None, key_str.encode())

    def encrypt_str(self, content_str):
        return self.fernet.encrypt(content_str.encode()).decode()

    def decrypt_to_str(self, crypted_str):
        return self.fernet.decrypt(crypted_str.encode()).decode()

class UnknownUser(Exception): pass
class InvalidPassword(Exception): pass

class PasswordVault:

    #TODO
    JSON_SCHEMA = {}
    SALT_HEX_KEY = 'salt_hex'

    def __init__(self, vault_dict=None, pwd_fn=None):
        # TODO: fix that content of pwd_fn may differ from given vault_dict...
        # In fact vault should not keep track of the file
        if vault_dict is None:
            logger.debug('Init of password vault with no entries')
        else:
            logger.debug('Init of password vault with entries: %s',
                         ', '.join(vault_dict.keys()))

        self.vault = vault_dict
        if self.vault is None:
            self.vault = {PasswordVault.SALT_HEX_KEY : os.urandom(32).hex(),
                          'passwords' : {}}
        self.pwd_fn = op.normpath(pwd_fn)

    def __eq__(self, other):
        return set(self.vault.keys())  == set(other.vault.keys()) and \
            self.pwd_fn == other.pwd_fn

    @staticmethod
    def from_file(pwd_fn):
        if not op.exists(pwd_fn):
            logger.warning('Password file %s does not exist. Create one '\
                           'and add generated salt.' %pwd_fn)
            with open(pwd_fn, 'w') as fout:
                json.dump({PasswordVault.SALT_HEX_KEY : os.urandom(32).hex(),
                           'passwords' : {}}, fout)

        vault = {}
        with open(pwd_fn, 'r') as fin:
            vault.update(json.load(fin))
        #TODO check json with schema
        return PasswordVault(vault, pwd_fn)

    def set_password(self, user, new_password_str, old_passord_str=''):
        assert(user != PasswordVault.SALT_HEX_KEY)
        try:
            if not self.password_is_valid(user, old_passord_str):
                raise InvalidPassword('Invalid old password for %s' % user)
        except UnknownUser:
            pass
        salt = bcrypt.gensalt()
        pwd_bytes = new_password_str.encode('utf-8')
        self.vault['passwords'][user] = \
            bcrypt.hashpw(pwd_bytes, salt).decode('utf-8')

    def __getitem__(self, key):
        return self.vault[key]

    def has_password_key(self, key):
        return key in self.vault['passwords']

    def has_key(self, key):
        return key in self.vault

    def save(self):
        # TODO: pwd_fn has to be specified!
        logger.debug('Save password vault')
        if self.pwd_fn is not None:
            with open(self.pwd_fn, 'w') as fout:
                json.dump(self.vault, fout)
        else:
            raise IOError('No file to save to')

    def check(self, user, password_str):
        try:
            if not self.password_is_valid(user, password_str):
                raise InvalidPassword('Invalid password for %s in %s' % \
                                      (user, self.pwd_fn))
        except KeyError:
            raise UnknownUser(user)

    def password_is_valid(self, user, password_str):
        try:
            return bcrypt.checkpw(password_str.encode('utf-8'),
                                  self.vault['passwords'][user].encode('utf-8'))
        except KeyError:
            raise UnknownUser(user)

    def get_encrypter(self, user, password_str, key=None):
        if key is None:
            self.check(user, password_str)
            salt = bytes.fromhex(self.vault[PasswordVault.SALT_HEX_KEY])
            encrypter = Encrypter(password_str, salt)
        else:
            encrypter = Encrypter.from_key(key)
        return encrypter


from .core import UserRole, nexts


class IndexedPattern:
    def __init__(self, pattern, index_start=0):
        self.pattern = pattern
        self.index = index_start
    def __call__(self):
        result = self.pattern % self.index
        self.index += 1
        return result

def import_gform_file(gform_fn, form_fn, language, merge=True):
    form = Form.from_gform_json_file(gform_fn, language,
                                     use_item_title_as_key=True)
    if op.exists(form_fn) and merge:
        with open(form_fn, 'r') as fin:
            form_origin = Form.from_json(fin.read())
            form_origin.add_translations(form)
            form = form_origin

    with open(form_fn, 'w') as fout:
        fout.write(form.to_json())


from .core import Notifier

class FolderExistsError(Exception): pass
class FileExistsError(Exception): pass

# Progress note COVEPIC compréhension FIC préliminaire

def module_from_code_str(code):
     spec = importlib.util.spec_from_loader('helper', loader=None)
     module = importlib.util.module_from_spec(spec)
     exec(code, module.__dict__)
     return module

class LocalFileSystem:
    """
    Keep track of all modifications made to be able to notice external
    modifications.
    """
    def __init__(self, root_folder, encrypter=None, track_changes=False):
        self.root_folder = op.normpath(root_folder)
        self.encrypter = encrypter
        self.enable_track_changes(track_changes)

    def enable_track_changes(self, state=True):
        self.track_changes = state
        self.current_stats = self.file_stats()

    def file_stats(self):
        stats = {}
        if self.track_changes:
            for wroot, dirs, files in os.walk(self.root_folder):
                for bfn in files:
                    rdir = op.relpath(wroot, self.root_folder)
                    fn = op.normpath(op.join(rdir, bfn))
                    stats[fn] = self.file_size(fn)
        return stats

    def external_changes(self):
        modifications = []
        additions = []
        if self.track_changes:
            for wroot, dirs, files in os.walk(self.root_folder):
                for bfn in files:
                    rdir = op.relpath(wroot, self.root_folder)
                    fn = op.normpath(op.join(rdir, bfn))
                    if fn not in self.current_stats:
                        additions.append(fn)
                    elif self.current_stats[fn] != self.file_size(fn):
                        modifications.append(fn)
        deletions = [f for f in self.current_stats if not self.exists(f)]
        return modifications, additions, deletions

    def accept_changes(self, modifications=None, additions=None, deletions=None):
        if self.track_changes:
            modifications = modifications if modifications is not None else []
            additions = additions if additions is not None else []
            deletions = deletions if deletions is not None else []
            for fn in modifications+additions:
                self.current_stats[fn] = self.file_size(fn)
            for fn in deletions:
                self.current_stats.pop(fn)

    def accept_all_changes(self):
        self.current_stats = self.file_stats()

    def change_dir(self, folder, track_changes=False):
        """ Note: change tracking will be reset """
        assert(self.exists(folder))
        return LocalFileSystem(op.join(self.root_folder, folder),
                               self.encrypter, track_changes)

    def clone(self):
        return LocalFileSystem(self.root_folder, self.encrypter,
                               self.track_changes)

    def set_encrypter(self, encrypter):
        self.encrypter = encrypter

    def unset_encrypter(self):
        self.encrypter = None

    def exists(self, fn):
        return op.exists(op.join(self.root_folder, fn))

    def is_file(self, fn):
        return op.isfile(op.join(self.root_folder, fn))

    def file_size(self, fn):
        return op.getsize(op.join(self.root_folder, fn))

    def makedirs(self, folder):
        full_folder = op.join(self.root_folder, folder)
        if op.exists(full_folder):
            logger.debug2('Folder %s already exists', full_folder)
            return
        logger.debug2('Create folder %s', full_folder)
        os.makedirs(full_folder)
        assert(op.exists(full_folder))

    def test_write_access(self):
        success = True
        try:
            self.save('test_write', '')
        except Exception as e:
            logger.error('Cannot write to %s, exception: %s',
                         self.root_folder, e)
            success = False
        else:
            self.remove('test_write')
        return success

    def full_path(self, fn):
        return op.join(self.root_folder, fn)

    def listdir(self, folder, list_folders_only=False):
        afolder = op.join(self.root_folder, folder)
        predicate = (lambda e : op.isdir(op.join(afolder, e)) \
                     if list_folders_only else lambda e : True)
        return [e for e in os.listdir(afolder) if predicate(e)]

    def dir_is_empty(self, folder):
        try:
            next(iter(os.scandir(op.join(self.root_folder, folder))))
        except StopIteration:
            return True
        return False

    def rmtree(self, folder):
        full_folder = op.join(self.root_folder, folder)
        if not op.exists(full_folder):
            logger.debug2('rmtree: Folder %s does not exist', full_folder)
            return

        for wroot, dirs, files in os.walk(op.join(self.root_folder, folder)):
            for bfn in files:
                rdir = op.relpath(wroot, self.root_folder)
                fn = op.normpath(op.join(rdir, bfn))
                self.current_stats.pop(fn)

        logger.debug2('Remove folder %s', full_folder)
        shutil.rmtree(full_folder)

    def copy_to_tmp(self, fn, decrypt=False, tmp_dir=None):
        """ Return destination temporary file """
        if tmp_dir is None:
            tmp_dir = tempfile.mkdtemp()
        tmp_fn = op.join(tmp_dir, op.basename(fn))
        if not decrypt:
            shutil.copy(op.join(self.root_folder, fn), tmp_fn)
        else:
            assert(self.encrypter is not None)
            logger.warning('Copying UNCRYPTED %s to %s', fn, tmp_fn)
            content_str = self.load(fn)
            with open(tmp_fn, 'w') as fout:
                fout.write(content_str)
        return tmp_fn

    def import_file(self, src_fn, dest_rfn, overwrite=False):
        with open(src_fn, 'r') as fin:
            content = fin.read()
        self.save(dest_rfn, content, overwrite=overwrite)

    def remove(self, fn):
        logger.debug2('Remove file %s', fn)
        os.remove(op.join(self.root_folder, fn))
        self.current_stats.pop(fn)

    def save(self, fn, content_str='', overwrite=False, crypt=True):
        fn = op.normpath(fn)
        afn = op.join(self.root_folder, fn)
        logger.debug2('Filesystem - save to abs fn: %s', afn)
        logger.debug2('Filesystem - working directory: %s', os.getcwd())
        if self.encrypter is not None and crypt:
            content_str = self.encrypter.encrypt_str(content_str)

        if op.exists(afn) and not overwrite:
            raise FileExistsError(afn)

        with open(afn, 'w') as fout:
            fout.write(content_str)

        self.current_stats[fn] = self.file_size(fn)

    def load(self, fn):
        afn = op.join(self.root_folder, fn)

        with open(afn, 'r') as fin:
            content_str = fin.read()

        if self.encrypter is not None:
            content_str = self.encrypter.decrypt_to_str(content_str)
        return content_str

class InvalidSheetPlugin(Exception): pass
class InvalidSheetLabel(Exception): pass
class NoFormMasterError(Exception): pass
class NoPluginFileError(Exception): pass
class UndefinedUser(Exception): pass

class Unformatter:
    def __init__(self, form, key, na_value=pd.NA):
        self.form = form
        self.key = key
        self.na_value = na_value
    def __call__(self, v):
        return self.form.unformat(self.key, v) if v!='' else self.na_value 

class Hint:

    def __init__(self, icon_style=None, message=None, is_link=False,
                 background_color_hex_str=None,
                 foreground_color_hex_str=None):
        self.message = message
        self.is_link = is_link

        self.background_qcolor = None if background_color_hex_str is None \
            else QtGui.QColor(background_color_hex_str)
        self.foreground_qcolor = None if foreground_color_hex_str is None \
            else QtGui.QColor(foreground_color_hex_str)

        self.qicon_style = icon_style
        self.qicon = None

    def preload(self, qobj):
        if self.qicon_style is not None:
            self.qicon = qobj.style().standardIcon(self.qicon_style)

class Hints:
    WARNING = Hint(icon_style=QtWidgets.QStyle.SP_MessageBoxWarning,
                   background_color_hex_str='#FCAF3E')
    DONE = Hint(icon_style=QtWidgets.QStyle.SP_DialogApplyButton)
    NOT_DONE = Hint(icon_style=QtWidgets.QStyle.SP_DialogCancelButton,
                    background_color_hex_str='#FCE94F')
    QUESTION = Hint(icon_style=QtWidgets.QStyle.SP_MessageBoxQuestion,
                    background_color_hex_str='#247BA0')
    ERROR = Hint(icon_style=QtWidgets.QStyle.SP_MessageBoxCritical,
                 background_color_hex_str='#EF2929')
    TEST = Hint(foreground_color_hex_str='#8F9EB7')
    ALL_HINTS = [WARNING, DONE, NOT_DONE, ERROR, QUESTION]

    @staticmethod
    def preload(qobj):
        for hint in Hints.ALL_HINTS:
            hint.preload(qobj)

from .sheet_plugin import SheetPlugin

"""
class FolderContentWatcher:

    def __init__(self, filesystem):
        self.filesystem = filesystem
        self.reset()

    def reset(self):
        self.stats = self.file_stats()

    def file_stats(self):
        return {fn : self.filesystem.file_size(fn) \
                for fn in self.filesystem.listdir('.')\
                if self.filesystem.is_file(fn)}

    def modified_files(self):
        new_stats = self.file_stats()
        common_files = set(self.stats).intersection(new_stats)
        return [fn for fn in common_files if self.stats[fn] != new_stats[fn]]

    def deleted_files(self):
        return set(self.stats).difference(self.file_stats())

    def new_files(self):
        return set(self.file_stats()).difference(self.stats)

    def ignore_file_changes(self, fns):
        for fn in fns:
            self.stats[fn] = self.filesystem.file_size(fn)

    def ignore_file_deletions(self, fns):
        for fn in fns:
            self.stats.pop(fn)

"""

class TestLocalFileSystem(unittest.TestCase):

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp()

    def touch_file(self, fn, content=''):
        with open(op.join(self.tmp_dir, fn), 'w') as fin:
            fin.write(content)

    def test_track_new_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)

        self.touch_file('new.cc')
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(adds, ['new.cc'])
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(dels), 0)

        filesystem.accept_changes(additions=['new.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_track_modified_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        self.touch_file('yy.cc', 'hey')

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(mods, ['yy.cc'])
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

        filesystem.accept_changes(modifications=['yy.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_track_deleted_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        os.remove(op.join(self.tmp_dir, 'yy.cc'))

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(dels, ['yy.cc'])

        filesystem.accept_changes(deletions=['yy.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_internal_tracking(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        filesystem.remove('xx.cc')

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

        filesystem.save('gg.cc', 'yep')
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

        filesystem.save('yy.cc', 'yep', overwrite=True)
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

class NonUniqueIndexFromValues(Exception) : pass

from .core import (FormEditionBlockedByPendingLiveForm, FormEditionLocked,
                   FormEditionNotOpen, FormEditionLockedType,
                   FormEditionOrphanError, FormEditionNotAvailable)

class DataSheet:
    """
    Table data where entries where input is done with an associated form.
    Provide different views of the data table.
    Notify on data change.
    """
    CSV_SEPARATOR = '\t'
    DATA_FILE_EXT = '.csv'

    SHEET_LABEL_RE = re.compile('[A-Za-z._-]+')

    def __init__(self, label, form_master=None, df=None, user=None,
                 filesystem=None, live_forms=None, watchers=None,
                 workbook=None, properties=None):
        """
        filesystem.root is the sheet-specific folder where to save all data
        and pending forms
        """
        self.label = self.validate_sheet_label(label)
        self.properties = {}
        self.access_level = UserRole.VIEWER
        self.update_properties(properties if properties is not None else {})

        if df is not None and form_master is None:
            raise Exception('Form master cannot be None if df is given')

        self.form_master = form_master
        self.live_forms = live_forms if live_forms is not None else {}
        self.user = user

        self.filesystem = filesystem
        if self.filesystem is not None and self.user is None:
            raise Exception('User required when file saving is used')
        if self.filesystem is not None:
            if not self.filesystem.exists('master_form_alternates'):
                self.filesystem.makedirs('master_form_alternates')
            self.filesystem.enable_track_changes()
            fs_label = DataSheet.get_sheet_label_from_filesystem(self.filesystem)
            if fs_label != self.label:
                raise InvalidSheetLabel('Sheet label (%s) is not the same as '\
                                        'containing folder (%s)' % \
                                        (self.label, fs_label))
        self.has_write_access = (self.filesystem.test_write_access() \
                                 if self.filesystem is not None else False)

        # TODO: use Dummy file system to avoid checking all the time?

        self.default_view = 'raw'
        self.views = {}

        self.cached_views = defaultdict(lambda: None)
        self.cached_validity = defaultdict(lambda: None)

        self.cached_inconsistent_entries = None

        self.notifier = Notifier(watchers if watchers is not None else {})

        self.df = self.empty_df_from_master()

        if df is not None:
            self.import_df(df)

        self.entry_fns = {}

        if self.filesystem is not None and not self.filesystem.exists('data'):
            self.filesystem.makedirs('data')

        if self.filesystem is not None:
            self.reload_all_data()
            self.load_live_forms()

        self.workbook = workbook
        self.set_plugin(SheetPlugin(self))

    def empty_df_from_master(self):
        df = None
        if self.form_master is not None:
            dtypes = self.form_master.get_dtypes()
            cols = ['__entry_id__', '__update_idx__', '__conflict_idx__',
                    '__fn__'] + [k for k in dtypes]
            df = pd.DataFrame(columns=cols)
            df['__entry_id__'] = df['__entry_id__'].astype(np.int64)
            df['__update_idx__'] = df['__update_idx__'].astype(np.int64)
            df['__conflict_idx__'] = df['__conflict_idx__'].astype(np.int64)
            df['__fn__'] = df['__fn__'].astype('string')

            for col,dt in dtypes.items():
                df[col] = df[col].astype(dt)

            df.set_index(['__entry_id__', '__update_idx__',
                          '__conflict_idx__'],  inplace=True)
        return df

    def set_filesystem(self, fs):
        # TODO: check if really needed? Should be set only once at __init__
        self.filesystem = fs
        self.filesystem.enable_track_changes()
        self.has_write_access = self.filesystem.test_write_access()

    def set_workbook(self, workbook):
        self.plugin.set_workbook(workbook)

    @staticmethod
    def from_files(user, filesystem, watchers=None, workbook=None):
        label = DataSheet.get_sheet_label_from_filesystem(filesystem)
        logger.debug('Load form master for sheet %s', label)
        form_master = DataSheet.load_form_master(filesystem)
        logger.debug('Create sheet %s, using filesystem(root=%s)',
                     label, filesystem.full_path(filesystem.root_folder))
        sheet_properties = DataSheet.load_properties_from_file(filesystem)
        sheet = DataSheet(label, form_master=form_master, df=None, user=user,
                          filesystem=filesystem, watchers=watchers,
                          workbook=workbook, properties=sheet_properties)
        sheet.load_plugin()
        return sheet

    def base_views(self):
        return {'raw' : lambda ddf: ddf,
                'latest' : self.latest_update_df}

    def latest_update_df(self, df=None):
        if df is None:
            df = self.df
        # fm = lambda x : x.loc[[x.index.max()]]
        # latest = df.groupby(level=0, group_keys=False).apply(fm)
        latest = df.groupby(level=0, group_keys=False).tail(1).sort_index()
        if latest.empty:
            latest = self.empty_df_from_master()
        return latest

    #@check_role(UserRole.ADMIN)
    def dump_plugin_code(self, plugin_code=None, overwrite=False):
        if self.filesystem is None:
            raise IOError('Cannot save plugin for sheet %s (no associated '\
                          'filesystem)')
        if plugin_code is None:
            logger.info('No plugin code given to dump, using template.')
            plugin_code = inspect.getsource(sheet_plugin_template)
        plugin_module = 'plugin_%s' % self.label
        plugin_fn = '%s.py' % plugin_module
        self.filesystem.save(plugin_fn, plugin_code, overwrite=overwrite)
        return plugin_fn

    def get_plugin_code(self):
        plugin_module = 'plugin_%s' % self.label
        plugin_fn = '%s.py' % plugin_module
        if self.filesystem.exists(plugin_fn):
            return self.filesystem.load(plugin_fn)
        else:
            return ''

    def load_plugin(self):
        plugin_module = 'plugin_%s' % self.label
        plugin_fn = '%s.py' % plugin_module
        if self.filesystem.exists(plugin_fn):
            logger.info('Load plugin of sheet %s from %s',
                        self.label, self.filesystem.full_path(plugin_fn))
            tmp_folder = op.dirname(self.filesystem.copy_to_tmp(plugin_fn,
                                                                 decrypt=True))
            sys.path.insert(0, tmp_folder)
            plugin_module = import_module(plugin_module)
            reload_module(plugin_module)
            sys.path.pop(0)
            self.set_plugin(plugin_module.CustomSheetPlugin(self))
        else:
            logger.info('No plugin to load for sheet %s', self.label)

    @staticmethod
    def load_properties_from_file(filesystem):
        property_fn = 'properties.json'
        properties = {'access_level' : UserRole.VIEWER}
        if filesystem.exists(property_fn):
            prop = json.loads(filesystem.load(property_fn))
            prop['access_level'] = UserRole[prop.get('access_level', 'VIEWER')]
            properties.update(prop)
        else:
            logger.debug('No property file to load from %s',
                         filesystem.root_folder)
        return properties

    def update_properties(self, properties):
        if 'access_level' in properties:
            self.access_level = properties.pop('access_level')
        self.properties.update(properties)

    def get_property(self, label):
        assert(label != 'access_level')
        return self.properties[label]

    def save_properties(self, overwrite=False):
        if self.filesystem is None:
            raise Exception('No filesystem available to save properties '\
                            'for sheet %s', self.label)
        logger.info('Save properties of sheet %s' % self.label)
        self.filesystem.save('properties.json',
                             json.dumps({**{'access_level' :
                                            self.access_level.name},
                                         **self.properties}),
                             overwrite=overwrite)

    @staticmethod
    def load_form_master(filesystem, form_fn='master.form'):
        form = None
        if filesystem.exists(form_fn):
            content = filesystem.load(form_fn)
            form = Form.from_json(content)
        else:
            logger.debug('No form master to load (%s does not exist in %s)',
                         form_fn, filesystem.root_folder)
        return form

    def reload_all_data(self):
        logger.debug('Reload all data for sheet %s', self.label)
        data_folder = 'data'
        if self.filesystem.exists(data_folder):
            data_bfns = [fn for fn in self.filesystem.listdir(data_folder) \
                         if fn.endswith(DataSheet.DATA_FILE_EXT)]
            if logger.level >= logging.DEBUG:
                logger.debug('Available data files for sheet %s:\n%s',
                             self.label, '\n'.join(data_bfns))
            if len(data_bfns) > 0:
                if self.df.shape[0] > 0:
                    self.df.drop(self.df.index, inplace=True)
                    self.notifier.notify('cleared_data')
                # Associated view will be cleared
                # Expect watchers to react
                for data_bfn in data_bfns:
                    data_fn = op.join(data_folder, data_bfn)
                    logger.debug('Load sheet data item from %s', data_fn)
                    df_content = self.filesystem.load(data_fn)
                    # _append_df will notify 'append_entry'
                    entry_df = self.df_from_str(df_content)
                    if not data_fn.endswith('main.csv'):
                        entry_df['__fn__'] = data_fn
                    self._append_df(entry_df)
                    self.fix_conflicting_entries()
                    self.invalidate_cached_views()
            else:
                logger.debug('No sheet data to load in %s', data_folder)
            self.filesystem.accept_all_changes()
        else:
            self.filesystem.makedirs(data_folder)
            logger.debug('Data folder %s is empty', data_folder)

    def refresh_data(self):
        """
        Refresh data based on external file changes.
        """
        logger.debug2('Refresh data for sheet %s', self.label)
        if self.filesystem is not None:
            modified_files, new_files, deleted_files = \
                self.filesystem.external_changes()
            logger.debug('Files externally added: %s', new_files)
            logger.debug('Files externally modified: %s', modified_files)
            logger.debug('Files externally deleted: %s', deleted_files)

            # TODO: IMPORTANT new form data is ignored here
            new_data_files = [fn for fn in new_files if fn.startswith('data')]
            modified_data_files = [fn for fn in modified_files \
                                   if fn.startswith('data')]
            deleted_data_files = [fn for fn in deleted_files \
                                  if fn.startswith('data')]

            if len(modified_data_files) > 0 or len(deleted_data_files) > 0:
                self.reload_all_data()
            else:
                for data_fn in new_data_files:
                    logger.debug('Sheet %s, load new data file: %s',
                                 self.label, data_fn)
                    df_content = self.filesystem.load(data_fn)
                    entry_df = self.df_from_str(df_content)
                    if not data_fn.endswith('main.csv'):
                        entry_df['__fn__'] = data_fn
                    self._append_df(entry_df)

            # TODO: IMPORTANT changed form data is ignored here
            self.filesystem.accept_all_changes()

    def get_form_for_edition(self):
        # Insure that there is no pending live forms
        users_with_live_forms = self.users_with_pending_live_forms()
        if len(users_with_live_forms) > 0:
            locking_users = ', '.join(users_with_live_forms)
            logger.error('Form master of sheet %s is locked for edition by %s',
                         self.label, locking_users)
            raise FormEditionBlockedByPendingLiveForm(locking_users)

        # Insure that there is no edition lock
        if self.filesystem.exists('master.form.lock'):
            lock_user = self.filesystem.load('master.form.lock')
            raise FormEditionLocked(lock_user)

        self.lock_form_master_edition()
        try:
            return self.form_master.new()
        except LanguageError:
            from IPython import embed; embed()

    def get_alternate_master_forms(self):
        return self.filesystem.listdir('master_form_alternates')

    def open_alternate_master_form(self, form_bfn):
        return Form(self.filesystem.load(op.join('master_form_alternates', form_bfn)))

    def save_alternate_master_form(self, form_bfn, form):
        logger.info('Save alternate version of form %s as %s (sheet: %s)',
                    form.label, form_bfn, self.label)
        self.filesystem.save(op.join('master_form_alternates', form_bfn),
                             form.to_json(), overwrite=True)

    def get_alternate_form_fn(self):
        date_fmt = '%Y_%m_%d_%Hh%Mm%Ss'
        return '%s_%s' % (datetime.now().strftime(date_fmt), protect_fn(self.user))

    def lock_form_master_edition(self):
        self.filesystem.save('master.form.lock', self.user)

    def unlock_form_master_edition(self):
        if self.filesystem.exists('master.form.lock'):
            self.filesystem.remove('master.form.lock')

    def close_form_edition(self):
        self.unlock_form_master_edition()

    def save_edited_form(self, edited_form):
        if not self.filesystem.exists('master.form.lock'):
            raise FormEditionNotOpen()

        # Check that existing variables keep the same vtype in the edited form
        current_vtypes = self.form_master.get_vtypes()
        edited_vtypes = edited_form.get_vtypes()
        invalid_vars = []
        for key, vtype in edited_vtypes.items():
            if (key in current_vtypes) and (current_vtypes[key] != vtype):
                invalid_vars.append((key,vtype,current_vtypes[key]))
        if len(invalid_vars) > 0:
            msg = '\n'.join('%s has type %s but must be %s' % iv
                            for iv in invalid_vars)
            raise FormEditionLockedType(msg)

        # Check that the edited form does not have orphan variables
        # (that are in df but not in current form master)
        orphan_variables = self.get_orphan_variables(current_vtypes=current_vtypes)
        if len(orphan_variables.intersection(edited_vtypes.keys())) > 0:
            raise FormEditionOrphanError(list(sorted(orphan_variables)))

        self.set_form_master(edited_form, save=True, overwrite=True)

    def get_orphan_variables(self, current_vtypes=None):
        if self.df is None:
            return set()
        current_vtypes = (current_vtypes if current_vtypes is not None
                          else self.form_master.get_vtypes())
        return set(self.df.columns).difference(current_vtypes.keys())

    def set_form_master(self, form, save=False, overwrite=False):
        # TODO: utest and check consistency with pending live forms
        if not save:
            logger.info('Set form master of sheet %s set (form label: %s)',
                        self.label, form.label)
        self.form_master = form
        if save:
            self.save_form_master(overwrite=overwrite)
            logger.info('Set and save form master of sheet %s set (form label: %s)',
                        self.label, form.label)


    ## End of methods used for FormEditor IO
    def _remove_from_value_to_index(self, entry_df):
        # TODO utest that value indexes are properly maintained
        # after entry deletion
        entry_cols_set = set(entry_df.columns)
        for cols, value_to_index in self.value_to_index:
            if entry_cols_set.issubset(cols):
                for col_values, df_index in entry_df[list(cols)].groupby():
                    pass

    def _add_to_value_to_index(self):
        pass

    def __df_index_from_value_wip(self, value_dict, view=None,
                                  full_mask_search=True):
        # Trying to use a maintained mapping of values to index to speed up
        # ...
        if len(value_dict) == 0:
            return None
        view = view if view is not None else self.default_view
        df = self.get_df_view(view)
        if df is None or df.shape[0] == 0:
            return None
        sorted_cols = tuple(sorted(value_dict.keys()))
        value_to_index = self.value_to_index[view]
        matched_index = set()
        if not full_mask_search:
            if sorted_cols not in value_to_index:
                logger.debug('Sheet %s view %s, build value index for columns %s',
                             self.label, view, sorted_cols)
                get_indexes = lambda x: set(x.index.to_list())
                value_to_index[sorted_cols] = (df.groupby(by=list(sorted_cols))
                                               .apply(get_indexes))
            to_look_up = tuple(value_dict[k] for k in sorted_cols)
            try:
                matched_index = value_to_index[sorted_cols][to_look_up]
            except KeyError:
                pass
        matched_index = list(matched_index)

        if full_mask_search or \
            not all(df.loc[matched_index, col].all() for col in sorted_cols):
            logger.warning('Value to index embarassingly failed from keys %s',
                           sorted_cols)
            # The check that does prevent missed values...
            # Only insures that found index is actually associated with
            # queried values
            iter_vd = iter(value_dict.items())
            first_key, first_value = next(iter_vd)
            m = df[first_key] == first_value
            for key, value in iter_vd:
                m &= (df[key] == value)
            matched_index = df[m].index.to_list()
            logger.debug('Sheet %s, view %s: Index matching %s: %s',
                         self.label, view, value_dict, matched_index)

        return matched_index[0] if len(matched_index)==1 else matched_index


    def df_index_from_value(self, value_dict, view=None):
        view = view if view is not None else self.default_view
        df = self.get_df_view(view)
        if df is None or df.shape[0] == 0:
            return []
        matched_index = df_index_from_value(df, value_dict)
        logger.debug('Sheet %s, view %s: Index matching %s: %s',
                     self.label, view, value_dict, matched_index)
        return matched_index

    def save(self, overwrite=False):
        if self.filesystem is None:
            raise IOError('Cannot save data of sheet %s (no associated '\
                          'filesystem)')

        if not self.filesystem.exists('data'):
            self.filesystem.makedirs('data')

        self.save_form_master(overwrite=overwrite)
        self.save_properties(overwrite=overwrite)
        self.save_all_data()
        for form_id, form in self.live_forms.items():
            for section_name, section in form.sections.items():
                for item in section.items:
                    for key, value_str in item.values_str:
                        self.save_live_form_input(form_id, section_name,
                                                  key, value_str)

    def save_all_data(self, entry_df=None):
        # TODO: admin role + lock !
        if self.df is not None and self.df.shape[0] > 0:
            main_data_fn = 'main.csv'
            if not self.filesystem.exists('data'):
                logger.info('Sheet %s: Create data folder', self.label)
                self.filesystem.makedirs('data')
            logger.info('Sheet %s: Save all data', self.label)
            self.filesystem.save(op.join('data', main_data_fn),
                                 self.df_to_str(self.df.drop(columns='__fn__')),
                                 overwrite=True)

            logger.info('Remove all single data entries of sheet %s',
                        self.label)
            for entry_idx, data_fn in self.df['__fn__'].iteritems():
                if not pd.isna(data_fn):
                    logger.info('Delete file of entry %s: %s', data_fn, entry_idx)
                    self.filesystem.remove(data_fn)
                else:
                    logger.info('No file to delete for entry %s', entry_idx)

            self.df['__fn__'] = pd.NA

    def load_live_forms(self):
        # TODO: handle consistency with form master, + ustests
        logger.debug('Load live forms for sheet %s', self.label)
        top_folder = self.get_live_forms_folder()
        if self.filesystem.exists(top_folder):
            live_form_folders = self.filesystem.listdir(top_folder)
            for form_id_str in live_form_folders:
                live_form_folder = op.join(top_folder, form_id_str)
                if self.filesystem.exists(op.join(live_form_folder,
                                                  'TO_DELETE')):
                    # TODO: utest
                    logger.debug('Live form %s marked as to remove',
                                 form_id_str)
                    try:
                        self.filesystem.rmtree(live_form_folder)
                    except Exception as e:
                        logger.error('Error while deleting live form '\
                                     'folder %s: %s', live_form_folder,
                                     repr(e))
                    continue
                saved_entries = defaultdict(dict)
                for entry_fn in self.filesystem.listdir(live_form_folder):
                    content = self.filesystem.load(op.join(live_form_folder,
                                                           entry_fn))
                    section, key, value_str = json.loads(content)
                    saved_entries[section][key] = value_str
                logger.debug2('Create live form %s with %d saved entries',
                             form_id_str, len(saved_entries))
                first_section = self.form_master.first_section()

                if '__entry_id__' in saved_entries[first_section]:
                    entry_id_str = (saved_entries[first_section]
                                    .pop('__entry_id__'))
                    entry_id = np.int64(entry_id_str)
                    update_idx_str = (saved_entries[first_section]
                                      .pop('__update_idx__'))

                    submission = (saved_entries[first_section]
                                  .pop('__submission__'))

                    logger.debug2('Loaded from live from file: %s '\
                                 '__entry_id__ = %s, __update_idx__ = %s ',
                                  entry_id_str, update_idx_str)

                    form_id = int(form_id_str) # TODO factorize
                    live_form = {'append' : self.form_new_entry,
                                 'update' : self.form_update_entry,
                                 'set': self.form_set_entry}[submission](entry_id,
                                                                         form_id)
                    # From this point form input saving callback is active
                    for section, entries in saved_entries.items():
                        for key, value_str in entries.items():
                            live_form[section][key].set_input_str(value_str,
                                                                  use_callback=False,
                                                                  force=True)
                    first_section = live_form[live_form.first_section()]
                    logger.debug2('IDs after live form input: __entry_id__=%d, '\
                                 '__update_idx__=%d',
                                 first_section['__entry_id__'].get_value(),
                                 first_section['__update_idx__'].get_value(),)

                    self.live_forms[form_id] = live_form
                else:
                    logger.error('Cannot load live form %s', form_id_str)
        else:
            logger.debug2('Live form folder %s is empty', top_folder)

    def save_form_master(self, overwrite=False):
        if self.filesystem is None:
            raise Exception('No filesystem available to save form master '\
                            'for sheet %s', self.label)

        if self.form_master is not None:
            form_content = self.form_master.to_json()
            logger.info('Save form master of sheet %s' % self.label)
            self.filesystem.save('master.form', form_content,
                                 overwrite=overwrite)
        else:
            logger.info('No form master to save for sheet %s' % self.label)

    def get_live_forms_folder(self):
        return op.join('live_forms', protect_fn(self.user))

    def users_with_pending_live_forms(self):
        users = []
        if self.filesystem.exists('live_forms'):
            for user_name in self.filesystem.listdir('live_forms'):
                if len(self.filesystem.listdir(op.join('live_forms', user_name))) > 0:
                    users.append(user_name)
        return users

    def export_to_pdf(self, output_pdf_abs_fn, password, view=None,
                      columns=None, sort_by=None):
        assert(self.filesystem is not None)
        weasyprint = import_module('weasyprint')
        PyPDF2 = import_module('PyPDF2')
        output_pdf_fn = op.normpath(output_pdf_abs_fn)
        if self.df is None:
            logger.warning('No data to export')
            return

        df = self.get_df_view(view).reset_index(drop=True)
        if sort_by is not None:
            df.sort_values(by=sort_by, inplace=True)
        if columns is not None:
            df = df[columns]

        # todo add jinja2 dep
        css_fit = weasyprint.CSS(string=(
            "@page scaled {\n"
            "    size: 400mm 300mm;\n"
            "}"
            "body {\n"
            "   page: scaled;\n"
            "}\n"
        ))

        df_html = (df.style.hide_index().render()) # .apply(highlight_odd_row, axis=1)
         # self.df.to_html(classes='wide', escape=False)
        html_page = HTML_TOP + df_html + HTML_BOTTOM

        fpdf = BytesIO()
        weasyprint.HTML(string=html_page).write_pdf(fpdf, stylesheets=[css_fit])

        output = PyPDF2.PdfFileWriter()
        input_pdf = PyPDF2.PdfFileReader(fpdf)

        for i in range(0, input_pdf.getNumPages()):
            output.addPage(input_pdf.getPage(i))

        with open(output_pdf_fn, 'wb') as fout:
            if password is not None:
                output.encrypt(password, use_128bit=True)
            output.write(fout)

    @staticmethod
    def get_sheet_label_from_filesystem(fs):
        return PurePath(fs.root_folder).parts[-1]

    def validate_sheet_label(self, label):
        if DataSheet.SHEET_LABEL_RE.match(label) is None:
            raise InvalidSheetLabel("Sheet label %s has invalid format")
        return label

    def set_plugin(self, plugin, overwrite=None):
        plugin_str = None
        if isinstance(plugin, str):
            plugin_str = plugin
            plugin = (module_from_code_str(plugin)
                      .CustomSheetPlugin(self))
        self.plugin = plugin
        # cached views invalidated there:
        views = plugin.views(self.base_views())
        logger.debug2('Sheet %s, load plugin views: %s',
                     self.label, ','.join(views))
        self.set_views(views)
        default_view = plugin.default_view()
        if default_view is not None:
            self.set_default_view(default_view)
        if plugin_str is not None:
            self.dump_plugin_code(plugin_str, overwrite=overwrite)

        self.plugin.set_workbook(self.workbook)

    def after_workbook_load(self):
        self.plugin.after_workbook_load()

    def view_validity(self, view_label=None):
        if view_label is None:
            view_label = self.default_view

        cached_validity = self.cached_validity

        validity_df = cached_validity[view_label]
        if validity_df is None:
            validity_df = self.plugin.view_validity(self.get_df_view(view_label),
                                                    view_label)
            if validity_df is not None:
                logger.debug('Update cached validity for view "%s". '\
                             'Got columns: %s', view_label,
                             ', '.join(validity_df.columns))
            else:
                logger.warning('Update cached  view validity "%s": None',
                               view_label)
            if self.df is not None:
                # IMPORTANT: ASSUME that validity_df aligns with self.df...
                # but that may not be the case -> TODO clarify
                inconsistent_ids = (self.inconsistent_entries()
                                    .intersection(validity_df.index))
                validity_df.loc[inconsistent_ids, :] = False
            cached_validity[view_label] = validity_df
        return validity_df

    def __eq__(self, other):
        # TODO add sort by column in plugin
        # TODO maintain sorting
        # TODO df equality test while ignoring row order: dfs_weak_equal(df1, df2)
        # TODO check weird index, add index check at utest main_usage
        return isinstance(other, DataSheet) and self.label==other.label and \
            df_weak_equal(self.df, other.df) and \
            self.form_master==other.form_master

    def df_from_str(self, df_str):
        if df_str == '':
            return pd.DataFrame()
        converters = {k: Unformatter(self.form_master, k) \
                      for k in self.form_master.key_to_items}
        df = pd.read_csv(io.StringIO(df_str), sep=DataSheet.CSV_SEPARATOR,
                         engine='python', index_col=False,
                         converters=converters)

        def hex_to_int(h):
            try:
                return np.int64(int(h, 16))
            except OverflowError:
                logger.error('+++++++++++++++++++++++++++++++++++++++++')
                logger.error('Cannot convert uuid to signed int64. ' \
                             'Generate a new one. This must be saved later!')
                logger.error('+++++++++++++++++++++++++++++++++++++++++')
                return np.int64(int.from_bytes(uuid1().bytes,
                                               byteorder='big',
                                               signed=True) >> 64)
        if '__origin_id__' in df.columns:
            df['__entry_id__'] = (df['__origin_id__']
                                  .apply(hex_to_int)
                                  .astype(np.int64))
        else:
            df['__entry_id__'] = (df['__entry_id__']
                                  .apply(hex_to_int)
                                  .astype(np.int64))

        if df.dtypes['__entry_id__'] != np.int64:
            print('df_from_str: Error __entry_id__ from __origin_id__')
            from IPython import embed; embed()

        df['__update_idx__'] = (df['__update_idx__'].apply(int)
                                .astype(np.int64))
        df['__conflict_idx__'] = np.int64(0)
        df.set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'],
                     inplace=True)
        return df

    def df_to_str(self, df=None):
        df = df if df is not None else self.df
        if df is None or df.shape[0]==0:
            return ''

        if '__origin_id__' in df.columns:
            df = df.drop(columns=['__origin_id__'])

        if '__conflict_idx__' in df.columns:
            df = df.drop(columns=['__conflict_idx__'])

        df = df.copy()
        for col in df.columns:
            if col not in ['__entry_id__', '__update_idx__']:
                logger.debug2('df_to_str: format column %s', col)
                f = lambda v: (self.form_master.format(col,v) \
                               if not pd.isna(v) else '')
                try:
                    df[[col]] = df[[col]].applymap(f)
                except AttributeError:
                    from IPython import embed; embed()

        df = df.reset_index()
        df['__entry_id__'] = df['__entry_id__'].apply(lambda x: hex(x))
        df['__update_idx__'] = df['__update_idx__'].apply(str)
        content = df.to_csv(sep=DataSheet.CSV_SEPARATOR, index=False,
                            quoting=csv.QUOTE_NONNUMERIC)
        return content

    def invalidate_cached_views(self):
        for view in self.views:
            self.cached_views[view] = None
            self.cached_validity[view] = None
            self.cached_inconsistent_entries = None
        self.notifier.notify('views_refreshed')

    def get_df_view(self, view_label=None):

        if view_label is None:
            view_label = self.default_view
        cached_views = self.cached_views

        view_df = cached_views[view_label]
        if view_df is None:
            view_df = self.views[view_label](self.df)
            if view_df is not None:
                logger.debug('Sheet %s: Update cached view "%s". Shape %s. '\
                             'Columns: %s', self.label, view_label, view_df.shape,
                             ', '.join(view_df.columns))
                if '__fn__' in view_df.columns:
                    view_df = view_df.drop(columns=['__fn__'])
            else:
                logger.debug('Update cached view "%s": None', view_label)
            cached_views[view_label] = view_df

        return view_df

    def set_default_view(self, view_label):
        if view_label not in self.views:
            raise Exception('View %s not found in %s' % \
                            (view_label, ', '.join(self.views)))
        self.default_view = view_label

    def add_views(self, views_getters):
        self.views.update(views_getters)
        self.invalidate_cached_views()

    def set_views(self, views_getters):
        """
        Args:
            - views_getters (dict str:callable):
            Map a view label to a callable that computes the view
            Signature is callable(dataframe)
        """
        self.views = views_getters
        self.invalidate_cached_views()

    # def is_valid(self):
    #     df = self.get_df_view('latest')
    #     if df is not None:
    #         return all(df[col].is_unique \
    #                    for col in self.form_master.unique_keys)
    #     else:
    #         return True

    def inconsistent_entries(self):
        if self.cached_inconsistent_entries is None:
            self.cached_inconsistent_entries = set()
            if self.df is not None:
                conflicting_uids = self.concurrent_updated_entries()
                dup_ids = self.duplicate_entries(conflicting_ids=conflicting_uids)
                self.cached_inconsistent_entries.update(conflicting_uids)
                self.cached_inconsistent_entries.update(dup_ids)
        return self.cached_inconsistent_entries

    def duplicate_entries(self, df=None, conflicting_ids=None,
                          cols_to_check=None):
        df = df if df is not None else self.df
        if df is None:
            return set()

        cols_to_check = cols_to_check if cols_to_check is not None \
            else self.form_master.unique_keys

        if conflicting_ids is None:
            conflicting_ids = self.concurrent_updated_entries(df)
        if len(conflicting_ids) > 0:
            df = df.drop(conflicting_ids)
        ids_of_duplicates = set()
        latest_df = self.latest_update_df(df)
        for col in cols_to_check:
            m = latest_df[col].duplicated(keep=False)
            ids_of_duplicates.update(latest_df[m].index)
        if len(ids_of_duplicates) > 0:
            logger.error('Duplicate entries for column(s) %s:\n %s',
                         ', '.join(cols_to_check), ids_of_duplicates)
        return ids_of_duplicates

    def concurrent_updated_entries(self, df=None):
        df = df if df is not None else self.df
        if df is None:
            return set()
        ids_of_conflicts = self.df.query('__conflict_idx__ > 0').index
        if len(ids_of_conflicts) > 0:
            logger.warning('Sheet %s: Conflicting entries: %s', self.label,
                           ids_of_conflicts.to_list())
        return ids_of_conflicts

    def validate_unique(self, key, value, update_idx, entry_id, conflict_idx):
        logger.debug2('Sheet %s: Validate uniqueness of %s', self.label, key)
        if self.df is None or self.df.shape[0]==0:
            return True
        def index_has_locs(index, seq):
            try:
                locs = index.get_locs(seq)
                return len(locs) > 0
            except KeyError:
                return False

        if entry_id not in self.df.index.get_level_values('__entry_id__'):
            # Entry not there -> new one
            tmp_entry_id = self.new_entry_id()
            tmp_entry_df = (pd.DataFrame({key:[value],
                                          '__entry_id__' : [tmp_entry_id],
                                          '__update_idx__' : [0],
                                          '__conflict_idx__' : [0]})
                            .set_index(['__entry_id__', '__update_idx__',
                                        '__conflict_idx__']))
            tmp_df = self.df[[key]].append(tmp_entry_df)
        elif index_has_locs(self.df.index, (entry_id, update_idx, conflict_idx)):
            # Entry already there -> modification
            tmp_df = self.df[[key]].copy()
            tmp_df.loc[[(entry_id, update_idx, conflict_idx)], key] = value
            tmp_entry_df = tmp_df.loc[[(entry_id, update_idx, conflict_idx)]]
        else:
            # Entry to update
            tmp_entry_df = (pd.DataFrame({key:[value],
                                          '__entry_id__' : [entry_id],
                                          '__update_idx__' : [update_idx],
                                          '__conflict_idx__' : [0]})
                            .set_index(['__entry_id__', '__update_idx__',
                                        '__conflict_idx__']))
            tmp_df = self.df[[key]].append(tmp_entry_df)
        duplicate_entry_ids = self.duplicate_entries(tmp_df,
                                                     cols_to_check=[key])
        duplicate_entry_ids.difference_update(self.concurrent_updated_entries(tmp_df))
        duplicate_candidate_ids = [ii[0] for ii in duplicate_entry_ids]
        unique_ok = tmp_entry_df.index[0][0] not in duplicate_candidate_ids
        logger.debug2('Check if %s is in duplicate candidates %s', entry_id,
                      duplicate_candidate_ids)
        if not unique_ok:
            logger.warning('Value %s for key %s is not unique', value, key)
        return unique_ok

    def form_update_entry(self, entry_idx, form_id=None):
        """
        Create a form and fill it with content of an existing entry.
        Some item are disabled according to item.freeze_on_update
        """
        if self.form_master is not None and self.has_write_access:
            entry_dict = self.df.loc[[entry_idx]].to_dict('record')[0]
            new_update_idx = self.df.loc[entry_idx[0]].index.max()[0] + 1
            form = self._new_form('append', entry_dict=entry_dict,
                                  form_id=form_id, entry_id=entry_idx[0],
                                  update_idx=new_update_idx)
            for item in form.to_freeze_on_update:
                item.set_editable(False)
            return form
        else:
            return None

    def form_new_entry(self, entry_idx=None, form_id=None):
        if not self.has_write_access:
            logger.error('Sheet %s: Cannot create form (no write access)',
                         self.label)
            return None
        return self._new_form('append', form_id=form_id)

    def form_set_entry(self, entry_idx, form_id=None):
        if not self.has_write_access:
            return None
        entry_dict = self.df.loc[[entry_idx]].to_dict('record')[0]
        return self._new_form('set', entry_dict=entry_dict, form_id=form_id,
                              entry_id=entry_idx[0], update_idx=entry_idx[1],
                              conflict_idx=entry_idx[2])

    def _new_form(self, submission, entry_dict=None, entry_id=None,
                  form_id=None, update_idx=np.int64(0),
                  conflict_idx=np.int64(0)):
        if self.form_master is None:
            raise NoFormMasterError()

        entry_dict = entry_dict if entry_dict is not None else {}
        entry_dict.pop('__fn__', None)

        logger.debug2('Sheet %s: fork from master', self.label)
        form = self.form_master.new()
        form.set_user(self.user)
        forms_folder = self.get_live_forms_folder()

        if form_id is None:
            form_id = uuid1().int
            # Change ID if already in use:
            if self.filesystem is not None:
                # TODO: add user lock for live form IO!
                while self.filesystem.exists(op.join(forms_folder,
                                                     '%d' % form_id)):
                    logger.warning('Form UUID %d is already used by '\
                                   'a saved live forms of sheet %s', form_id,
                               self.label)
                    form_id = uuid1().int

        if self.filesystem is not None:
            if not self.filesystem.exists(forms_folder):
                self.filesystem.makedirs(forms_folder)

            form_folder = op.join(forms_folder, '%d' % form_id)
            self.filesystem.makedirs(form_folder)

            # f = lambda sec, k, s: self.save_live_form_input(form_id, sec, k, s)
            form.set_input_callback(LazyFunc(self.save_live_form_input,
                                             form_id=form_id))

        entry_id = entry_id if entry_id is not None else self.new_entry_id()

        form.set_values_from_entry(entry_dict)

        logger.debug2('Sheet %s: set unique validator', self.label)

        form.set_unique_validator(LazyFunc(self.validate_unique,
                                           update_idx=update_idx,
                                           entry_id=entry_id,
                                           conflict_idx=conflict_idx))
        entry_id_str = str(entry_id)
        update_idx_str = str(update_idx)
        conflict_idx_str = str(conflict_idx)
        logger.debug2('Sheet %s: prepend entry id %d, update idx %s '\
                     'and submission mode %s', self.label, entry_id,
                     update_idx, submission)
        form._prepend('__entry_id__', entry_id, 'int64')
        form._prepend('__update_idx__', update_idx, 'int64')
        form._prepend('__conflict_idx__', conflict_idx, 'int64')
        form._prepend('__submission__', submission, 'text')

        if self.filesystem is not None:
            first_section = form.first_section()
            self.save_live_form_input(form_id, first_section,
                                      '__entry_id__', entry_id_str)
            self.save_live_form_input(form_id, first_section,
                                      '__update_idx__', update_idx_str)
            self.save_live_form_input(form_id, first_section,
                                      '__conflict_idx__', conflict_idx_str)
            self.save_live_form_input(form_id, first_section,
                                      '__submission__', submission)

        logger.debug2('Sheet %s: call form.set_on_submission', self.label)
        form.set_on_submission(LazyFunc(self.on_submitted_entry, form_id=form_id))
        form.set_on_cancel(LazyFunc(self.clean_live_form, form_id=form_id))

        self.live_forms[form_id] = form

        return form

    # @check_role(UserRole.EDITOR) # TODO
    def save_live_form_input(self, form_id, form_section, item_key, input_str):
        fn = self.get_live_form_entry_fn(form_id, form_section,
                                         item_key, input_str)
        logger.debug2('Save input of form %d, section "%s" and key "%s" to '\
                     'file %s', form_id, form_section, item_key, fn)
        entry = (form_section, item_key, input_str)
        self.filesystem.save(fn, json.dumps(entry), overwrite=True)

    def get_live_form_entry_fn(self, form_id, form_section, item_key, input_str):
        bfn = '{section}_{item}.json'.format(section=form_section,
                                                   item=item_key)
        folder = self.get_live_form_folder(form_id)
        return op.join(folder, bfn)

    def get_live_form_folder(self, form_id):
        #form_folder = op.join(self.get_live_forms_folder(), '%d' % form_id)
        return op.join(self.get_live_forms_folder(), '%d' % form_id)

    def new_entry_id(self):
        """ Return a 64-bit signed int that fits pandas.Int64Index """
        uid = np.int64(int.from_bytes(uuid1().bytes,
                                      byteorder='big',
                                      signed=True) >> 64)
        if self.df is not None:
            while uid in self.df.index:
                uid = np.int64(int.from_bytes(uuid1().bytes,
                                              byteorder='big',
                                              signed=True) >> 64)
        return uid

    def on_submitted_entry(self, entry_dict, form_id):
        entry_dict = entry_dict.copy()
        submission_mode = entry_dict.pop('__submission__')
        entry_id = entry_dict.pop('__entry_id__')
        update_idx = entry_dict.pop('__update_idx__')
        conflict_idx = entry_dict.pop('__conflict_idx__')
        logger.debug2('Processing submission of entry %d, '\
                     'update idx: %d, mode: %s',
                     entry_id, update_idx, submission_mode)
        if submission_mode == 'append':
            self.append_entry(entry_dict, (entry_id, update_idx, conflict_idx))
        elif submission_mode == 'set':
            # print('set submission')
            # from IPython import embed; embed()
            self.set_entry(entry_dict, (entry_id, update_idx, conflict_idx))
        else:
            raise Exception('Unknown submission mode "%s"' % submission_mode)

        form_folder = self.get_live_form_folder(form_id)
        self.filesystem.save(op.join(form_folder, 'TO_DELETE'), '',
                             overwrite=True)
        self.clean_live_form(form_id)

    def clean_live_form(self, form_id):
        form_folder = self.get_live_form_folder(form_id)
        logger.info('Remove live form folder %s', form_folder)
        try:
            self.filesystem.rmtree(form_folder)
        except Exception as e:
            logger.error('Error while deleting live form folder %s: %s',
                         form_folder, repr(e))

        self.live_forms.pop(form_id)
        logger.debug2('Sheet %s: Popped form_id %s -> remaining forms: %s',
                     self.label, form_id,
                     ', '.join(str(fid) for fid in self.live_forms))

    def add_entry(self, entry_dict, entry_idx, process_entry_df,
                  save_func=None):
        if save_func is None:
            save_func = self.save_single_entry
        if logger.level >= logging.DEBUG:
            logger.debug('Sheet %s: Add entry %s, (keys: %s)',
                         self.label, entry_idx, ','.join(entry_dict.keys()))

        # Convert entry dict to pandas.DataFrame and set index
        idx_arrays = [np.array([entry_idx[0]], dtype=np.int64),
                      np.array([entry_idx[1]], dtype=np.int64),
                      np.array([entry_idx[2]], dtype=np.int64)]
        index = pd.MultiIndex.from_arrays(idx_arrays,
                                          names=('__entry_id__',
                                                 '__update_idx__',
                                                 '__conflict_idx__'))
        entry_df = pd.DataFrame([entry_dict], index=index)

        dkeys = self.form_master.datetime_keys
        datetime_cols = list(set(entry_df.columns).intersection(dkeys))
        other_cols =  list(set(entry_df.columns).difference(dkeys))
        entry_df[other_cols] = entry_df[other_cols].fillna(pd.NA)
        entry_df[datetime_cols] = entry_df[datetime_cols].fillna(pd.NaT)

        logger.debug('Sheet %s: process addition of entry_df: index=%s, cols=%s',
                     self.label, entry_df.index.name,
                     ','.join(entry_df.columns))

        # Inject entry in current dataframe
        # Index of entry may change because of conflicting entries
        entry_idx = process_entry_df(entry_df)

        logger.debug('Sheet %s: process saving of entry_df: index=%s, cols=%s',
                     self.label, entry_df.index.name,
                     ','.join(entry_df.columns))
        # Save to file if needed
        fn = save_func(entry_df)
        logger.debug('Sheet %s: saved entry_df (index=%s) to fn: %s',
                     self.label, entry_df.index.name, fn)

        if fn is not None:
            self.df.loc[entry_idx, '__fn__'] = fn

        self.invalidate_cached_views()
        return entry_df

    def save_single_entry(self, entry_df):
        if self.filesystem is not None:
            entry_rfn = '%d.csv' % uuid1().int
            while self.filesystem.exists(op.join('data', entry_rfn)):
                entry_rfn = '%d.csv' % uuid1().int
            entry_fn = op.join('data', entry_rfn)
            logger.debug('Sheet %s: save entry %s to %s',
                         self.label, entry_df.index.to_list(), entry_fn)
            self.filesystem.save(entry_fn, self.df_to_str(entry_df))
            return entry_fn
        else:
            logger.debug2('Sheet %s: entry %d not saved (no associated '\
                          'filesystem)', self.label, entry_df.index.to_list())
        return None

    def add_new_entry(self, entry_dict):
        form = self.form_new_entry()
        form.set_values_from_entry(entry_dict)
        form.submit()
        return form

    def append_entry(self, entry_dict, entry_idx=None):
        if entry_idx is None:
            entry_idx = (self.new_entry_id(), 0)
        self.add_entry(entry_dict, entry_idx, self._append_df)

    # TODO: admin feature!
    def delete_entry(self, entry_idx):
        logger.debug('Sheet %s (df shape: %s): delete entry %s',
                     self.label, self.df.shape, entry_idx)
        deleted_entry = self.df.loc[[entry_idx]]
        self.notifier.notify('pre_delete_entry', entry_idx)
        entry_fn = self.df.loc[entry_idx, '__fn__']
        self.df.drop(entry_idx, inplace=True)

        logger.debug2('Sheet %s: df shape after deletion: %s',
                     self.label, self.df.shape)

        if self.filesystem is not None:
            if not pd.isna(entry_fn):
                self.filesystem.remove(entry_fn)
            else:
                self.save_all_data()

        # TODO: update conflit idx!
        self.resolve_conflicting_entries(entry_idx)
        self.invalidate_cached_views()
        self.notifier.notify('deleted_entry', entry_df=deleted_entry)

    def set_entry(self, entry_dict, entry_idx):
        """ WARNING: this is an admin feature, not conflict-free! """
        self.add_entry(entry_dict, entry_idx, self.set_entry_df,
                       save_func=self.save_all_data)

    def _append_df(self, entry_df):
        # TODO: use merge instead of append
        # -> have to change notification and QListView
        """ ASSUME: entry index is properly set """
        logger.debug('Append df to sheet "%s" (index: %s, columns: %s)',
                     self.label, entry_df.index.to_list(),
                     ','.join(entry_df.columns))

        if entry_df.shape[0] == 0:
            logger.debug2('Empty entry not appended to sheet %s', self.label)
            return None

        self.df = self.df.append(entry_df)
        self.df.sort_index(inplace=True)
        entry_index = self.fix_conflicting_entries(index_to_track=entry_df.index[0])
        logger.debug2('Entry has been appended to sheet %s', self.label)
        logger.debug2('Resulting df has columns: %s)', ','.join(self.df.columns))
        self.invalidate_cached_views()
        self.notifier.notify('appended_entry', entry_df=entry_df)

        # Note: only the index of the first row of entry_df is returned.
        # This is expected to work only for single entries
        return entry_index

    def resolve_conflicting_entries(self, entry_idx):
        try:
            locs = self.df.index.get_locs(entry_idx[:2])
        except KeyError:
            return
        if len(locs) == 1:
            new_index = self.df.index.to_list()
            prev_idx = new_index[locs[0]]
            new_index[locs[0]] = (prev_idx[0], prev_idx[1], 0)
            self.df.set_index(pd.MultiIndex.from_tuples(new_index,
                                                        names=self.df.index.names),
                              inplace=True)

    def fix_conflicting_entries(self, index_to_track=None):
        new_tracked_index = index_to_track
        index_to_track = index_to_track if index_to_track is not None else tuple()
        if self.df is None or self.df.shape[0] == 0:
            return None

        ipos_to_fix = np.flatnonzero(self.df.index.duplicated(keep=False))
        logger.debug('Check conflicting entries in %s',
                     [self.df.index[i] for i in ipos_to_fix])
        if len(ipos_to_fix) > 0:
            new_index = self.df.index.to_list()
            taken_cids = {}
            for ipos in ipos_to_fix:
                idx = self.df.index[ipos]
                # idx[0] = entry_id, idx[1] = update_idx, idx[2] = conflict_idx
                if idx[:2] not in taken_cids:
                    locs = self.df.index.get_locs(idx[:2])
                    taken_cids[idx[:2]] = set(self.df.index[locs]
                                              .get_level_values('__conflict_idx__'))
                cur_taken_ids = taken_cids[idx[:2]]
                new_conflict_idx = idx[2] + 1
                while new_conflict_idx in cur_taken_ids:
                    new_conflict_idx += 1
                cur_taken_ids.add(new_conflict_idx)
                new_index_entry = (idx[0], idx[1], new_conflict_idx)
                logger.info('Fix duplicate index %s -> %s', idx, new_index_entry)
                if index_to_track == idx:
                    new_tracked_index = new_index_entry
                new_index[ipos] = new_index_entry
            self.df.set_index(pd.MultiIndex.from_tuples(new_index,
                                                        names=self.df.index.names),
                              inplace=True)
        return new_tracked_index

    def set_entry_df(self, entry_df):
        logger.debug('Set df entry %s in sheet "%s" (index: %s, columns: %s)',
                     entry_df.index[0], self.label, entry_df.index.names,
                     ','.join(entry_df.columns))

        self.df.update(entry_df)
        entry_index = self.fix_conflicting_entries(entry_df.index[0])
        # see: https://github.com/pandas-dev/pandas/pull/40219
        #      https://stackoverflow.com/questions/28217172/why-does-pandas-dataframe-update-change-the-dtypes-of-the-updated-dataframe

        self.invalidate_cached_views()
        self.notifier.notify('entry_set', entry_idx=entry_index)
        return entry_index

    def import_df(self, imported_df):
        """ """
        assert('__entry_id__' not in imported_df.columns)
        assert('__update_idx__' not in imported_df.columns)
        assert('__conflict_idx__' not in imported_df.columns)
        if imported_df.index.names != ['__entry_id__', '__update_idx__',
                                       '__conflict_idx__']:
            logger.debug('Generate entry uuids for index of sheet %s',
                         self.label)
            nb_rows = imported_df.shape[0]
            ids = np.array([self.new_entry_id() \
                            for i in range(nb_rows)],
                           dtype=np.int64)
            uidx = np.zeros(nb_rows, dtype=np.int64)
            cidx = np.zeros(nb_rows, dtype=np.int64)
            index = pd.MultiIndex.from_arrays([ids, uidx, cidx],
                                              names=('__entry_id__',
                                                     '__update_idx__',
                                                     '__conflict_idx__'))
            imported_df.set_index(index, inplace=True)
        self._append_df(imported_df)

def shuffle_df_rows(df):
    new_order = np.random.permutation(range(df.shape[0]))
    if df.index.name is not None:
        df = df.reset_index()
    df2 = df.copy() #.astype(df.dtypes.to_dict())
    for irow in range(df.shape[0]):
        for icol in range(df.shape[1]):
            df2.iloc[new_order[irow],icol] = df.iloc[irow, icol]
    if df.index.name is not None:
        df2.set_index(df.index.name)
    return df2

def df_weak_equal(df1, df2):
    if df1.index.name is not None:
        df1 = df1.reset_index()
    if df2.index.name is not None:
        df2 = df2.reset_index()
    if set(df1.columns) != set(df2.columns):
        logger.debug('Columns differ (%s) != (%s)',
                     ','.join(df1.columns), ','.join(df2.columns))
        return False
    hash1 = df1.apply(lambda x: hash(tuple(x)), axis = 1)
    hash2 = df2[df1.columns].apply(lambda x: hash(tuple(x)), axis = 1)

    diff_hash = set(hash1).symmetric_difference(hash2)
    if len(diff_hash) > 0:
        
        mask_extra = hash1.isin(diff_hash).to_numpy()
        logger.debug('Entries in df1 and not in df2:\n%s',
                     df1[mask_extra])
        mask_extra = hash2.isin(diff_hash).to_numpy()
        logger.debug('Entries in df2 and not in df1:\n%s',
                     df2[mask_extra])
        return False
    return True

class TestDataSheet(unittest.TestCase):

    def setUp(self):
        # logger.setLevel(logging.DEBUG)
        logger.setLevel("DEBUG2")
        self.tmp_dir = tempfile.mkdtemp()

        self.form_def_ts_data = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                         'freeze_on_update' : True,
                        },
                        {'keys' : {'Age': None},
                         'vtype' :'int'},
                        {'keys' : {'Taille': None},
                         'vtype' :'number'},
                        {'keys' : {'Phone_Number': None},
                         'unique' : True},
                        {'keys' : {'Flag': None},
                         'vtype' : 'boolean'},
                        {'keys' : {'Comment': None},
                         'vtype' : 'text'},
                        {'keys' : {'Date': None},
                         'vtype' : 'date'},
                        {'keys' : {'Timestamp_Submission': None},
                         'vtype' :'datetime',
                         'generator' : 'timestamp_submission', }
                    ]
                }
            }
        }
        self.data_df_ts_data = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0004', 'CE0006']),
            ('__entry_id__', np.array([0, 0, 1], dtype=np.int64)),
            ('__update_idx__', np.array([0, 1, 0], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0], dtype=np.int64)),
            ('Age', pd.array([22, 50, None], dtype=pd.Int64Dtype())),
            ('Taille', [None, 1.7, 1.7]),
            ('Phone_Number', ['514', '514', '512']),
            ('Flag', [True, False, None]),
            ('Comment', ['a\tb', '"', '""']),
            ('Date', [date(2020,1,2), date(2020,1,21), date(2020,10,2)]),
            ('Timestamp_Submission', [datetime(2020,1,2,13,37),
                                      datetime(2021,2,2,13,37),
                                      datetime(2020,1,5,13,37)]),
        ])).set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'])

        self.sheet_id = 'Participant_info'
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'}),
                 FormItem(keys={'Age':None},
                          vtype='int', supported_languages={'French'},
                          default_language='French'),
                 FormItem(keys={'Timestamp_Creation':None},
                          vtype='datetime', generator='timestamp_creation',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Titre de formulaire'})

        self.user = 'me'
        self.sheet_folder = op.join(self.tmp_dir, self.sheet_id)
        os.makedirs(self.sheet_folder)
        self.filesystem = LocalFileSystem(self.sheet_folder)
        self.sheet = DataSheet(self.sheet_id, form, None,
                               self.user, self.filesystem)

        self.sheet_ts = DataSheet(self.sheet_id,
                                  Form.from_dict(self.form_def_ts_data),
                                  self.data_df_ts_data,
                                  self.user, self.filesystem,
                                  properties={'access_level':UserRole.MANAGER})
        self.sheet_ts.save()
        logger.debug('--------------------')
        logger.debug('utest setUp finished')


    def init_df_from_form_master(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                         'freeze_on_update' : True,
                        },
                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                },
                'section2' : {
                    'items' : [
                        {'keys' : {'Var1' : None},
                         'vtype' : 'int64'
                        },
                    ]
                },
                'section3' : {
                    'items' : [
                        {'keys' : {'Var1' : None},
                         'vtype' : 'int64'
                        },
                    ],
                }
            }
        }
        sheet_id = 'pinfo_with_duplicates'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)
        sheet = DataSheet(sheet_id, Form.from_dict(form_def),
                          None, user, filesystem)

        cols = ['__entry_id__', '__update_idx__', '__conflict_idx__', '__fn__',
                'Participant_ID', 'Name', 'Var1']
        expected_df = pd.DataFrame(columns=cols)
        expected_df['__entry_id__'] = expected_df['__entry_id__'].astype(np.int64)
        expected_df['__update_idx__'] = (expected_df['__update_idx__']
                                         .astype(np.int64))
        expected_df['__conflict_idx__'] = (expected_df['__conflict_idx__']
                                           .astype(np.int64))
        expected_df.set_index(['__entry_id__', '__update_idx__',
                               '__conflict_idx__'], inplace=True)

        expected_df['Participant_ID'] = (expected_df['Participant_ID']
                                         .astype('string'))
        expected_df['Name'] = (expected_df['Participant_ID']
                               .astype('string'))
        expected_df['Var1'] = expected_df['Var1'].astype('int64')
        assert_frame_equal(sheet.df, expected_df)

    def test_df_weak_equal(self):
        df1 = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0004', 'CE0006']),
            ('Age', [22, 50, None]),
            ('Timestamp', [datetime(2020,1,2,13,37),
                           datetime(2021,2,2,13,37),
                           datetime(2020,1,5,13,37)]),
        ]))
        df1.set_index('Participant_ID', inplace=True)

        self.assertTrue(df_weak_equal(df1, df1))
        self.assertTrue(df_weak_equal(df1, df1.reset_index()))
        self.assertTrue(df_weak_equal(df1, shuffle_df_rows(df1)))
        permutations = np.random.permutation(df1.columns)
        self.assertTrue(df_weak_equal(df1, df1[permutations]))
        self.assertFalse(df_weak_equal(df1, df1[df1.columns[1:]]))

        df2 = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0004', 'CE0006']),
            ('Age', [22, 51, None]),
            ('Timestamp', [datetime(2020,1,2,13,37),
                           datetime(2021,2,2,13,37),
                           datetime(2020,1,5,13,37)]),
        ]))
        self.assertFalse(df_weak_equal(df1, df2))

    def test_properties(self):
        self.assertEqual(self.sheet_ts.access_level, UserRole.MANAGER)
        self.assertEqual(self.sheet.access_level, UserRole.VIEWER)

        self.sheet_ts.update_properties({'lesca_participant_sheet' : True})
        self.sheet_ts.save_properties(overwrite=True)

        sheet_ts2 = DataSheet.from_files(self.user, self.sheet_ts.filesystem.clone())
        self.assertEqual(sheet_ts2.access_level, UserRole.MANAGER)
        self.assertTrue(sheet_ts2.get_property('lesca_participant_sheet'))

    def test_form_user(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'User' :
                                   {'French':'Utilisateur'}},
                         'vtype' : 'user_name'
                        },
                    ]
                }
            }
        }
        sheet_id = 'user_sheet'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        form_master = Form.from_dict(form_def)
        self.assertIsNone(form_master['section1']['User'].get_value())
        sheet = DataSheet(sheet_id, form_master, None, user, filesystem)
        form = sheet.form_new_entry()
        self.assertIsNone(form_master['section1']['User'].get_value())
        self.assertEqual(form['section1']['User'].get_value(), user)

    def test_unique_form_check(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                         'freeze_on_update' : True,
                        },
                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                }
            }
        }
        data = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['P1', 'P1', 'P2']), # last is dup
            ('__entry_id__',   np.array([0, 0, 1], dtype=np.int64)),
            ('__update_idx__', np.array([0, 1, 0], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0], dtype=np.int64)),
            ('Name', ['John', 'Jon', 'Robert']),
        ])).set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'])

        sheet_id = 'pinfo'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        logger.debug('utest: create sheet')
        sheet = DataSheet(sheet_id, Form.from_dict(form_def),
                          data, user, filesystem)

        logger.debug('utest: create update form')
        form = sheet.form_update_entry(sheet.df.index[0])
        self.assertTrue(form.is_valid())

        logger.debug('utest: create new entry form')
        form = sheet.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : 'P1'})
        self.assertFalse(form.is_valid())

    def test_inconsistencies(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                         'freeze_on_update' : True,
                        },
                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                }
            }
        }
        data = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['P1', 'P1', 'P2', 'P2']), # last is dup
            ('__entry_id__',   np.array([0, 0, 1, 2], dtype=np.int64)),
            # 2 first are conflicting updates
            ('__update_idx__', np.array([0, 0, 0, 0], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0, 0], dtype=np.int64)),
            ('Name', ['John', 'Jon', 'Robert', 'Dude']),
        ])).set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'])

        sheet_id = 'pinfo_with_duplicates'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        logger.debug('utest: create sheet with duplicates in data')
        sheet = DataSheet(sheet_id, Form.from_dict(form_def),
                          data, user, filesystem)

        # TODO use cell validity on top of row validity?
        self.assertEqual(sheet.inconsistent_entries(),
                         {(0,0,1), (0,0,2), (1,0,0), (2,0,0)})

    def test_index_from_value(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'freeze_on_update' : True,
                         'allow_empty' : False,
                        },
                        {'keys' : {'Interview' :
                                   {'French': "Type d'interview"}},
                         'freeze_on_update' : True,
                         'allow_empty' : False,
                        },

                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                }
            }
        }
        data = pd.DataFrame(OrderedDict([
            ('__entry_id__',     np.array([0, 0, 1, 2, 2], dtype=np.int64)),
            ('__update_idx__',   np.array([0, 1, 0, 0, 1], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0, 0, 0], dtype=np.int64)),
            ('Participant_ID', ['P1', 'P1', 'P1', 'P1', 'P1']),
            ('Interview', ['Npk', 'Npsy', 'Npsy', 'Prelim', 'Tuto']),
            ('Extra', ['yep', 'nope', 'maybe', 'sure', 'thing']),
        ])).set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'])

        sheet_id = 'sheet'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        logger.debug('utest: create sheet with duplicates in data')
        sheet = DataSheet(sheet_id, Form.from_dict(form_def),
                          data, user, filesystem)
        sheet.set_default_view('latest')

        # TODO ustest keys not found in df
        self.assertEqual(len(sheet.df_index_from_value({'Participant_ID' : 'P1',
                                                        'Interview' : 'Npk'})),
                         0)
        self.assertEqual(set(sheet.df_index_from_value({'Participant_ID' : 'P1',
                                                        'Interview' : 'Npsy'})),
                         {(0,1,0),(1,0,0)})
        self.assertEqual(len(sheet.df_index_from_value({'Participant_ID' : 'P3',
                                                        'Interview' : 'Npsy'})),
                         0)
        self.assertEqual(sheet.df_index_from_value({'Participant_ID' : 'P1',
                                                     'Interview' : 'Tuto'}),
                         [(2,1,0)])

        # Update entry
        # from IPython import embed; embed()
        form = sheet.form_update_entry((2,1,0))
        form.set_values_from_entry({'Extra' : 'waza'})
        form.submit()
        self.assertEqual(sheet.df_index_from_value({'Participant_ID' : 'P1',
                                                     'Interview' : 'Tuto'}),
                         [(2,2,0)])

        # No need to test data modications as long as search method is systematic
        # and does rely on secondary maintained indexes

        # New entry

        # Set existing entry

        # Delete entry


    def test_conflicting_update(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                         'freeze_on_update' : True,
                        },
                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                }
            }
        }
        data = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['P1', 'P1', 'P2', 'P1']),
            ('__entry_id__', np.array([0, 0, 2, 0], dtype=np.int64)),
            ('__update_idx__', np.array([0, 1, 0, 0], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0, 0], dtype=np.int64)),
            ('Name', ['John', 'Jon', 'Robert', 'Dude']),
        ])).set_index(['__entry_id__', '__update_idx__', '__conflict_idx__'])

        sheet_id = 'pinfo_with_conflicts'
        user = 'me'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        logger.debug('utest: create sheet with conlicting updates')
        logger.debug('\n%s', data)
        sheet = DataSheet(sheet_id, Form.from_dict(form_def),
                          data, user, filesystem)

        self.assertEqual(sheet.inconsistent_entries(), {(0,0,1),(0,0,2)})

    def test_duplicate_form_input(self):
        form = self.sheet_ts.form_new_entry()
        entry = {'Participant_ID' : 'CE0004', 'Age' : 55,
                 'Taille' : 1.6, 'Date' : date(2010,1,3),
                 'Phone_Number' : '555'}
        form.set_values_from_entry(entry)
        self.assertFalse(form.is_valid())

    def test_duplicate_form_input(self):
        form = self.sheet_ts.form_new_entry()
        entry = {'Participant_ID' : 'CE0004', 'Age' : 55,
                 'Taille' : 1.6, 'Date' : date(2010,1,3),
                 'Phone_Number' : '555'}
        form.set_values_from_entry(entry)
        self.assertFalse(form.is_valid())

    def test_form_edition_no_pending_live_forms(self):
        form = self.sheet_ts.form_new_entry()
        self.assertRaises(FormEditionBlockedByPendingLiveForm,
                          self.sheet_ts.get_form_for_edition)
        form.submit()
        self.sheet_ts.get_form_for_edition()

    def test_form_edition_lock(self):
        form_master = self.sheet_ts.get_form_for_edition()
        self.assertRaises(FormEditionLocked, self.sheet_ts.get_form_for_edition)
        self.sheet_ts.close_form_edition()

    def test_form_edition_save(self):
        form_master = self.sheet_ts.get_form_for_edition()
        new_label = 'new_form_label'
        form_master.label = new_label
        self.sheet_ts.save_edited_form(form_master)

        reloaded_sheet = DataSheet.from_files(self.user,
                                              self.sheet_ts.filesystem.clone())
        self.assertEqual(reloaded_sheet.form_master.label, new_label)

    def test_form_edition_save_lock(self):
        self.assertRaises(FormEditionNotOpen,
                          self.sheet_ts.save_edited_form, Form({}, 'fr', {'fr'}))
        form_master = self.sheet_ts.get_form_for_edition()
        form_master.label = 'new_label'
        self.sheet_ts.save_edited_form(form_master)
        self.sheet_ts.close_form_edition()
        self.assertRaises(FormEditionNotOpen,
                          self.sheet_ts.save_edited_form, Form({}, 'fr', {'fr'}))

    def test_form_edition_locked_types(self):
        form_master = self.sheet_ts.get_form_for_edition()
        form_master['section1'].items[1].vtype = 'text'
        self.assertRaises(FormEditionLockedType, self.sheet_ts.save_edited_form,
                          form_master)

    def test_form_edition_orphan_variables(self):
        form_master = self.sheet_ts.get_form_for_edition()
        age_item = form_master['section1'].items[1]
        save_age_item = FormItem(**age_item.to_dict())
        form_master.remove_item('section1', age_item)
        self.sheet_ts.save_edited_form(form_master)
        self.sheet_ts.close_form_edition()

        form_master = self.sheet_ts.get_form_for_edition()
        form_master.add_item('section1', age_item)
        self.assertRaises(FormEditionOrphanError, self.sheet_ts.save_edited_form,
                          form_master)

    def test_to_pdf(self):
        pdf_fn = op.join(self.tmp_dir, 'sheet.pdf')
        self.sheet_ts.export_to_pdf(pdf_fn, 'pwd')
        self.assertTrue(self.filesystem.exists(pdf_fn))

    def test_views(self):
        sheet = DataSheet('Participant_info',
                          Form.from_dict(self.form_def_ts_data),
                          df=self.data_df_ts_data)
        sheet.set_default_view('latest')
        df_latest = sheet.get_df_view()
        mask = df_latest.Participant_ID=='CE0004'
        self.assertEqual(df_latest.loc[mask, 'Age'].values[0], 50)

    def ___test_error_on_missing_columns(self):
        """
        Test error for columns that are in form_master but not in raw df
        """
        #TODO: remove if not useful
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'unique' : True,
                        },
                        {'keys' : {'Age': None},
                         'vtype' :'int'},
                        {'keys' : {'Timestamp': None},
                         'vtype' :'datetime',
                         'generator' : 'timestamp_creation', },
                        {'keys' : {'Extra_col' : None},
                         'vtype' : 'int'},
                    ]
                }
            }
        }

        sheet = DataSheet('Participant_info', Form.from_dict(form_def))
        # TODO: maybe allow extra columns, while warnning?
        self.assertRaises(FormDataInconsitency, sheet.set_df,
                          self.data_df_ts_data)

    def test_plugin_views(self):
        # TODO: test against all versions of plugin API (may change overtime)

        class Plugin(SheetPlugin):
            def views(self, base_views):
                base_views.update({'young' : lambda df: df[df.Age<50]})
                return base_views
            def default_view(self):
                return 'latest'
            def view_validity(self, df, view):
                return pd.DataFrame(index=df.index, columns=df.columns,
                                    data=np.ones(df.shape, dtype=bool))

        self.sheet_ts.set_plugin(Plugin(self.sheet_ts))
        df_young = self.sheet_ts.get_df_view('young')
        mask = df_young.Participant_ID=='CE0004'
        self.assertEqual(df_young.loc[mask, 'Age'].values[0], 22)
        validity = self.sheet_ts.view_validity('young')
        self.assertEqual(validity.shape, df_young.shape)
        self.assertTrue((validity.dtypes == bool).all())

    def test_validity(self):
        class Plugin(SheetPlugin):

            def views(self, base_views):
                return base_views

            def default_view(self):
                return 'latest'

            def view_validity(self, df, view):
                validity = pd.DataFrame(index=df.index, columns=df.columns,
                                        dtype=bool)
                if view == 'latest':
                    col = 'Taille'
                    validity[col] = ~df[col].duplicated(keep=False).to_numpy()
                return validity

        self.sheet_ts.set_plugin(Plugin(self.sheet_ts))
        # Check view validity
        view = self.sheet_ts.get_df_view('latest')
        validity = self.sheet_ts.view_validity('latest')
        expected_validity = pd.DataFrame(data=np.ones(view.shape, dtype=bool),
                                         index=view.index, columns=view.columns)
        expected_validity['Taille'] = False
        assert_frame_equal(validity, expected_validity)

        # Check that validity is recomputed when view is invalidated
        form = self.sheet_ts.form_update_entry(view.index[1])
        form['section1']['Taille'].set_input_str('1.5')
        form.submit()

        view = self.sheet_ts.get_df_view('latest')
        validity = self.sheet_ts.view_validity('latest')
        expected_validity = pd.DataFrame(index=view.index, columns=view.columns,
                                         dtype=bool)
        assert_frame_equal(validity, expected_validity)

    def test_data_io(self):
        form = self.sheet_ts.form_new_entry()
        entry = {'Participant_ID' : '"', 'Age' : 43,
                 'Taille' : 1.4, 'Comment' : '\t', 'Flag' : True,
                 'Date' : date(2030,1,3),
                 'Phone_Number' : '555'}
        form.set_values_from_entry(entry)
        logger.debug('-----------------------')
        logger.debug('utest: submit form')
        submitted_entry = form.submit()

        logger.debug('-----------------------')
        logger.debug('utest: load sheet again')
        sh2 = DataSheet.from_files(self.user, self.filesystem.clone())
        eid = submitted_entry['__entry_id__']
        loaded_entry = sh2.df.loc[[eid]].to_dict('record')[0]

        self.assertEqual(loaded_entry['Age'], entry['Age'])
        self.assertEqual(loaded_entry['Comment'], entry['Comment'])
        self.assertEqual(loaded_entry['Participant_ID'],
                         entry['Participant_ID'])
        self.assertEqual(loaded_entry['Phone_Number'],
                         entry['Phone_Number'])
        self.assertEqual(loaded_entry['Flag'],
                         entry['Flag'])
        self.assertEqual(loaded_entry['Date'],
                         entry['Date'])

    def test_form_new_entry(self):
        watched_entry = []
        def watch_entry(entry_df):
            watched_entry.append(entry_df)
        self.sheet_ts.notifier.add_watcher('appended_entry', watch_entry)

        form = self.sheet_ts.form_new_entry()
        self.assertEqual(form['section1']['__submission__'].get_value(),
                         'append')
        entry = {'Participant_ID' : 'CE0000', 'Age' : 43,
                 'Phone_Number' : '555'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))
        ts_before_submit = datetime.now()
        sleep(0.1)
        form.submit()
        self.assertTrue(self.sheet_ts.df.index.unique)
        entry_id = (form['section1']['__entry_id__'].get_value(),
                    form['section1']['__update_idx__'].get_value(),
                    form['section1']['__conflict_idx__'].get_value())
        last_entry = self.sheet_ts.df.loc[[entry_id]]
        last_entry_dict = last_entry.to_dict('record')[0]
        self.assertEqual(last_entry_dict['Age'], entry['Age'])
        self.assertEqual(last_entry_dict['Participant_ID'],
                         entry['Participant_ID'])
        self.assertEqual(last_entry_dict['Phone_Number'],
                         entry['Phone_Number'])
        self.assertGreater(last_entry_dict['Timestamp_Submission'],
                           ts_before_submit)
        self.assertEqual(watched_entry[0].to_dict('record')[0]['Age'],
                         entry['Age'])

    def test_form_entry_update(self):
        # Add a new entry from an existing one

        watched_entry = []
        def watch_entry(entry_df):
            watched_entry.append(entry_df)
        self.sheet_ts.notifier.add_watcher('appended_entry', watch_entry)

        entry_to_update = self.sheet_ts.df.index[0]
        previous_pid = self.sheet_ts.df.loc[entry_to_update, 'Participant_ID']
        logger.debug('-------------------------')
        logger.debug('utest: create update form')
        form = self.sheet_ts.form_update_entry(entry_to_update)
        self.assertEqual(form['section1']['__submission__'].get_value(),
                         'append')
        self.assertEqual((form['section1']['__entry_id__'].get_value(),
                          form['section1']['__update_idx__'].get_value()),
                         (entry_to_update[0], 2))
        # Check that Participant_ID is frozen (not editable)
        self.assertFalse(form['section1']['Participant_ID'].editable)
        self.assertRaises(NotEditableError,
                          form['section1']['Participant_ID'].set_input_str,
                          'CE0000')
        # Update the entry
        logger.debug('-----------------')
        logger.debug('utest: fill form')
        entry = {'Age' : 77, 'Phone_Number' : '444'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))
        ts_before_submit = datetime.now()
        self.assertEqual(type(form['section1']['__entry_id__'].get_value()),
                         np.int64)
        self.assertEqual(type(form['section1']['__update_idx__'].get_value()),
                         np.int64)

        sleep(0.1)
        logger.debug('-----------------')
        logger.debug('utest: submit form')
        form.submit()


        entry_idx = (form['section1']['__entry_id__'].get_value(),
                     form['section1']['__update_idx__'].get_value(),
                     form['section1']['__conflict_idx__'].get_value())
        self.assertEqual(entry_idx[1], 2)
        last_entry = self.sheet_ts.df.loc[[entry_idx]]
        last_entry_dict = last_entry.to_dict('record')[0]
        self.assertEqual(last_entry_dict['Age'], entry['Age'])
        self.assertEqual(last_entry_dict['Participant_ID'], previous_pid)
        self.assertEqual(last_entry_dict['Phone_Number'],
                         entry['Phone_Number'])
        self.assertGreater(last_entry_dict['Timestamp_Submission'],
                           ts_before_submit)
        self.assertEqual(watched_entry[0].to_dict('record')[0]['Age'],
                         entry['Age'])

    def test_entry_update_from_plugin_action(self):

        entry_to_update = self.sheet_ts.df.iloc[1].name

        logger.debug('-------------------------')
        logger.debug('utest: create update form')
        form, alabel = self.sheet_ts.plugin.action(self.sheet_ts.df.iloc[[1]],
                                                   'Participant_ID')
        self.assertEqual(form['section1']['__submission__'].get_value(),
                         'append')
        self.assertNotEqual((form['section1']['__entry_id__'].get_value(),
                             form['section1']['__update_idx__'].get_value()),
                            entry_to_update)
        # Check that Participant_ID is frozen (not editable)
        self.assertFalse(form['section1']['Participant_ID'].editable)
        self.assertRaises(NotEditableError,
                          form['section1']['Participant_ID'].set_input_str,
                          'CE0000')

    def test_resolve_conflicting_entries_by_deletion(self):
        sheet_ts2 = DataSheet.from_files(self.user, self.filesystem.clone())

        form = self.sheet_ts.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 33})
        form.submit()

        form = sheet_ts2.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 44})
        form.submit()

        sheet_ts2.refresh_data()
        self.sheet_ts.refresh_data()

        logger.debug('utest: Fix conflict by deletion')

        to_delete = self.sheet_ts.df[self.sheet_ts.df.Age == 44].index[0]
        self.sheet_ts.delete_entry(to_delete)

        sheet_ts2.refresh_data()

        for sheet_name,sheet in [('ts', self.sheet_ts), ('ts2', sheet_ts2)]:
            logger.debug('Check that sheet %s has no more concurrent updates',
                         sheet_name)
            self.assertEqual(len(sheet.concurrent_updated_entries()), 0)
            self.assertEqual(sheet.df.loc[(1,1,0), 'Age'], 33)

    def test_conflicting_entries_on_load(self):
        sheet_ts2 = DataSheet.from_files(self.user, self.filesystem)

        form = self.sheet_ts.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 33})
        form.submit()

        form = sheet_ts2.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 44})
        form.submit()

        sheet_ts3 = DataSheet.from_files(self.user, self.filesystem)
        self.assertEqual(set(sheet_ts3.concurrent_updated_entries()),
                         {(1,1,1),(1,1,2)})

    def test_conflicting_entries_on_refresh(self):
        sheet_ts2 = DataSheet.from_files(self.user, self.filesystem.clone())

        form = self.sheet_ts.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 33})
        form.submit()

        form = sheet_ts2.form_update_entry((1,0,0))
        form.set_values_from_entry({'Age' : 44})
        form.submit()

        sheet_ts2.refresh_data()
        self.sheet_ts.refresh_data()

        self.assertEqual(set(sheet_ts2.concurrent_updated_entries()),
                         {(1,1,1),(1,1,2)})

        self.assertEqual(set(self.sheet_ts.concurrent_updated_entries()),
                         {(1,1,1),(1,1,2)})

    def test_form_entry_set(self):
        # Change the content of an entry
        # All values can change
        entry_idx_to_modify = self.sheet_ts.df.index[1]

        watched_entry = []
        def watch_entry(entry_idx):
            watched_entry.append(self.sheet_ts.df.loc[[entry_idx]])
        self.sheet_ts.notifier.add_watcher('entry_set', watch_entry)

        logger.debug('-------------------------')
        logger.debug('utest: create set form')
        form = self.sheet_ts.form_set_entry(entry_idx_to_modify)
        self.assertEqual(form['section1']['__submission__'].get_value(),
                         'set')
        self.assertEqual((form['section1']['__entry_id__'].get_value(),
                          form['section1']['__update_idx__'].get_value(),
                          form['section1']['__conflict_idx__'].get_value()),
                         entry_idx_to_modify)
        # Check that Participant_ID is frozen (not editable)
        self.assertTrue(form['section1']['Participant_ID'].editable)
        form['section1']['Participant_ID'].set_input_str('CE0000')
        # Update the entry
        logger.debug('-----------------')
        logger.debug('utest: fill form')
        entry = {'Age' : 77, 'Phone_Number' : '444'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))
        ts_before_submit = datetime.now()
        sleep(0.1)
        logger.debug('-----------------')
        logger.debug('utest: submit form')
        form.submit()
        self.assertEqual(len(watched_entry), 1)

        entry_idx = (form['section1']['__entry_id__'].get_value(),
                     form['section1']['__update_idx__'].get_value(),
                     form['section1']['__conflict_idx__'].get_value())
        self.assertEqual(entry_idx, entry_idx_to_modify)
        self.assertEqual(watched_entry[0].iloc[0]['Age'],
                         entry['Age'])

        self.assertEqual(watched_entry[0].loc[entry_idx_to_modify,
                                              'Participant_ID'],
                         'CE0000')
        self.assertEqual(watched_entry[0].loc[entry_idx_to_modify,
                                              'Phone_Number'],
                         entry['Phone_Number'])
        self.assertGreater(watched_entry[0].loc[entry_idx_to_modify,
                                                'Timestamp_Submission'],
                           ts_before_submit)

    def test_set_entry_file_update(self):

        entry_to_modify = self.sheet_ts.df.index[1]
        logger.debug('-------------------------')
        logger.debug('utest: create set form')
        logger.debug('utest: df before set:')
        logger.debug(self.sheet_ts.df)
        form = self.sheet_ts.form_set_entry(entry_to_modify)
        # Update the entry
        logger.debug('-----------------')
        logger.debug('utest: fill form')
        entry = {'Age' : 77, 'Phone_Number' : '444'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))

        sleep(0.1)
        form.submit()
        logger.debug('utest: df after set:')
        logger.debug(self.sheet_ts.df)

        self.sheet_ts.reload_all_data()

        logger.debug('utest: df after data reload:')
        logger.debug(self.sheet_ts.df)

        self.assertTrue(self.sheet_ts.df.index.is_unique)
        self.assertEqual(self.sheet_ts.df.loc[entry_to_modify, 'Age'], 77)


    def test_form_folder_removal(self):

        form_id = 1
        form = self.sheet_ts.form_new_entry(form_id=form_id)
        entry = {'Participant_ID' : 'CE0000', 'Age' : 43,
                 'Phone_Number' : '555'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))

        form_folder = self.sheet_ts.get_live_form_folder(form_id)
        fs = self.sheet_ts.filesystem
        self.assertTrue(fs.exists(form_folder))
        form.submit()
        self.assertFalse(fs.exists(form_folder))

    def test_form_folder_delayed_removal(self):
        class DataSheetFormHook(DataSheet):

            def rename_form_folder(self, form_folder):
                form_afolder = self.filesystem.full_path(form_folder)
                dummy_form_folder = op.join(op.dirname(form_afolder),
                                            'dummy')
                os.rename(form_afolder, form_afolder + '_dummy')

            def restore_form_folders(self):
                form_top_folder = self.get_live_forms_folder()
                for form_folder in self.filesystem.listdir(form_top_folder):
                    if form_folder.endswith('_dummy'):
                        form_folder = op.join(form_top_folder, form_folder)
                        form_afolder = self.filesystem.full_path(form_folder)
                        os.rename(form_afolder, form_afolder[:-len('_dummy')])

            def clean_live_form(self, form_id):
                self.rename_form_folder(self.get_live_form_folder(form_id))
                super(DataSheetFormHook, self).clean_live_form(form_id)

        sh1 = DataSheetFormHook(self.sheet_id,
                                Form.from_dict(self.form_def_ts_data),
                                self.data_df_ts_data,
                                self.user, self.filesystem)

        form_id = 1
        form = sh1.form_new_entry(form_id=form_id)
        entry = {'Participant_ID' : 'CE0000', 'Age' : 43,
                 'Phone_Number' : '555'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))
        form.submit()
        sh1.restore_form_folders()

        logger.debug('-------------------------------------------')
        logger.debug('utest: create new sheet, expect live form '\
                     'folder to be deleted')
        sh2 = DataSheet(self.sheet_id,
                        Form.from_dict(self.form_def_ts_data),
                        self.data_df_ts_data,
                        self.user, self.filesystem)
        self.assertFalse(sh2.filesystem.exists(sh2.get_live_form_folder(form_id)))

    def test_refresh_sheet(self):
        sheet_ts2 = DataSheet(self.sheet_id,
                              Form.from_dict(self.form_def_ts_data),
                              self.data_df_ts_data,
                              self.user, self.filesystem.change_dir('.'))
        form = self.sheet_ts.form_new_entry()
        entry = {'Participant_ID' : 'CE0000', 'Age' : 43,
                 'Phone_Number' : '555'}
        for k,v in entry.items():
            form['section1'][k].set_input_str(str(v))

        form.submit()
        entry_idx = (form['section1']['__entry_id__'].get_value(),
                     form['section1']['__update_idx__'].get_value(),
                     form['section1']['__conflict_idx__'].get_value())

        sheet_ts2.refresh_data()
        last_entry = sheet_ts2.df.loc[entry_idx]
        #last_entry_dict = last_entry.to_dict('record')[0]
        self.assertEqual(last_entry['Age'], entry['Age'])
        self.assertEqual(last_entry['Participant_ID'],
                         entry['Participant_ID'])
class UserData:

    def __init__(self, store_file='piccel.json'):
        store_dir = op.join(user_data_dir('piccel', 'lesca'))
        logger.info('User data folder: %s', store_dir)
        if not op.exists(store_dir):
            os.makedirs(store_dir)
        self.store_fn = op.join(store_dir, store_file)
        if op.exists(self.store_fn):
            with open(self.store_fn) as fin:
                self.store = json.load(fin)
        else:
            self.store = {}

        store_changed = False
        if 'recent_files' not in self.store:
            self.store['recent_files'] = {}
            store_changed = True
        else:
            fixed_list = [fn for fn in self.store['recent_files'] \
                          if op.exists(fn)]
            if len(fixed_list) != len(self.store['recent_files']):
                # TODO : utest
                logger.debug('Purge non-existent entries in recent files')
                logger.debug('Previous recent files:\n %s',
                             '\n'.join(self.store['recent_files'].keys()))
                logger.debug('New recent files:\n %s', '\n'.join(fixed_list))
                self.store['recent_files'] = {fn:self.store['recent_files'][fn]\
                                              for fn in fixed_list}
                store_changed = True

        if store_changed:
            self.save()

        logger.debug('Loaded user data: %s', self.store)

    def clear(self):
        self.store = {}
        self.save()

    def get_recent_files(self):
        # recent_files: {fn : last_access_timestamp}
        sorted_fns = sorted(self.store['recent_files'].items(),
                           key=lambda e: e[1])
        return [fn for fn, ts in sorted_fns][::-1]

    def record_recent_file(self, fn):
        if not op.exists(fn):
            logger.error('File %s does not exist. It will not be saved '\
                         'in recent files' % fn)
        else:
            ts = datetime.now().timestamp()
            self.store['recent_files'][fn] = ts
            self.save()

    def get_last_user(self):
        return self.store.get('last_user', None)

    def set_last_user(self, user):
        self.store['last_user'] = user
        self.save()

    def save(self):
        with open(self.store_fn, 'w') as fout:
            json.dump(self.store, fout)

class TestUserData(unittest.TestCase):

    def setUp(self):
        self.store_fn = 'sheeter_utest.json'
        self.udata = UserData(self.store_fn)
        self.tmp_dir = tempfile.mkdtemp()

    def tearDown(self):
        self.udata.clear()
        shutil.rmtree(self.tmp_dir)

    def touch_fn(self, bfn):
        fn = op.join(self.tmp_dir, bfn)
        with open(fn, 'w') as fin:
            fin.write('')
        return fn

    def test_recent_files_order(self):
        self.assertEqual(self.udata.get_recent_files(), [])
        self.udata.record_recent_file(self.touch_fn('f1.ext'))
        self.udata.record_recent_file(self.touch_fn('f2.ext'))
        self.udata.record_recent_file(self.touch_fn('f1.ext'))
        self.assertEqual(self.udata.get_recent_files(),
                         [op.join(self.tmp_dir, f) for f in ['f1.ext', 'f2.ext']])

    def test_persistence(self):
        self.udata.record_recent_file(self.touch_fn('f1.ext'))
        udata2 = UserData(self.store_fn)
        self.assertEqual(udata2.get_recent_files(),
                         [op.join(self.tmp_dir, 'f1.ext')])

class ConfigurationNotLoaded(Exception): pass

class PiccelLogic:
    """
    State: workbook selector
        * get_recent_files
        - load -> Decrypt
    State: Decrypt
        - decrypt workbook -> Login
    State: Login
        * get_users (name, role, password_check)
        - on_login_fail -> Login
        - on_login_ok -> workbook edition
        - on_cancel -> workbook selector
    State: Workbook edition
        * get_workbook()
        - on_close -> workbook selector
    """
    STATE_SELECTOR = 0
    STATE_ACCESS = 1
    STATE_LOGIN = 2
    STATE_WORKBOOK = 3

    STATES = ['selector', 'access', 'login', 'workbook']

    CFG_FILE_EXT = '.psh'

    def __init__(self, system_data):
        self.state = PiccelLogic.STATE_SELECTOR
        self.system_data = system_data
        self.workbook = None

    def get_recent_files(self):
        return self.system_data.get_recent_files()

    def load_configuration(self, filesystem, cfg_fn):
        message = 'ok'
        try:
            self.workbook = WorkBook.from_configuration_file(cfg_fn, filesystem)
            f_cfg_fn = filesystem.full_path(cfg_fn)
            self.system_data.record_recent_file(f_cfg_fn)
            self.state = PiccelLogic.STATE_ACCESS
        except Exception as e:
            logger.error('Error loading file %s: %s', cfg_fn, e)
            message = 'Error loading file %s' % cfg_fn
            self.state = PiccelLogic.STATE_SELECTOR
            # from IPython import embed; embed()
        return message

    def decrypt(self, access_pwd):
        message = 'ok'
        try:
            self.workbook.decrypt(access_pwd)
            self.state = PiccelLogic.STATE_LOGIN
        except Exception as e:
            logger.error('Error decrypting workbook %s: %s',
                         self.workbook.label, e)
            message = 'Decryption error'
            self.state = PiccelLogic.STATE_SELECTOR
        return message

    def get_user_names(self):
        last_user = self.system_data.get_last_user()
        users = self.workbook.get_users()
        if last_user is not None and last_user in users:
            last_user = [last_user]
        else:
            last_user = []
        return last_user + [u for u in users if len(last_user)==0 or \
                            u != last_user[0]]

    def check_access_password(self, password_str):
        return self.workbook.access_password_is_valid(password_str)

    def check_role_password(self, user, password_str):
        role = self.workbook.user_roles[user]
        return self.workbook.role_password_is_valid(role, password_str)

    def cancel_access(self):
        self.cancel_login()

    def cancel_login(self):
        self.filesystem = None
        self.cfg = None
        self.workbook = None
        self.state = PiccelLogic.STATE_SELECTOR

    def login(self, user, role_pwd=None, progression_callback=None):
        """
        Create encrypter using given access password.
        Load workbook using given user.
        """

        self.workbook.user_login(user, role_pwd)

        logger.debug('Record that last user is %s', user)
        self.system_data.set_last_user(user)

        if progression_callback is not None:
            progression_callback(1)

        self.state = PiccelLogic.STATE_WORKBOOK

    def close_workbook(self):
        assert(self.state == PiccelLogic.STATE_WORKBOOK)
        self.encrypter = None
        self.state = PiccelLogic.STATE_LOGIN
        self.cancel_login()

class TestPiccelLogic(unittest.TestCase):

    def setUp(self):
        self.udata = UserData('sheeter_utest.json')
        self.tmp_dir = tempfile.mkdtemp()
        filesystem = LocalFileSystem(self.tmp_dir)
        workbook = WorkBook('Test WB', 'wb_data', filesystem)
        self.cfg_fn = 'wb.psh'
        workbook.save_configuration_file(self.cfg_fn)
        self.access_pwd = '1234'
        self.editor_pwd = 'FVEZ'
        self.admin_pwd = '5425'
        self.manager_pwd = 'a542fezf5'

        workbook.set_access_password(self.access_pwd)
        workbook.decrypt(self.access_pwd)
        workbook.set_password(UserRole.EDITOR, self.editor_pwd)
        workbook.set_password(UserRole.ADMIN, self.admin_pwd)
        workbook.set_password(UserRole.MANAGER, self.manager_pwd)
        workbook.set_users({
            'thomas' : UserRole.ADMIN,
            'simon' : UserRole.EDITOR,
            'catherine' : UserRole.MANAGER,
            'guest' : UserRole.VIEWER,
        })

    def tearDown(self):
        self.udata.clear()
        shutil.rmtree(self.tmp_dir)

    def test_selector(self):
        sheeter = PiccelLogic(self.udata)
        self.assertEqual(sheeter.state, sheeter.STATE_SELECTOR)
        self.assertEqual(sheeter.get_recent_files(), [])
        filesystem = LocalFileSystem(self.tmp_dir)
        msg = sheeter.load_configuration(filesystem, self.cfg_fn)
        self.assertEqual(msg, 'ok')
        self.assertEqual(sheeter.state, sheeter.STATE_ACCESS)

    def test_decrypt(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        msg = logic.decrypt(self.access_pwd)
        self.assertEqual(msg, 'ok')
        self.assertEqual(logic.state, logic.STATE_LOGIN)

    def test_login_unknown_user(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        logic.decrypt(self.access_pwd)
        self.assertRaises(UnknownUser, logic.login, 'chouchou', 'bobie')

    def test_login_invalid_password(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        logic.decrypt(self.access_pwd)
        self.assertRaises(InvalidPassword, logic.login, 'thomas', 'nope')
        self.assertRaises(InvalidPassword, logic.login, 'thomas',
                          self.access_pwd, 'nope')

    def test_check_passwords(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        self.assertTrue(logic.check_access_password(self.access_pwd))
        logic.decrypt(self.access_pwd)
        self.assertTrue(logic.check_role_password('thomas', self.admin_pwd))
        self.assertTrue(logic.check_role_password('simon', self.editor_pwd))
        self.assertTrue(logic.check_role_password('guest', self.access_pwd))
        self.assertTrue(logic.check_role_password('catherine', self.manager_pwd))

        self.assertFalse(logic.check_role_password('thomas', 'nope'))
        self.assertFalse(logic.check_role_password('simon', 'nope'))
        self.assertFalse(logic.check_role_password('catherine', 'nope'))
        self.assertFalse(logic.check_role_password('guest', 'nope'))

    def test_last_user_first(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        logic.decrypt(self.access_pwd)
        logic.login('simon', self.editor_pwd)

        filesystem.unset_encrypter()
        logic2 = PiccelLogic(self.udata)
        logic2.load_configuration(filesystem, self.cfg_fn)
        logic2.decrypt(self.access_pwd)
        self.assertEqual(logic2.get_user_names()[0], 'simon')

    def test_correct_login(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_fn)
        logic.decrypt(self.access_pwd)
        logic.login('thomas', self.admin_pwd)
        logic.login('simon', self.editor_pwd)
        logic.login('guest')
        self.assertIsNotNone(logic.workbook)
        self.assertEqual(logic.state, PiccelLogic.STATE_WORKBOOK)

        # Check:
        #     - user-specific log file exists -> this has to be explicitely enabled
        #     - workbook is loaded

class WorkBookFileError(Exception): pass
class SheetLabelAlreadyUsed(Exception): pass
class SheetDataOverwriteError(Exception): pass
class UnauthorizedRole(Exception): pass
class InconsistentRoles(Exception): pass
class PasswordChangeError(Exception): pass
class NoAccessPasswordError(Exception): pass
class NoRolePasswordError(Exception): pass
class EncryptionError(Exception): pass

class check_role(object):
    def __init__(self, role):
        self.role = role

    def __call__(self, func, *args, **kwargs):
        def _check(*args, **kwargs):
            if args[0].user_role is None:
                raise UndefinedUser('User not associated with sheet %s. '
                                    'Cannot call role-protected method %s.' % \
                                    (args[0].label, func.__name__))
            if args[0].user_role.value < self.role.value:
                raise UnauthorizedRole('User %s has role %s but '\
                                       '%s requires at least' % \
                                       (args[0].user, args[0].user_role,
                                        self.role))
            else:
                return func(*args, **kwargs)
        return _check

class AnyMatch:
    def __init__(self):
        pass
    def match(*args, **kwargs):
        return True

def combine_regexps(regexp_strs):
    return '|'.join('(?:%s)' % r for r in regexp_strs)

class WorkBook:
    """
    Workflow:
    - load workbook
    - decryption using access password (self.decrypted is True)
    - login user with role-specific password (self.user is not None)
    """
    ACCESS_KEY = 'data_access'
    SHEET_FOLDER = 'sheets'
    ENCRYPTION_FN = 'encryption.json'

    def __init__(self, label, data_folder, filesystem, password_vault=None,
                 linked_book_fns=None):
        """
        Create workbook from basic configuration: where is the main data folder
        and password checksums for every role.
        The list of users will be loaded when the woorkbook is decrypted using
        the access password. Data will be loaded when user logs in.

        A workbook can be created from scratch:
        wb = WorkBook('my_wb', 'data_path_relative_to_root ',
                      LocalFileSystem('path_to_root'))
        # TODO helper with more natural path definition:
        wb = WorkBook.create('my_wb', 'data_path', 'cfg_fn')
        # Set access password (saved to data_path/encryption.json):
        wb.set_access_password('access_pwd')

        # Add user with role:
        wb.set_users({'me': UserRole.ADMIN,
                      'guest': UserRole.VIEWER,
                      'friend', UserRole.EDITOR})
        # Set password for given role (saved to data_path/encryption.json):
        wb.set_password(UserRole.ADMIN, 'admin_pwd')
        wb.save_configuration_file('../my_wb.psh')
        """
        self.label = label
        self.filesystem = filesystem
        if self.filesystem.encrypter is not None:
            logger.warning('Init of workbook %s: Encrypter already associated '\
                           'with filesystem but will be redefined after login',
                           label)
        if not filesystem.exists(data_folder):
            logger.info('WorkBook %s: Data folder %s not found, create it',
                        self.label, data_folder)
            filesystem.makedirs(data_folder)

        self.has_write_access = filesystem.test_write_access()

        sheet_folder = op.join(data_folder, WorkBook.SHEET_FOLDER)
        if not filesystem.exists(sheet_folder):
            logger.info('WorkBook %s: Create sheet subfolder', self.label)
            filesystem.makedirs(sheet_folder)

        if password_vault is None:
            logger.info('WorkBook %s: Create password vault', self.label)
            pwd_rfn = op.join(data_folder, WorkBook.ENCRYPTION_FN)
            pwd_fn = self.filesystem.full_path(pwd_rfn)
            password_vault = PasswordVault.from_file(pwd_fn)
            logger.info('WorkBook %s: Save password vault to %s',
                        self.label, pwd_fn)
            password_vault.save()
        self.password_vault = password_vault
        self.user = None
        self.user_role = None
        self.user_roles = None

        self.data_folder = data_folder
        self.linked_book_fns = (linked_book_fns if linked_book_fns is not None \
                                else {})
        # TODO: user role retrieval can only be done while decrypting!
        self.linked_books = []
        # TODO: utest linked workbook!
        for linked_workbook_fn in self.linked_book_fns.keys():
            self.preload_linked_workbook(linked_workbook_fn)
            # TODO: warning: prevent circular linkage!

        logger.debug('WorkBook %s init: root folder: %s',
                     self.label, self.filesystem.root_folder)
        logger.debug('WorkBook %s init: data folder: %s',
                     self.label, self.data_folder)
        logger.debug('WorkBook %s init: encryption file: %s',
                     self.label, self.password_vault.pwd_fn)

        self.sheets = {}
        self.decrypted = False
        self.logged_in = False

    def add_linked_workbook(self, cfg_fn, sheet_filters):
        self.linked_book_fns[cfg_fn] = sheet_filters
        self.preload_linked_workbook(cfg_fn)

    def preload_linked_workbook(self, linked_workbook_fn):
        logger.info('Workbook %s: Preload linked workbook %s',
                    self.label, linked_workbook_fn)
        sheet_filters = self.linked_book_fns[linked_workbook_fn]
        linked_wb = WorkBook.from_configuration_file(linked_workbook_fn,
                                                     self.filesystem)
        self.linked_books.append((linked_wb, combine_regexps(sheet_filters)))

    def __getitem__(self, sheet_label):
        assert(self.logged_in)
        if sheet_label not in self.sheets:
            logger.error('WorkBook %s: cannot find sheet %s in %s',
                         self.label, sheet_label, ', '.join(self.sheets))
        return self.sheets[sheet_label]

    def has_sheet(self, sheet_label):
        return sheet_label in self.sheets

    def save_configuration_file(self, workbook_fn):
        cfg = {
            'workbook_label' : self.label,
            'data_folder' : self.data_folder,
            'linked_sheets' : self.linked_book_fns
            }
        # TODO use normpath when actually reading/writing files/folders!
        logger.debug('Write WorkBook configuration file to %s', workbook_fn)
        self.filesystem.save(workbook_fn, json.dumps(cfg), overwrite=True,
                             crypt=False)

    @staticmethod
    def from_configuration_file(workbook_fn, filesystem=None):
        """
        workbook_file is a json file:
        {
        'workbook_label' : 'Workbook Title',
        'data_folder' : 'path_to_wb_folder',
        'linked_sheets' : {
            'path_to_other_workbook' : 'sheet_label_regexp'
            }
        }
        Decryption pwd is not entered and user is not logged in at this point
        """
        if filesystem is None:
            filesystem = LocalFileSystem(op.dirname(workbook_fn))
            workbook_fn = op.basename(workbook_fn)
        cfg = json.loads(filesystem.load(workbook_fn))
        wb_cfg_folder = op.normpath(op.dirname(workbook_fn))
        filesystem = filesystem.change_dir(wb_cfg_folder)
        if filesystem.exists(cfg['data_folder']):
            crypt_cfg_rel_fn = op.join(cfg['data_folder'],
                                       WorkBook.ENCRYPTION_FN)
            crypt_cfg_full_fn = filesystem.full_path(crypt_cfg_rel_fn)
            # TODO: PasswordVauld should work from file system, not full path
            password_vault = PasswordVault.from_file(crypt_cfg_full_fn)
        else:
            logger.warning('WorkBook %s: Data folder %s in %s does not exists. '\
                           'Create it', cfg['workbook_label'],
                           cfg['data_folder'], filesystem.root_folder)
            filesystem.makedirs(cfg['data_folder'])
            password_vault = None

        return WorkBook(cfg['workbook_label'], cfg['data_folder'],
                        filesystem, password_vault=password_vault,
                        linked_book_fns=cfg['linked_sheets'])

    def set_password(self, role, pwd, old_pwd=''):
        assert(role in UserRole)
        logger.debug('Set password for role %s', role.name)
        self.password_vault.set_password(role.name, pwd, old_pwd)
        self.password_vault.save()

    def set_access_password(self, pwd):
        if self.password_vault.has_password_key(WorkBook.ACCESS_KEY):
            raise PasswordChangeError('Cannot overwrite existing encryption key')
        logger.debug('Set data access password')
        self.password_vault.set_password(WorkBook.ACCESS_KEY, pwd)
        logger.debug('Set VIEWER role password = data access password')
        self.password_vault.set_password(UserRole.VIEWER.name, pwd)
        self.password_vault.save()

    def decrypt(self, access_pwd, key_afn=None):
        """
        Load user list and resolve linked books
        Must be called before user login.
        """
        # TODO improve API with key input
        if key_afn is None:
            if not self.access_password_is_valid(access_pwd):
                logger.error('Invalid password for data access')
                raise InvalidPassword('Data access')
            logger.info('WorkBook %s: decrypt', self.label)
            encrypter = self.password_vault.get_encrypter(WorkBook.ACCESS_KEY,
                                                          access_pwd)
        else:
            with open(key_afn, 'r') as fin:
                key = fin.read()
            encrypter = self.password_vault.get_encrypter(None, None, key)
        self.filesystem.set_encrypter(encrypter)
        self.decrypted = True

        users_fn = op.join(self.data_folder, 'users.json')
        if not self.filesystem.exists(users_fn):
            self.filesystem.save(users_fn, json.dumps({}))

        self.user_roles = self._load_user_roles()
        logger.info('WorkBook %s: Loaded users:\n %s', self.label,
                     pformat(self.user_roles))

        for linked_wb, sheet_filter in self.linked_books:
            linked_wb.decrypt(access_pwd)
            linked_user_roles = linked_wb._load_user_roles()
            for user, role in self.user_roles.copy().items():
                if user in linked_user_roles:
                    if linked_user_roles[user] > role:
                        logger.info('Use higher role %s from linked workbook %s'\
                                    'instead of role %s for user %s',
                                    linked_user_roles[user],
                                    linked_wb.label, role, user)
                        self.user_roles[user] = linked_user_roles[user]
                else:
                    raise UnknownUser('%s in %s', linked_wb.label)
        return True


    def dump_access_key(self, key_afn):
        assert(self.decrypted)
        with open(key_afn, 'w') as fout:
            fout.write(self.filesystem.encrypter.get_key())

    def _load_user_roles(self):
        assert(self.decrypted)
        users_fn = op.join(self.data_folder, 'users.json')
        logger.info('WorkBook %s: Load users from %s',
                    self.label, users_fn)
        user_roles = json.loads(self.filesystem.load(users_fn))
        for role in set(user_roles.values()):
            if not self.password_vault.has_password_key(role):
                logger.warning('No password set for role %s.' % role)
        return {u:UserRole[r] for u,r in user_roles.items()}

    def refresh_all_data(self):
        logger.debug2('Workbook %s: Refresh data', self.label)
        for sheet in self.sheets.values():
            sheet.refresh_data()

    def set_user(self, user, role):
        if not self.decrypted:
            raise EncryptionError()
        assert(isinstance(role, UserRole))
        if not self.password_vault.has_password_key(role.name):
            raise NoRolePasswordError(role)

        self.user_roles[user] = role
        self.save_user_roles()

    def get_users(self):
        assert(self.decrypted)
        return self.user_roles.keys()

    def get_user_role(self, user):
        assert(self.decrypted)
        return self.user_roles[user]

    def set_users(self, user_roles):
        for u,r in user_roles.items():
            assert(isinstance(r, UserRole))
        self.user_roles.update(user_roles)
        self.save_user_roles()

    def save_user_roles(self):
        if not self.decrypted:
            raise EncryptionError()

        users_fn = op.join(self.data_folder, 'users.json')
        logger.info('Save user file to %s', users_fn)
        to_dump = {u:r.name for u,r in self.user_roles.items()}
        self.filesystem.save(users_fn, json.dumps(to_dump), overwrite=True)

    def access_password_is_valid(self, pwd):
        try:
            return self.password_vault.password_is_valid(WorkBook.ACCESS_KEY, pwd)
        except UnknownUser:
            raise NoAccessPasswordError()

    def role_password_is_valid(self, role, pwd):
        assert(role in UserRole)
        return self.password_vault.password_is_valid(role.name, pwd)

    def user_login(self, user, pwd, progress_callback=None, load_sheets=True):
        """
        Note: The role password only protects access to certain methods of the
        WorkBook class.
        If a user has write access to the workbook files and has the data access
        password, then they can modify workbook files as they want.
        There is no mechanism that strictly protects admin operations.

        Write access must be handled by the file system.
        """
        # TODO: check role according to self.user_roles
        assert(self.decrypted)
        self.user = user
        try:
            self.user_role = self.user_roles[user]
        except KeyError:
            logger.error('Unknown user %s while login in %s', user, self.label)
            raise UnknownUser(user)
        logger.info('Logging as user %s with role %s', user, self.user_role)
        if self.user_role!= UserRole.VIEWER and \
           not self.password_vault.password_is_valid(self.user_role.name, pwd):
            logger.error('Invalid password for role %s' % self.user_role.name)
            raise InvalidPassword('role %s' % self.user_role.name)

        for linked_book, sheet_filter in self.linked_books:
            linked_book.user_login(user, pwd, load_sheets=load_sheets)

        self.logged_in = True

        if load_sheets:
            self.reload(progress_callback)

    def get_sheet(self, sheet_label):
        assert(self.logged_in)
        return self.sheets[sheet_label]

    def get_nb_sheets(self, sheet_re):
        if isinstance(sheet_re, str):
            sheet_re = re.compile(sheet_re)
        sheet_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER)
        return sum(1 for sh in self.filesystem.listdir(sheet_folder) \
                   if sheet_re.match(sh))

    def dump_default_plugin(self, plugin_fn, plugin_code=None):
        logger.debug('Dump default workbook plugin')
        if plugin_code is None:
            plugin_code = inspect.getsource(workbook_plugin_template)
        self.filesystem.save(plugin_fn, plugin_code, overwrite=True)

    def reload(self, progress_callback=None):
        if not self.decrypted:
            logger.error('WorkBook %s: decryption not setup, cannot reload.')
            return

        if self.user is None:
            logger.error('WorkBook %s: user not logged in, cannot reload.')
            return

        plugin_fn = op.join(self.data_folder, 'plugin_common.py')
        if not self.filesystem.exists(plugin_fn):
            logger.info('WorkBook %s: plugin file "%s" does not exist. '\
                        'Dump default one', self.label, plugin_fn)
            self.dump_default_plugin(plugin_fn)
        self.load_plugin()

        # TODO: sort out sheet filtering
        # Get number of element to load:
        if progress_callback is not None:
            progression = 1
            progress_total = self.get_nb_sheets() + \
                sum(lwb.get_nb_sheets(sh_regexp) \
                    for lwb,sh_regexp in self.linked_books)
            progress_increment = 100/progress_total
            logger.debug('WorkBook %s: progress goal: %d, increment: %f',
                         self.label, progress_total, progress_increment)

        # ASSUME all sheet labels are unique
        self.sheets = self.load_sheets(parent_workbook=self)
        logger.debug('WorkBook %s: Load linked workbooks: %s',
                     self.label, ','.join('"%s"'%l for l,b in self.linked_books))
        for linked_book, sheet_regexp in self.linked_books:
            self.sheets.update(linked_book.load_sheets(sheet_regexp,
                                                       progress_callback,
                                                       parent_workbook=self))
        self.after_workbook_load()

    def after_workbook_load(self):
        logger.debug('Workbook %s: call after_workbook_load on all sheets',
                     self.label)
        # for sheet in self.sheets.values():
        #     sheet.plugin.check()

        for sheet in self.sheets.values():
            sheet.after_workbook_load()

    def load_plugin(self):
        plugin_module = 'plugin_common'
        plugin_fn = op.join(self.data_folder, '%s.py' % plugin_module)
        tmp_folder = op.dirname(self.filesystem.copy_to_tmp(plugin_fn,
                                                            decrypt=True))
        logger.debug('Workbook %s: load plugin', self.label)
        sys.path.insert(0, tmp_folder)
        plugin_module = import_module(plugin_module)
        reload_module(plugin_module)
        self.plugin = plugin_module.CustomWorkBookPlugin(self)
        sys.path.pop(0)

    def load_sheets(self, sheet_regexp=None, progress_callback=None,
                    parent_workbook=None):
        # TODO. improve progress callback to avoid handling logic of increment
        if progress_callback is not None:
            progression = 0
            progress_total = self.get_nb_sheets()
            progress_increment = 100/progress_total
            logger.debug('WorkBook %s: progress goal: %d, increment: %f',
                         self.label, progress_total, progress_increment)
        if self.filesystem.encrypter is None:
            logger.error('WorkBook %s: decryption not setup, cannot reload.')
            return
        if self.user is None:
            logger.error('WorkBook %s: user not logged in, cannot reload.')
            return

        if isinstance(sheet_regexp, str):
            sheet_regexp = re.compile(sheet_regexp)
        elif sheet_regexp is None:
            sheet_regexp = AnyMatch()

        sheet_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER)
        logger.info('WorkBook %s: Load sheets from %s',
                    self.label, sheet_folder)
        sheets = {}

        sheet_list = self.plugin.sheet_order()
        logger.info('WorkBook %s: sheets order from common plugin: %s',
                     self.label, sheet_list)

        sheet_folders = self.filesystem.listdir(sheet_folder,
                                                list_folders_only=True)

        unknown_sheets = set(sheet_list).difference(sheet_folders)
        if len(unknown_sheets) > 0:
            logger.warning('WorkBook %s: Unknown sheets specified in '\
                           'common plugin: %s' \
                           %(self.label, ', '.join(unknown_sheets)))

        for sheet_label in sheet_folders:
            if sheet_label not in sheet_list:
                sheet_list.append(sheet_label)

        logger.debug('WorkBook %s: sheets to load from files: %s',
                     self.label, sheet_list)
        for sheet_label in sheet_list:
            if not self.filesystem.exists(op.join(sheet_folder,
                                                  sheet_label)):
                logger.warning('WorkBook %s: Skip loading sheet %s '\
                               '(no folder dfound)' %(self.label, sheet_label))
                continue
            if sheet_regexp.match(sheet_label) is not None:
                logger.info('WorkBook %s: Reload data sheet %s' % \
                            (self.label, sheet_label))
                # TODO: specify role here?
                sh_fs = self.filesystem.change_dir(op.join(sheet_folder,
                                                           sheet_label))

                sh = DataSheet.from_files(self.user, sh_fs,
                                          workbook=parent_workbook)
                sheets[sheet_label] = sh
                if progress_callback is not None:
                    progression += progress_increment
                    progress_callback(int(progression))
            else:
                logger.debug('WorkBook %s: sheet %s not loaded (filtered)' % \
                             (self.label, sheet_label))
            if progress_callback is not None:
                progress_callback(100)

        return sheets

    def __eq__(self, other):
        return isinstance(other, WorkBook) and self.label==other.label and\
            self.user_roles == other.user_roles and \
            self.password_vault == other.password_vault and \
            self.data_folder == other.data_folder and \
            self.linked_book_fns == other.linked_book_fns and \
            self.sheets == other.sheets

    @check_role(UserRole.ADMIN)
    def add_sheet(self, sheet, overwrite_data=False, overwrite_form=False):
        assert(self.filesystem.encrypter is not None)
        if sheet.label in self.sheets:
            raise SheetLabelAlreadyUsed(sheet.label)

        sheet_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER,
                               sheet.label)
        if self.filesystem.exists(sheet_folder) and not overwrite_data:
            raise SheetDataOverwriteError('Cannot add sheet %s (folder already '\
                                          'exists)' % sheet.label)

        if not self.filesystem.exists(sheet_folder):
            self.filesystem.makedirs(sheet_folder)
        sheet.set_filesystem(self.filesystem.change_dir(sheet_folder))
        sheet.save()

        sheet.set_workbook(self)
        self.sheets[sheet.label] = sheet

    @check_role(UserRole.EDITOR)
    def save_sheet_entry(self, sheet_label, entry_df):
        assert(self.encrypter is not None)
        data_fn = self.get_data_fn(sheet_label)
        sheet = self.sheets[sheet_label]
        df_content_str = self.encrypter.encrypt_str(sheet.df_to_str(entry_df))
        logger.info('Save entry of sheet %s to %s' % \
                    (sheet_label, data_fn))
        self.filesystem.save(data_fn, df_content_str)
        return data_fn

    @check_role(UserRole.EDITOR)
    def new_live_form(self, sheet_label, form_id=None, entry_dict=None,
                      watchers=None):
        sheet = self.sheets[sheet_label]

        if form_id is None:
            form_id = uuid4().hex
            form_folder = self.get_live_form_folder(sheet_label, form_id)
            self.filesystem.makedirs(form_folder)
        else:
            form_id = form_id
            form_folder = self.get_live_form_folder(sheet_label, form_id)
            assert(self.filesystem.exists(form_folder))

        form = sheet.new_live_form(entry_dict=entry_dict, watchers=watchers)
        logger.debug('Make form input callback for form %s', form_id)
        form_callback = LazyFunc(self.save_live_form_input, form_id=form_id)
        form.set_input_callback(form_callback)
        self.live_forms_by_sheet[sheet_label][form_id] = form
        self.live_forms_by_id[form_id] = form
        return form, form_id

    def get_live_form(self, form_id):
        # TODO: check that live form folder actually exists?
        # because it may have been submitted concurrently
        # Should not happen though if there is a user lock
        return self.live_forms_by_id[form_id]

    def live_forms(self, sheet_label):
        return self.live_forms_by_sheet[sheet_label].items()

    def live_form_is_empty(self, sheet_label, form_id):
        form_folder = self.get_live_form_folder(sheet_label, form_id)
        return self.filesystem.dir_is_empty(form_folder)

class TestWorkBook(unittest.TestCase):

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp()
        logger.setLevel(logging.DEBUG)
        self.access_pwd = '1234'
        self.admin_pwd = '5425'
        self.editor_pwd = '0R43'

    def tearDown(self):
        shutil.rmtree(self.tmp_dir)

    def test_combine_regexp(self):
        re1 = '.*A'
        re2 = 'B.*'
        re3 = 'jo.n'
        regexp = re.compile(combine_regexps([re1, re2, re3]))
        self.assertIsNotNone(regexp.match('cocoA'))
        self.assertIsNotNone(regexp.match('Booh'))
        self.assertIsNotNone(regexp.match('john'))
        self.assertIsNone(regexp.match('doe'))

    def test_write_access(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        self.assertTrue(wb.has_write_access)

    def test_load_with_unknown_files(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        user = 'TV'

        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')

        wb = WorkBook(wb_id, data_folder, fs)
        wb.set_access_password(self.access_pwd)
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        wb.set_password(UserRole.EDITOR, self.editor_pwd)
        cfg_bfn = 'wb.psh'
        wb.save_configuration_file(cfg_bfn)

        wb.decrypt(self.access_pwd)
        wb.set_user(user, UserRole.ADMIN)
        wb.user_login(user, self.admin_pwd)

        sheet_id = 'Participant_info'
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'}),
                 FormItem(keys={'Age':None},
                          vtype='int', supported_languages={'French'},
                          default_language='French'),
                 FormItem(keys={'Timestamp':None},
                          vtype='datetime', generator='timestamp_creation',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Titre de formulaire'})
        sh1 = DataSheet(sheet_id, form, user=user)
        sh1.set_default_view('latest')
        # Add sheet to workbook (auto save)
        logger.debug('utest: add sheet1 to workbook1')
        wb.add_sheet(sh1) # note: this is an admin feature

        sh1.add_new_entry({'Participant_ID' : 'CE9999', 'Age' : 43,
                           'Timestamp' : datetime(2021, 4, 16, 17, 28)})

        fs.save(op.join(wb.data_folder, 'dummy_file'))
        fs.makedirs(op.join(wb.data_folder, 'dummy_folder'))
        fs.save(op.join(wb.data_folder, 'dummy_folder','dummy_file'))
        fs.save(op.join(wb.data_folder, 'sheets', 'dummy_file'))
        fs.save(op.join(wb.data_folder, 'sheets', sheet_id, 'dummy_file'))
        fs.save(op.join(wb.data_folder, 'sheets', sheet_id, 'data', 'dummy_file'),
                'dummy data content')
        fs.makedirs(op.join(wb.data_folder, 'sheets', sheet_id, 'live_forms',
                            'dummy_form_folder'))
        fs.save(op.join(wb.data_folder, 'sheets', sheet_id, 'live_forms',
                        'dummy_form_folder', 'dummy_file'), 'dummy form content')

        logger.debug('-----------------------')
        logger.debug('utest: create workbook2')

        # TODO: ignore sheet subfolder that do not contain proper sheet data
        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)
        self.assertEqual(wb, wb2)

    def test_set_access_password(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        access_pwd = '1245'
        self.assertRaises(NoAccessPasswordError, wb.access_password_is_valid,
                          access_pwd)
        wb.set_access_password(access_pwd)
        self.assertTrue(wb.access_password_is_valid(access_pwd))
        self.assertFalse(wb.access_password_is_valid('154Y76'))

    def test_set_user(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        access_pwd = '1245'
        self.assertRaises(EncryptionError, wb.set_user, 'me', UserRole.ADMIN)
        wb.set_access_password(access_pwd)
        wb.decrypt(access_pwd)
        self.assertRaises(NoRolePasswordError, wb.set_user, 'me',
                          UserRole.ADMIN)
        admin_pwd = '12T64'
        wb.set_password(UserRole.ADMIN, admin_pwd)
        wb.set_user('me', UserRole.ADMIN)

    def test_create_empty_workbook(self):
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        user_roles = {user : UserRole.ADMIN}
        data_folder = 'pinfo_files'
        wb1 = WorkBook(wb_id, data_folder, fs)

        # Assert that stem folders are created
        self.assertTrue(fs.exists(data_folder))
        self.assertTrue(fs.exists(op.join(data_folder, 'sheets')))

        encryption = json.loads(fs.load(op.join(data_folder,
                                                WorkBook.ENCRYPTION_FN)))
        self.assertTrue(len(encryption['salt_hex']) > 0)

    def test_load_save_configuration_file(self):
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        self.user_roles = {user : UserRole.ADMIN}
        data_folder = 'pinfo_files'
        wb1 = WorkBook(wb_id, data_folder, fs)
        cfg_fn = 'wb.psh'
        wb1.save_configuration_file(cfg_fn)
        self.assertEqual(wb1, WorkBook.from_configuration_file(cfg_fn, fs))

    def test_decrypt_from_key_file(self):
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')
        wb_id = 'Participant_info'
        user = 'me'
        user_roles = {user : UserRole.ADMIN}
        data_folder = 'pinfo_files'
        wb1 = WorkBook(wb_id, data_folder, fs)
        wb1.set_access_password(self.access_pwd)
        wb1.set_password(UserRole.ADMIN, self.admin_pwd)
        wb1.set_password(UserRole.EDITOR, self.editor_pwd)

        wb1.decrypt(self.access_pwd)

        key_fn = op.join(self.tmp_dir, 'key')
        logger.debug('utest: dump key from workbook1')
        wb1.dump_access_key(key_fn)

        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')

        wb2 = WorkBook(wb_id, data_folder, fs)
        wb2.decrypt(None, key_afn=key_fn)

        self.assertEqual(wb1, wb2)

    def test_data_persistence(self):

        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')
        wb_id = 'Participant_info'
        user = 'me'
        user_roles = {user : UserRole.ADMIN}
        data_folder = 'pinfo_files'
        wb1 = WorkBook(wb_id, data_folder, fs)

        wb1.set_access_password(self.access_pwd)
        wb1.set_password(UserRole.ADMIN, self.admin_pwd)
        wb1.set_password(UserRole.EDITOR, self.editor_pwd)

        wb1.decrypt(self.access_pwd)
        wb1.set_user(user, UserRole.ADMIN)
        wb1.user_login(user, self.admin_pwd)

        # Create a sheet with data
        sheet_id = 'Participant_info'
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'}),
                 FormItem(keys={'Age':None},
                          vtype='int', supported_languages={'French'},
                          default_language='French'),
                 FormItem(keys={'Timestamp':None},
                          vtype='datetime', generator='timestamp_creation',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Titre de formulaire'})
        sh1 = DataSheet(sheet_id, form, user=user)

        sh1.set_default_view('latest')

        # Add sheet to workbook (auto save)
        logger.debug('utest: add sheet1 to workbook1')
        wb1.add_sheet(sh1) # note: this is an admin feature

        form = sh1.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : 'CE9999', 'Age' : 43,
                                    'Timestamp' : datetime(2021, 4, 16, 17, 28)})
        form.submit()

        # TODO: utest Error when trying to add sheet with already used ID

        # Create a new form for sh1
        logger.debug('utest: get live form 1 from workbook1')
        f1_id = 111
        f1 = sh1.form_new_entry(form_id=f1_id)
        logger.debug('utest: get live form 2 from workbook1')
        f2_id = 222
        f2 = sh1.form_new_entry(form_id=f2_id)

        # will call input_callback hooked by workbook, that saves entry to file
        logger.debug('utest: set Participant_ID using form 1 from workbook1')
        f1['section1']['Participant_ID'].set_input_str('CE0001')

        # Create a new workbook
        logger.debug('-----------------------')
        logger.debug('utest: create workbook2')
        wb2 = WorkBook(wb_id, data_folder, fs)
        wb2.decrypt(self.access_pwd)

        wb2.user_login(user, self.admin_pwd)
        # Check that sheet Participant_info is properly loaded
        # Check that pending live forms are properly loaded
        print('wb2.sh:')
        print(wb2.get_sheet(sh1.label).df)

        sh_reloaded = wb2.sheets['Participant_info']
        print('wb2.sh df after loading:')
        print(sh_reloaded.df)

        f1_reloaded = sh_reloaded.live_forms[f1_id]
        f1_reloaded['section1']['Age'].set_input_str('42')
        f1_reloaded.submit()
        print('wb2.sh df after submission:')
        print(sh_reloaded.df)
        df_from_f1 = sh_reloaded.df.tail(1)
        self.assertEqual(df_from_f1['Age'].iloc[0], 42)
        self.assertEqual(df_from_f1['Participant_ID'].iloc[0], 'CE0001')
        f2_reloaded = sh_reloaded.live_forms[f2_id]
        f2_reloaded.cancel()
        self.assertEqual(len(sh_reloaded.live_forms), 0)
        self.assertTrue(len(sh_reloaded.filesystem.listdir('live_forms')), 0)

        wb1.reload()
        self.assertEqual(wb1, wb2)

    def test_dashboard(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        wb.set_access_password(self.access_pwd)
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        wb.set_password(UserRole.EDITOR, self.editor_pwd)
        wb.decrypt(self.access_pwd)
        wb.set_user(user, UserRole.ADMIN)
        wb.user_login(user, self.admin_pwd)

        # Create data sheet participant info (no form)
        sheet_id = 'Participants'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE90001'],
                              'Secure_ID' : ['452164532', '5R32141']})
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Secure_ID':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          allow_empty=False)
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=user)

        # Create data sheet evaluation with outcome = OK or FAIL
        sheet_id = 'Evaluation'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),
                 FormItem(keys={'Planned':None},
                          vtype='boolean', supported_languages={'French'},
                          default_language='French',
                          allow_empty=False),
                 FormItem(keys={'Outcome':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          allow_empty=False),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime', generator='timestamp_submission',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh_eval = DataSheet(sheet_id, form, user=user)

        wb.add_sheet(sh_eval)
        wb.add_sheet(sh_pp)

        # Create dashboard sheet that gets list of participants from p_info
        # and compute evaluation status. Action is a string report.
        class Dashboard(LescaDashboard):
            def sheets_to_watch(self):
                return super(Dashboard, self).sheets_to_watch() + \
                    ['Evaluation']

            def after_workbook_load(self):
                self.eval = self.workbook['Evaluation']
                super(Dashboard, self).after_workbook_load()

            def refresh_entries(self, pids):
                logger.debug('Dashboard refresh for: %s', pids)

                self.df.loc[pids, 'Eval'] = 'eval_todo'
                eval_df = self.eval.get_df_view('latest')
                if eval_df is not None:
                    eval_df = eval_df.set_index('Participant_ID')
                    common_index = (set(pids)
                                    .intersection(self.df.index)
                                    .intersection(eval_df.index))
                    eval_df = eval_df.loc[common_index, :]

                    map_set(self.df, 'Eval',
                            {'eval_OK':
                             And((eval_df, 'Planned', [True]),
                                 (eval_df, 'Outcome', ['OK'])),
                            'eval_FAIL':
                             Or((eval_df, 'Planned', [False]),
                                (eval_df, 'Outcome', ['FAIL']))
                             })
            def action(self, entry_df, selected_column):
                logger.debug('plugin.action: entry_df=%s, selected_column=%s',
                             entry_df, selected_column)
                form, action_label = None, None
                if selected_column.startswith('Eval'):
                    participant_id = entry_df.index[0]
                    eval_df = self.eval.get_df_view('latest')
                    selection = eval_df[eval_df.Participant_ID == participant_id]
                    if selection.shape[0] == 0:
                        form = self.eval.form_new_entry()
                        form.set_values_from_entry({'Participant_ID' :
                                                    participant_id})
                        action_label = '%s | New' % self.eval.label
                    else:
                        assert(selection.shape[0] == 1)
                        form = self.eval.form_update_entry(selection.index[0])
                        action_label = '%s | Update' % self.eval.label
                    form.set_values_from_entry({
                        'Session_Action' : 'do_session',
                        'Staff' : self.eval.user
                    })
                return form, action_label

        logger.debug('utest: Create dashboard')
        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin(Dashboard(sh_dashboard))
        wb.add_sheet(sh_dashboard)

        wb.after_workbook_load()

        dashboard_df = sh_dashboard.get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Eval'] == 'eval_todo').all())

        logger.debug('utest: Add new participant CE90002')
        # Add new pp
        form = sh_pp.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : 'CE90002',
                                    'Secure_ID' : '5432524'})
        form.submit()

        dashboard_df = sh_dashboard.get_df_view()
        last_dashboard_entry = dashboard_df.tail(1)
        self.assertEqual(last_dashboard_entry.index[0], 'CE90002')
        self.assertEqual(last_dashboard_entry['Eval'].iat[0], 'eval_todo')

        # Add new eval
        logger.debug('utest: Add evaluation for CE4444 '\
                     '(not in participants list)')
        pid = 'CE4444'
        form = sh_eval.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : pid,
                                    'Planned' : True,
                                    'Outcome' : 'FAIL',
                                    'Timestamp_Submission' : datetime.now()})
        form.submit()
        dashboard_df = sh_dashboard.get_df_view()
        self.assertNotIn(pid, dashboard_df.index)

        # Add new eval
        logger.debug('utest: Add first evaluation for CE90002')
        pid = 'CE90002'
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith(sh_eval.label))
        form.set_values_from_entry({'Planned' : True,
                                    'Outcome' : 'FAIL',
                                    'Timestamp_Submission' : datetime.now()})
        form.submit()
        dashboard_df = sh_dashboard.get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_FAIL')

        sleep(0.01)
        logger.debug('utest: Add entry for participant who already passed eval')
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(sh_eval.label))
        form.set_values_from_entry({'Planned' : True,
                                    'Outcome' : 'OK',
                                    'Timestamp_Submission' : datetime.now()})
        form.submit()
        dashboard_df = sh_dashboard.get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_OK')

        sh_pp.delete_entry(sh_pp.df.index[1])
        dashboard_df = sh_dashboard.get_df_view()

        self.assertEqual(dashboard_df.shape, (2,1))


    def test_dashboard_status_track(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Study'
        user = 'me'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        wb.set_access_password(self.access_pwd)
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        wb.set_password(UserRole.EDITOR, self.editor_pwd)
        wb.decrypt(self.access_pwd)
        wb.set_user(user, UserRole.ADMIN)
        wb.user_login(user, self.admin_pwd)

        # Create sheet for participant status
        sheet_id = 'Participants'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002'],
                              'Study_Status' : ['ongoing', 'ongoing'],
                              'Staff' : ['TV', 'TV'],
                              'Timestamp_Submission' : [datetime(2021,9,9,10,10),
                                             datetime(2021,9,9,10,10)]})
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem({'Staff' : None},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem({'Study_Status' :
                           {'French':'Statut du participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          choices={
                              'ongoing' : {'French' : 'Etude en cours'},
                              'drop_out' : {'French' : "Sorti.e de l'étude"},
                          },
                          allow_empty=False),
                 FormItem(keys={'Timestamp_Submission' : None},
                          vtype='datetime',
                          generator='timestamp_submission',
                          supported_languages={'French'},
                          default_language='French')
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Status'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=user)

        # Create Progress note sheet
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem(keys={'Note_Type':None},
                          vtype='text', supported_languages={'French'},
                          choices={'health' : {'French' : 'Etat de santé'},
                                   'withdrawal' : {'French' : "Abandon"},
                                   'exclusion' : {'French' : "Exclusion"}
                                   },
                          default_language='French',
                          allow_empty=False),
                 FormItem(keys={'Timestamp_Submission' : None},
                          vtype='datetime',
                          generator='timestamp_submission',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Common progress note'})
        sh_pnote = DataSheet('Progress_Note', form, user=user)

        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_pp)

        class Dashboard(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(Dashboard, self).__init__(*args, **kwargs)

            def sheets_to_watch(self):
                return super(Dashboard, self).sheets_to_watch() + \
                    ['Progress_Note']

            def refresh_all(self):
                self.refresh_entries(self.df.index)
                self.sheet.invalidate_cached_views()

            def refresh_entries(self, pids):
                logger.debug('Dashboard refresh for: %s', pids)
                track_participant_status(self.df, 'Study_Status', 'Participants',
                                         'Progress_Note', self.workbook, pids)

            def action(self, entry_df, selected_column):
                return participant_status_action(entry_df, selected_column,
                                                 self.workbook, 'Participants')

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin(Dashboard(sh_dashboard))
        wb.add_sheet(sh_dashboard)

        wb.after_workbook_load()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Study_Status'] == 'ongoing').all())

        pid = 'CE0001'
        logger.debug('---- Test add progress note not related to drop-out ----')

        form, action = form_update_or_new('Progress_Note', wb,
                                          {'Participant_ID' : pid},
                                          entry_dict={'Note_Type' : 'health'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'ongoing')

        logger.debug('---- Test add exclusion progress note ----')
        form, action = form_update_or_new('Progress_Note', wb,
                                          {'Participant_ID' : pid},
                                          entry_dict={'Note_Type' : 'exclusion'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'confirm_drop')

        logger.debug('---- Test ignore exclusion from progress note ----')
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Study_Status')
        self.assertTrue(action_label.endswith('Update'), action_label)
        self.assertTrue(action_label.startswith('Participants'), action_label)

        form.set_values_from_entry({'Study_Status' : 'ongoing'})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'ongoing')

        logger.debug('---- Test add withdrawal progress note ----')
        form, action = form_update_or_new('Progress_Note', wb,
                                          {'Participant_ID' : pid},
                                          entry_dict={'Note_Type' : 'withdrawal'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'confirm_drop')

        logger.debug('---- Test accept withdrawal from progress note ----')
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Study_Status')
        self.assertTrue(action_label.endswith('Update'), action_label)
        self.assertTrue(action_label.startswith('Participants'), action_label)

        form.set_values_from_entry({'Study_Status' : 'drop_out'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'drop_out')

    def test_dashboard_interview_track(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        self.user = 'me'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        wb.set_access_password(self.access_pwd)
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        wb.set_password(UserRole.EDITOR, self.editor_pwd)
        wb.decrypt(self.access_pwd)
        wb.set_user(self.user, UserRole.ADMIN)
        wb.user_login(self.user, self.admin_pwd)

        # Create data sheet participant info (no form)
        sheet_id = 'Participants'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002']})
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=self.user)

        # Create Interview plan sheet
        sheet_id = DEFAULT_INTERVIEW_PLAN_SHEET_LABEL
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          unique=True,
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem({'Staff' : None},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Interview_Type':None},
                          vtype='text', supported_languages={'French'},
                          choices={'Preliminary' :
                                   {'French' : 'Séance préliminaire'},
                                   'Eval' : {'French' : "Séance d'évaluation"}
                          },
                          default_language='French',
                          allow_empty=False),
                 FormItem(keys={'Plan_Action':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'plan':{'French':'Plannifier un rendez-vous'},
                                   'cancel_date':
                                   {'French':'Annuler le rendez-vous précédent'},
                                   'assign_staff':
                                   {'French':'Assigner un intervenant'}},
                          allow_empty=False),
                 FormItem(keys={'Interview_Date':None},
                          vtype='datetime', supported_languages={'French'},
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Availability':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Date_Is_Set':None},
                          vtype='boolean', supported_languages={'French'},
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Callback_Days':None},
                          vtype='int', supported_languages={'French'},
                          default_language='French',
                          number_interval={'left':0, 'closed':'neither'},
                          allow_empty=True),
                 FormItem(keys={'Send_Email':None},
                          vtype='boolean', supported_languages={'French'},
                          default_language='French',
                          choices={'True':{'French':'Envoyer un courriel'},
                                   'False':{'French':'NE PAS envoyer de courriel'}},
                          allow_empty=True),
                 FormItem(keys={'Email_Schedule':None},
                         vtype='text', supported_languages={'French'},
                         default_language='French',
                         choices={'now':None,
                                  'days_before_1':None,
                                  'days_before_2':None,
                                  'days_before_3':None},
                          allow_empty=True),
                 FormItem(keys={'Email_Template':None},
                         vtype='text', supported_languages={'French'},
                         default_language='French',
                         choices={'Eval':None,
                                  'Eval_remind':None,
                                  'Preliminary':None,
                                  'Preliminary_remind':None},
                          allow_empty=True),
                FormItem(keys={'Email_Status':None},
                         vtype='text', supported_languages={'French'},
                         default_language='French',
                         choices={'to_send':None,
                                  'sent':None,
                                  'error':None},
                         init_values={'Email_Status' : 'to_send'},
                         allow_empty=True),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          allow_empty=False,
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Plannification'})
        sh_plan = DataSheet(sheet_id, form, user=self.user)

        # Create evaluation sheet
        sheet_id = 'Eval'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          unique=True,
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Session_Action':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'do_session':{'French':'Réaliser la séance'},
                                   'cancel_session':
                                   {'French':'Annuler la séance'}},
                          allow_empty=False),
                 FormItem(keys={'Session_Status':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'done':None,
                                   'redo':None},
                          allow_empty=True),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh_eval = DataSheet(sheet_id, form, user=self.user)

        wb.add_sheet(sh_plan)
        wb.add_sheet(sh_eval)
        wb.add_sheet(sh_pp)

        # Create dashboard sheet that gets list of participants from p_info
        # and compute evaluation status.
        class Dashboard(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(Dashboard, self).__init__(*args, **kwargs)
                self.date_now = None

            def after_workbook_load(self):
                self.eval_tracker = InterviewTracker('Eval', self.workbook)
                super(Dashboard, self).after_workbook_load()

            def sheets_to_watch(self):
                return super(Dashboard, self).sheets_to_watch() + \
                    [DEFAULT_INTERVIEW_PLAN_SHEET_LABEL, 'Eval']

            def refresh_all(self):
                self.refresh_entries(self.df.index)
                self.sheet.invalidate_cached_views()

            def refresh_entries(self, pids):
                logger.debug('Dashboard refresh for: %s', pids)
                self.eval_tracker.track(self.df, pids, date_now=self.date_now)

            def action(self, entry_df, selected_column):
                return self.eval_tracker.action(entry_df, selected_column)

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin(Dashboard(sh_dashboard))
        wb.add_sheet(sh_dashboard)

        wb.after_workbook_load()

        df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((df['Eval'] == 'eval_not_done').all())

        from .plugin_tools import DATE_FMT
        pid = 'CE0001'
        logger.debug('---- Test most recent entry in plan sheet ----')

        logger.debug('----- Assign staff for %s -----', pid)

        dashboard_df = wb['Dashboard'].get_df_view()
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Staff')
        self.assertTrue(action_label.endswith('New'), action_label)
        plan_sheet_label = DEFAULT_INTERVIEW_PLAN_SHEET_LABEL
        self.assertTrue(action_label.startswith(plan_sheet_label), action_label)

        ts = datetime(2021,9,10,10,10)
        form.set_values_from_entry({'Plan_Action' : 'assign_staff',
                                    'Staff' : 'Thomas Vincent',
                                    'Timestamp_Submission' : ts})
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'eval_not_done')
        self.assertEqual(df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(df.loc[pid, 'Eval_Plan'], 'eval_plan')

        logger.debug('------- Pid %s: Plan interview date, no email --------',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        print('action_label:', action_label)
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))

        form.set_values_from_entry({'Plan_Action' : 'plan',
                                    'Interview_Date' : idate,
                                    'Availability' : 'ignored',
                                    'Date_Is_Set' : True,
                                    'Send_Email' : False,
                                    'Timestamp_Submission' : ts})
        # TODO: test Date_Is_Set False but date is not None
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'eval_scheduled')
        self.assertEqual(df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATE_FMT))

        logger.debug('-- Pid %s: No planned date, availability, no callback --',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11,30)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Plan_Action' : 'plan',
                                    'Interview_Date' : None,
                                    'Availability' : 'parfois',
                                    'Date_Is_Set' : False,
                                    'Callback_days' : 0,
                                    'Send_Email' : False,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_not_done')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        logger.debug('-- Pid %s: No planned date, availability, '\
                     'callback in 7 days --', pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11,35)
        wb['Dashboard'].plugin.date_now = ts
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        callback_nb_days = 7
        form.set_values_from_entry({'Callback_Days' : callback_nb_days,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_callback_%dD' % callback_nb_days)
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        wb['Dashboard'].plugin.date_now = ts + timedelta(days=1)
        wb['Dashboard'].plugin.refresh_all()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_callback_%dD' % (callback_nb_days-1))
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        wb['Dashboard'].plugin.date_now = ts + timedelta(days=callback_nb_days+1)
        wb['Dashboard'].plugin.refresh_all()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_callback_now' )
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        logger.debug('------- Pid %s: Plan interview date, with email --------',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,12)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Interview_Date' : idate,
                                    'Date_Is_Set' : True,
                                    'Send_Email' : True,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_email_pending')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATE_FMT))

        logger.debug('------- Interview email sent for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,13)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Email_Status' : 'sent',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_email_sent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATE_FMT))


        logger.debug('------- Interview email error for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,14)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Email_Status' : 'error',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_email_error')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Thomas Vincent')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATE_FMT))

        logger.debug('------- Interview done for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,16)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Eval'))

        form.set_values_from_entry({'Session_Action' : 'do_session',
                                    'User' : 'Thomas Vincent',
                                    'Session_Status' : 'done',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_done')
        # Overriding User field does not work:
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], wb.user)
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         ts.strftime(DATE_FMT))

        logger.debug('------- Interview to redo for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,17)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Eval'))
        form.set_values_from_entry({'Session_Action' : 'do_session',
                                    'Session_Status' : 'redo',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_redo')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], wb.user)
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         ts.strftime(DATE_FMT))

        logger.debug('------- Interview cancelled for %s --------' % pid)
        idate = datetime(2021,10,11,10,10)
        ts = datetime(2021,9,10,10,18)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Eval'))
        form.set_values_from_entry({'Session_Action' : 'cancel_session',
                                    'User' : 'Thomas Vincent',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_cancelled')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], wb.user)
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'eval_plan')

        logger.debug('--- Pid %s: Plan interview date again, with email ----',
                     pid)
        idate = datetime(2021,10,15,10,10)
        ts = datetime(2021,9,10,10,29)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Interview_Date' : idate,
                                    'Date_Is_Set' : True,
                                    'Staff' : 'Catherine-Alexandra Grégoire',
                                    'Send_Email' : True,
                                    'Email_Status' : 'to_send',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_email_pending')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Catherine-Alexandra Grégoire')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATE_FMT))

    def test_dashboard_emailled_poll_track(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        wb.set_access_password(self.access_pwd)
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        wb.set_password(UserRole.EDITOR, self.editor_pwd)
        wb.decrypt(self.access_pwd)
        wb.set_user(user, UserRole.ADMIN)
        wb.user_login(user, self.admin_pwd)

        # Create data sheet participant info (no form)
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002']})
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sheet_label = 'Participants'
        sh_pp = DataSheet(sheet_label, form_master=form, df=pp_df, user=user)

        # Create Email sheet
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          unique=True,
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem({'Staff' : None},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Email_Action':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'plan':
                                   {'French':"Plannifier l'envoi d'un courriel"},
                                   'cancel':
                                   {'French':"Annuler l'envoi d'un courriel"},
                                   'call_off':
                                   {'French':"Supprimer le suivi d'envoi de courriel"}},
                          allow_empty=False),
                 FormItem(keys={'Email_Template':None},
                          vtype='text', supported_languages={'French'},
                          choices={'Poll' : {'French' : 'Sondage'},
                                   'Eval' : {'French' : "Séance d'évaluation"}},
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Email_Schedule':None},
                          vtype='datetime', supported_languages={'French'},
                          generator='timestamp_creation',
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Overdue_Days':None},
                          vtype='int', supported_languages={'French'},
                          default_language='French',
                          allow_empty=True),
                 FormItem(keys={'Email_Status':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'to_send':None,
                                   'sent':None,
                                   'error':None},
                          init_values={'Email_Status' : 'to_send'},
                          allow_empty=True),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          allow_empty=True,
                          supported_languages={'French'},
                          default_language='French')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Plannification'})
        sheet_email_label = 'Email'
        sh_email = DataSheet(sheet_email_label, form, user=user)

        # Create Poll sheet
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          unique=True,
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem({'Answer' : None},
                          vtype='boolean',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem({'Timestamp_Submission' : None},
                          vtype='datetime',
                          default_language='French',
                          supported_languages={'French'},
                          generator='timestamp_submission')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Plannification'})
        sheet_poll_label = 'Poll'
        sh_poll = DataSheet(sheet_poll_label, form, user=user)

        wb.add_sheet(sh_email)
        wb.add_sheet(sh_poll)
        wb.add_sheet(sh_pp)

        class Dashboard(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(Dashboard, self).__init__(*args, **kwargs)
                self.date_now = None

            def sheets_to_watch(self):
                return super(Dashboard, self).sheets_to_watch() + \
                    ['Poll', 'Email']

            def refresh_all(self):
                self.refresh_entries(self.df.index)
                self.sheet.invalidate_cached_views()

            def refresh_entries(self, pids):
                logger.debug('Dashboard refresh for: %s', pids)
                track_emailled_poll(self.df, 'Poll', 'Email', self.workbook, pids,
                                    date_now=self.date_now)

            def action(self, entry_df, selected_column):
                return emailled_poll_action(entry_df, selected_column, 'Email',
                                            self.workbook)

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin(Dashboard(sh_dashboard))
        wb.add_sheet(sh_dashboard)

        wb.after_workbook_load()

        pid = 'CE0001'
        logger.debug('--- Pid %s: Email not planned ----', pid)
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Poll'] == 'poll_to_send').all())

        logger.debug('--- Pid %s: Plan email ----', pid)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Poll')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Email_Action' : 'plan',
                                    'Staff' : 'Catherine-Alexandra Grégoire',
                                    'Email_Template' : 'Poll',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_pending')

        logger.debug('--- Pid %s: Cancel email ----', pid)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Email_Action' : 'cancel',
                                    'Staff' : 'Catherine-Alexandra Grégoire'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_to_send')

        logger.debug('--- Pid %s: Plan email again ----', pid)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Email_Action' : 'plan',
                                    'Staff' : 'Thomas Vincent',
                                    'Email_Template' : 'Poll',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_pending')

        logger.debug('--- Pid %s: Email error ----', pid)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Email_Action' : 'plan',
                                    'Staff' : 'Script',
                                    'Email_Template' : 'Poll',
                                    'Email_Status' : 'error',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_error')

        logger.debug('--- Pid %s: Email sent, not answered ----', pid)
        form, action_label = sh_dashboard.plugin.action(dashboard_df.loc[[pid]],
                                                        'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        ts = datetime(2021,9,10,10,29)
        wb['Dashboard'].plugin.date_now = ts
        overdue_nb_days = 2
        form.set_values_from_entry({'Email_Action' : 'plan',
                                    'Staff' : 'Script',
                                    'Email_Template' : 'Poll',
                                    'Email_Status' : 'sent',
                                    'Overdue_Days' : overdue_nb_days,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_sent')

        logger.debug('--- Pid %s: Email sent, overdue ----', pid)
        wb['Dashboard'].plugin.date_now = ts + timedelta(days=overdue_nb_days+1)
        wb['Dashboard'].plugin.refresh_all()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_overdue')

        # logger.debug('--- Pid %s: Email sent, overdue, remind ----', pid)

        # logger.debug('--- Pid %s: Email sent, overdue too long ----', pid)

        logger.debug('--- Pid %s: Email answered ----', pid)
        form = sh_poll.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : pid,
                                    'Answer' : True})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_answered')

        # logger.debug('--- Pid %s: Plan email again after answer ----', pid)
        # TODO: not sure useful. If there has been an anwser, no need to track
        # new email.

    def test_workbook_version(self):
        # TODO: enable version tracking while loading a workbook
        # Must be backward compatible
        # Maintain frozen workbook examples for all versions and insure
        # that they load properly
        pass

    def test_admin_features(self):
        # TODO
        # Test that admin lock / unlock works for all sheets

        # Merge all sheet entries

        # Add a user

        # Edit and entry
        pass

    def test_edition_form_not_persistent(self):
        # Edition requires to keep a reference of the row that is being edited.
        # df index can have duplicates, so a row cannot be unambiguously
        # identified by its index value.
        # Alternative:
        #    - use row integer index. It is ok while the df does not change,
        #      ie during the span of program run.
        #      But on reload, row order may change because of concurrent submission.
        #      So form data in edition mode cannot be persistent in this case
        #    - Always add an extra "internal" UUID column to uniquely identify
        #      a row. Peristence of edition form data is then possible.
        #      A drawback may the additional memory (16 bytes per entry),
        #      But it is neglible when dfs have lots of columns and one uses
        #      few sheets. With a lot of sheets, it may be an issue.
        # A key requirement is full data integrity:
        # Data overwriting because of concurrent access must never happen.
        # Since entry editing is precisely overwriting content, it should
        # only be an admin function to resolve data consistence issues.
        # So edition form data do not have to be persistent.
        pass

    def test_new_entry_form_persistent(self):
        # TODO: test persistence of *multiple* pending forms
        # Saving is user-dependent so must be handled at WorkBook level
        pass


class TestPasswordVault(unittest.TestCase):

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp()
        self.password_file = op.join(self.tmp_dir, 'passwords.json')
        logger.setLevel(logging.DEBUG)

    def tearDown(self):
        shutil.rmtree(self.tmp_dir)

    def test_set_password_no_old(self):
        vault = PasswordVault.from_file(self.password_file)
        pwd = '123456'
        vault.set_password('user', pwd)
        self.assertTrue(len(vault['passwords']['user'])>0)
        self.assertRaises(InvalidPassword, vault.set_password,
                          'user', 'new_pwd')

    def test_set_password_invalid_old(self):
        vault = PasswordVault.from_file(self.password_file)
        pwd = '123456'
        vault.set_password('user', pwd)
        self.assertRaises(InvalidPassword, vault.set_password,
                          'user', 'new_pwd', 'bad_old_pwd')

    def test_check(self):
        vault = PasswordVault.from_file(self.password_file)
        access_pwd = '123456'
        admin_pwd = '5623653'
        vault.set_password('access', access_pwd)
        vault.set_password('admin', admin_pwd)
        vault.save()

        vault2 = PasswordVault.from_file(self.password_file)
        self.assertRaises(InvalidPassword, vault2.check, 'admin', 'yoyo')
        vault2.check('admin', admin_pwd)
        vault2.check('access', access_pwd)

    def test_check_unknown_user(self):
        vault = PasswordVault.from_file(self.password_file)
        access_pwd = '123456'
        vault.set_password('access', access_pwd)

        vault2 = PasswordVault.from_file(self.password_file)
        self.assertRaises(UnknownUser, vault2.check, 'yolo', 'pwd')

class TestEncryption(unittest.TestCase):

    def test_fernet_with_password(self):
        password = "password"
        salt = os.urandom(32)
        key = derive_key(password, salt)
        f = Fernet(key)
        message = "Secret message!"
        token = f.encrypt(message.encode())
        self.assertEqual(message, f.decrypt(token).decode())

    def test_crypter(self):
        password = "password"
        salt = os.urandom(16)

        crypter = Encrypter(password, salt)
        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

    def test_key_access(self):
        password = "password"
        salt = os.urandom(16)
        crypter = Encrypter(password, salt)

        message = 'This is secret'
        crypted_message = crypter.encrypt_str(message)
        crypter2 = Encrypter.from_key(crypter.get_key())
        self.assertEqual(message, crypter2.decrypt_to_str(crypted_message))


def df_to_list_of_arrays(df):
    return list(zip(*[(c,s.to_numpy()) for c,s in df.iteritems()]))

class DataSheetModel(QtCore.QAbstractTableModel):

    def __init__(self, data_sheet):
        QtCore.QAbstractTableModel.__init__(self)
        self.sheet = data_sheet

        self.sort_icol = 0
        self.sort_ascending = True
        self.refresh_view()

        self.sheet.notifier.add_watcher('views_refreshed', self.refresh_view)

    def refresh_view(self):
        self.view_df = self.sheet.get_df_view()
        # assert(self.view_df.index.is_lexsorted())

        self.nb_rows = 0
        self.nb_cols = 0
        self.view = []
        self.colums = []
        self.view_validity = []
        self.sort_idx = []
        if self.view_df is not None:
            view_validity_df = self.sheet.view_validity()
            if self.sheet.plugin.show_index_in_ui():
                self.columns, self.view = df_to_list_of_arrays(self.view_df
                                                               .reset_index())
                _, self.view_validity = df_to_list_of_arrays(view_validity_df
                                                             .reset_index())
            else:
                self.columns, self.view = df_to_list_of_arrays(self.view_df)
                _, self.view_validity = df_to_list_of_arrays(view_validity_df)

            self.nb_cols = len(self.columns)
            self.nb_rows = len(self.view[0])

            self.sort_idx = np.argsort(self.view[self.sort_icol])
            if not self.sort_ascending:
                self.sort_idx = self.sort_idx[::-1]

    def rowCount(self, parent=None):
        return self.nb_rows

    def columnCount(self, parent=None):
        return self.nb_cols

    def data(self, index, role=QtCore.Qt.DisplayRole):
        icol = index.column()
        if index.isValid():
            if role == QtCore.Qt.TextAlignmentRole:
                # TODO let hint define alignement!
                return QtCore.Qt.AlignLeft | QtCore.Qt.AlignVCenter
                # if icol == 0:
                #     return QtCore.Qt.AlignLeft | QtCore.Qt.AlignVCenter
                # else:
                #     return QtCore.Qt.AlignCenter
            else:
                irow = self.sort_idx[index.row()]
                value = self.view[icol][irow]
                if role == QtCore.Qt.DisplayRole:
                    value_str = str(value) if not pd.isna(value) else ''
                    return value_str

                hint = self.sheet.plugin.hint(self.columns[icol], value)
                if hint is not None:
                    if role == QtCore.Qt.ForegroundRole:
                        return hint.foreground_qcolor
                    elif role == QtCore.Qt.DecorationRole:
                        return hint.qicon
                    elif role == QtCore.Qt.ToolTipRole:
                        return hint.message

                if role == QtCore.Qt.BackgroundRole:
                    bg_color = ui.main_qss.default_bg_qcolor

                    if not self.view_validity[icol][irow]:
                        bg_color = ui.main_qss.error_color
                    elif hint is not None and  hint.background_qcolor is not None:
                        bg_color = hint.background_qcolor

                    if index.row() % 2:
                        f = ui.main_qss.table_cell_even_row_darker_factor
                        bg_color = bg_color.darker(f)

                    return bg_color
        return None

    def entry_id(self, index):
        """ ASSUME: not called with "dynamic" sheet """
        if index.isValid():
            return self.view_df.index[self.sort_idx[index.row()]]
        return None

    def entry_df(self, index):
        if index.isValid():
            return self.view_df.iloc[[self.sort_idx[index.row()]],:]
        return None

    def headerData(self, icol, orientation, role):
        if role==QtCore.Qt.DisplayRole:
            if orientation == QtCore.Qt.Horizontal:
                return self.columns[icol]
        return None

    @QtCore.pyqtSlot()
    def update_after_append(self, entry_df):
        irow = self.view_df.index.get_loc(entry_df.index[0])
        tree_view_irow = np.where(self.sort_idx==irow)[0][0]
        self.beginInsertRows(QtCore.QModelIndex(), tree_view_irow, tree_view_irow)
        # TODO: proper callback to actual data change here
        self.endInsertRows()
        return True

    def update_before_delete(self, entry_id):
        irow = self.view_df.index.get_loc(entry_id)
        tree_view_irow = np.where(self.sort_idx==irow)[0][0]
        logger.debug('before_delete(%s) -> irow = %d',
                     entry_id, tree_view_irow)
        self.layoutAboutToBeChanged.emit()
        self.beginRemoveRows(QtCore.QModelIndex(), tree_view_irow, tree_view_irow)

    @QtCore.pyqtSlot()
    def update_after_delete(self, entry_df):
        # TODO: proper callback to actual data change here
        self.endRemoveRows()
        self.layoutChanged.emit()
        return True

    @QtCore.pyqtSlot()
    def update_after_clear(self):
        logger.debug('ItemModel of %s: Update_after_full_clear',
                     self.sheet.label)
        self.layoutAboutToBeChanged.emit()
        self.beginResetModel()
        self.endResetModel()
        self.layoutChanged.emit()
        return True

    @QtCore.pyqtSlot()
    def update_after_set(self, entry_idx):
        irow = self.view_df.index.get_loc(entry_idx)
        tree_view_irow = np.where(self.sort_idx==irow)[0][0]
        ncols = self.view_df.shape[1]
        self.dataChanged.emit(self.createIndex(tree_view_irow, 0),
                              self.createIndex(tree_view_irow, ncols-1))
        return True

def dict_lazy_setdefault(d, k, make_value):
    # TODO: ustest
    if k not in d:
        v = make_value()
        d[k] = v
        return v
    else:
        return d[k]

class text_connect:
    def __init__(self, text_get, text_set, ignore_empty=False):
        self.text_get = text_get
        self.text_set = text_set
        self.ignore_empty = ignore_empty
    def __call__(self):
        txt = self.text_get()
        if txt != '' or not self.ignore_empty:
            self.text_set(txt)

class get_set_connect:
    def __init__(self, f_get, f_set):
        self.get = f_get
        self.set = f_set
    def __call__(self):
        self.set(self.get())

def make_item_input_widget(item_widget, item, key, key_label,
                           item_is_single=False):
    input_widget = QtWidgets.QWidget(item_widget)
    init_value = item.values_str[key]
    _input_ui = None
    if (item.vtype == 'text' and item.choices is None and \
        item.nb_lines<=1) or item.vtype == 'int' or \
        item.vtype == 'number' or item.vtype == 'int64':
        # Single line input field
        _input_ui = ui.item_single_line_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        if not item_is_single:
            item.notifier.add_watcher('language_changed', refresh_label_key)
        #_input_ui.label_key.setText(item.tr[key])
        _input_ui.value_field.setText(init_value)
        callback = text_connect(_input_ui.value_field.text, item.set_input_str)
        _input_ui.value_field.editingFinished.connect(callback)
    elif item.vtype == 'text' and item.choices is None and \
         item.nb_lines>1:
        # Multi line input field
        _input_ui = ui.item_text_multi_line_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        _input_ui.value_field.setPlainText(init_value)
        callback = text_connect(_input_ui.value_field.toPlainText,
                                item.set_input_str)
        _input_ui.value_field.editingFinished.connect(callback)
    elif (item.vtype == 'boolean' and not item_is_single):
        _input_ui = ui.item_boolean_checkboxes_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.check_box)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        _input_ui.check_box.toggled.connect(lambda b: item.set_input_str('%s'%b))
        if init_value != '':
            _input_ui.check_box.setChecked(item.get_value())
    elif (item.vtype == 'text' and item.choices is not None) or\
         (item.vtype == 'boolean' and item_is_single):
        # Radio buttons
        _input_ui = ui.item_choice_radio_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        if not item_is_single:
            item.notifier.add_watcher('language_changed', refresh_label_key)

        radio_group = QtWidgets.QButtonGroup(input_widget)
        for idx, choice in enumerate(item.choices.keys()):
            frame = _input_ui.radio_frame
            radio_button = QtWidgets.QRadioButton(frame)
            refresh_radio_text = refresh_text(item, choice, radio_button)
            refresh_radio_text()
            item.notifier.add_watcher('language_changed', refresh_radio_text)
            radio_button.setObjectName("radio_button_"+choice)
            _input_ui.radio_layout.addWidget(radio_button, idx)
            radio_group.addButton(radio_button, idx)
            class ChoiceProcess:
                def __init__(self, item, choice_button):
                    self.item = item
                    self.choice_button = choice_button
                def __call__(self, state):
                    if state:
                        self.item.set_input_str(self.choice_button.text())
            radio_button.toggled.connect(ChoiceProcess(item, radio_button))
            # if item.vtype == 'boolean':
            #     from IPython import embed; embed()
            if item.is_valid() and item.value_to_str() == choice:
                radio_group.button(idx).setChecked(True)
        if item.allow_other_choice:
            radio_group.addButton(_input_ui.radio_button_other, idx+1)

            def toggle_other_field(flag):
                # flag = _input_ui.radio_button_other.ischecked()
                _input_ui.other_field.setEnabled(flag)
            _input_ui.radio_button_other.toggled.connect(toggle_other_field)

            callback = text_connect(_input_ui.other_field.text, item.set_input_str)
            _input_ui.other_field.editingFinished.connect(callback)
        else:
            _input_ui.radio_button_other_frame.hide()

    elif item.vtype == 'date' or item.vtype == 'datetime':
        # Date/Time input
        _input_ui = ui.item_datetime_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        date_str, date_fmt, hour, mins = item.split_qdatetime_str(key)

        if date_str is not None:
            qdate = QtCore.QDate.fromString(date_str, date_fmt)
        else:
            qdate = QtCore.QDate()
        logger.debug2("Init date field with %s -> qdate=%s", date_str, qdate)
        date_collector = DateTimeCollector(item.set_input_str, qdate, hour, mins)

        _input_ui.datetime_field.setDate(qdate)
        _input_ui.datetime_field.dateChanged.connect(date_collector.set_date)
        if hour is not None:
            _input_ui.hour_field.setValue(hour)
        else:
            _input_ui.hour_field.clear()
        callback = get_set_connect(_input_ui.hour_field.value,
                                   date_collector.set_hours)
        _input_ui.hour_field.editingFinished.connect(callback)

        if mins is not None:
            _input_ui.minute_field.setValue(mins)
        else:
            _input_ui.minute_field.clear()
        callback = get_set_connect(_input_ui.minute_field.value,
                                   date_collector.set_minutes)
        _input_ui.minute_field.editingFinished.connect(callback)

        if item.vtype == 'date':
            _input_ui.frame_hour.hide()
    else:
        logger.error('Cannot make UI for item %s (vtype: %s)', item, item.vtype)

    if _input_ui is not None and item_is_single:
        _input_ui.label_key.hide()

    return input_widget

class refresh_text:
    def __init__(self, item, item_tr_label, ui_label,
                 hide_on_empty=True):
        self.item = item
        self.item_tr_label = item_tr_label
        self.ui_label = ui_label
        self.hide_on_empty = hide_on_empty
    def __call__(self):
        text = self.item.tr[self.item_tr_label]
        self.ui_label.setText(text)
        if self.hide_on_empty and (text is None or len(text)==0):
            self.ui_label.hide()
        else:
            self.ui_label.show()

def make_item_widget(section_widget, item):
    item_widget = QtWidgets.QWidget(section_widget)
    _item_ui = ui.form_item_ui.Ui_Form()
    _item_ui.setupUi(item_widget)

    refresh_title = refresh_text(item, 'title', _item_ui.title)
    refresh_title()
    item.notifier.add_watcher('language_changed', refresh_title)

    refresh_description = refresh_text(item, 'description',
                                       _item_ui.description,
                                       hide_on_empty=True)
    refresh_description()
    item.notifier.add_watcher('language_changed', refresh_description)

    _item_ui.label_invalid_message.hide()
    if isinstance(item, FormItem):
        invalidity_callback = text_connect(item.get_validity_message,
                                           _item_ui.label_invalid_message.setText)
        item.notifier.add_watcher('item_invalid', invalidity_callback)
        item.notifier.add_watcher('item_invalid',
                                  _item_ui.label_invalid_message.show)
        item.notifier.add_watcher('item_valid', _item_ui.label_invalid_message.hide)
        if item.allow_None:
            _item_ui.required_label.hide()
        for key, key_label in item.keys.items():
            input_widget = make_item_input_widget(item_widget, item, key,
                                                  key_label,
                                                  item_is_single=len(item.keys)==1)
            _item_ui.input_layout.addWidget(input_widget)
            if not item.editable:
                input_widget.setEnabled(False)
    return item_widget


class SheetViewChanger:

    def __init__(self, combobox, sheet_model):
        self.sheet_model = sheet_model
        self.combobox = combobox

    def __call__(self, combox_index):
        view_label = self.combobox.currentText()
        self.sheet_model.beginResetModel()
        self.sheet_model.sheet.set_default_view(view_label)
        self.sheet_model.refresh_view()
        self.sheet_model.endResetModel()
        self.sheet_model.layoutChanged.emit()

def language_abbrev(language):
    # https://www.loc.gov/standards/iso639-2/php/code_list.php
    return {'French' : 'Fre',
            'English' : 'Eng'}[language]



#!/usr/bin/python3
import sys
from PyQt5 import QtCore, QtGui, QtWidgets

CSS = \
{
    'QWidget':
    {
        'background-color': '#333333',
    },
    'QLabel#label':
    {
        'color': '#888888',
        'background-color': '#444444',
        'font-weight': 'bold',
    },
    'QLabel#label:active':
    {
        'color': '#1d90cd',
    },
    'QPushButton#button':
    {
        'color': '#888888',
        'background-color': '#444444',
        'font-weight': 'bold',
        'border': 'none',
        'padding': '5px',
    },
    'QPushButton#button:active':
    {
        'color': '#ffffff',
    },
    'QPushButton#button:hover':
    {
        'color': '#1d90cd',
    }
}
 
def dictToCSS(dictionnary):
    stylesheet = ""
    for item in dictionnary:
        stylesheet += item + "\n{\n"
        for attribute in dictionnary[item]:
            stylesheet += "  " + attribute + ": " + dictionnary[item][attribute] + ";\n"
        stylesheet += "}\n"
    return stylesheet

class EditorTabCloser:
    def __init__(self, tab_widget, check_on_close):
        self.tab_widget = tab_widget
        self.check_on_close = check_on_close
        self.editor_widget = None

    def set_editor_tab(self, editor_widget):
        self.editor_widget = editor_widget
        self.check_on_close.append(editor_widget)

    def __call__(self):
        if self.editor_widget is not None:
            self.check_on_close.remove(self.editor_widget)
            self.tab_widget.removeTab(self.tab_widget.indexOf(self.editor_widget))

class WorkBookCreateDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)

        self.setWindowTitle("Create workbook")

        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        self.form_widget = QtWidgets.QWidget(self)
        self.form_ui = ui.workbook_creation_ui.Ui_Form()
        self.form_ui.setupUi(self.form_widget)

        self.form_ui.open_button.clicked.connect(self.on_select_root_dir)

        self.required_fields = {
            'Access password' : self.form_ui.access_pwd_field,
            'Editor password' : self.form_ui.editor_pwd_field,
            'Manager password' : self.form_ui.manager_pwd_field,
            'Admin password' : self.form_ui.admin_pwd_field,
            'Admin name' : self.form_ui.adminNameLineEdit
        }

        self.layout = QtWidgets.QVBoxLayout()
        self.layout.addWidget(self.form_widget)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

    def on_select_root_dir(self):
        root_folder = (QtWidgets.QFileDialog
                       .getExistingDirectory(self, 'Select root directory', '',
                                             QtWidgets.QFileDialog.ShowDirsOnly))
        if root_folder is not None:
            self.form_ui.root_folder_lineEdit.setText(root_folder)

    @staticmethod
    def create(self, parent=None):
        dialog = WorkBookCreateDialog(parent=parent)
        result = dialog.exec_()
        if result == QtWidgets.QDialog.Accepted:
            return (dialog.workbook_cfg_fn, dialog.access_pwd, dialog.admin_name,
                    dialog.admin_pwd)
        else:
            return None, None, None, None

    def accept(self):
        if self.check():
            self._make_workbook()
            super().accept()

    def check(self, show_errors=True):
        error_messages = []

        wb_label = self.form_ui.workbook_label_lineEdit.text()
        if len(wb_label) == 0:
            error_messages.append('Workbook label must not be empty')

        root_dir = self.form_ui.root_folder_lineEdit.text()
        if not op.exists(root_dir):
            error_messages.append('Root folder does not exist (%s)' % root_dir)

        if len(wb_label) > 0 and op.exists(root_dir) and \
            (op.exists(op.join(root_dir, protect_fn(wb_label) + '_files')) or \
             op.exists(op.join(root_dir, protect_fn(wb_label) + '.psh'))):
            error_messages.append('Root folder already contain workbook files')

        for field_name, field in self.required_fields.items():
            if len(field.text()) == 0:
                error_messages.append('%s is required' % field_name)

        if len(error_messages) > 0:
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Critical)
            message_box.setText('Errors:\n%s' %
                                '\n'.join(' - %s' % e for e in error_messages))
            message_box.exec_()

            return False

        return True

    def _make_workbook(self):
        # ASSUME: all fields are valid
        wb_label = self.form_ui.workbook_label_lineEdit.text()
        root_dir = self.form_ui.root_folder_lineEdit.text()
        protected_wb_label = protect_fn(wb_label)
        fs = LocalFileSystem(root_dir)
        wb_cfg_rfn = protected_wb_label + '.psh'
        data_rpath = protected_wb_label + '_files'
        wb = WorkBook(wb_label, data_rpath, fs)
        wb.save_configuration_file(wb_cfg_rfn)
        self.access_pwd = self.form_ui.access_pwd_field.text()
        wb.set_access_password(self.access_pwd)
        wb.decrypt(self.access_pwd)
        editor_pwd = self.form_ui.editor_pwd_field.text()
        wb.set_password(UserRole.EDITOR, editor_pwd)
        manager_pwd = self.form_ui.manager_pwd_field.text()
        wb.set_password(UserRole.MANAGER, manager_pwd)
        self.admin_pwd = self.form_ui.admin_pwd_field.text()
        wb.set_password(UserRole.ADMIN, self.admin_pwd)
        self.admin_name = self.form_ui.adminNameLineEdit.text()
        wb.set_users({self.admin_name : UserRole.ADMIN})

        self.workbook_cfg_fn = fs.full_path(wb_cfg_rfn)

class WorkBookWidget(QtWidgets.QWidget, ui.workbook_ui.Ui_Form):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

class WorkBookWindow(QtWidgets.QMainWindow):

    def __init__(self):
        super(WorkBookWindow, self).__init__()
        self.workbook_ui = WorkBookWidget(self)
        self.setCentralWidget(self.workbook_ui)
        self.check_on_close = []
        self.resize(1260, 1020)

    def closeEvent(self, event):
        for widget in self.check_on_close:
            if not widget.closeEvent(event):
                break



class UsersEditor(QtWidgets.QWidget)
    def __init__(self, users, user_role, parent=None):
        super(UsersEditor, self).__init__(parent)

        self.table = QtGui.QTableWidget()
        self.table.setColumnCount(3) # User / Role / -

        for irow, (user, role) in enumerate(users.items()):
            item1 = QtGui.QTableWidgetItem(user)
            self.table.setItem(irow, 0, item1)
            item2 = QtGui.QTableWidgetItem()
            role_select = QtGui.QComboBox()
            for role in userRole:
                role_select.addItem(role.name)
            self.table.setCellWidget(irow, 1, role_select)
            item_minus = QtGui.QTableWidgetItem('-')
            self.table.setItem(irow, 0, item_minus)

        self.table.setItem(irow+1, 0, QtGui.QTableWidgetItem('+'))

class PiccelApp(QtWidgets.QApplication):

    USER_FILE = 'piccel.json'

    def __init__(self, argv, cfg_fn=None, user=None, access_pwd=None,
                 role_pwd=None, cfg_fns=None, refresh_rate_ms=0):
        super(PiccelApp, self).__init__(argv)

        self.setStyle('Fusion')
        self.setStyleSheet(ui.main_qss.main_style)
        Hints.preload(self)

        self.refresh_rate_ms = refresh_rate_ms

        # icon_style = QtWidgets.QStyle.SP_ComputerIcon
        # self.setWindowIcon(self.style().standardIcon(icon_style))
        self.setWindowIcon(QtGui.QIcon(':/icons/main_icon'))
        self.logic = PiccelLogic(UserData(PiccelApp.USER_FILE))

        self.selector_screen = QtWidgets.QWidget()
        _selector_ui = ui.selector_ui.Ui_Form()
        _selector_ui.setupUi(self.selector_screen)

        button_icon = QtGui.QIcon(':/icons/top_selection_open_icon')
        _selector_ui.button_open_file.setIcon(button_icon)
        _selector_ui.button_open_file.clicked.connect(self.select_file)

        button_icon = QtGui.QIcon(':/icons/top_selection_create_icon')
        _selector_ui.button_create.setIcon(button_icon)
        _selector_ui.button_create.clicked.connect(self.create)

        if cfg_fns is None:
            self.recent_files = self.logic.get_recent_files()
        else:
            logger.debug('Available cfg fn: %s', cfg_fns)
            self.recent_files = cfg_fns

        def load_workbook_title(wb_fn):
            try:
                with open(wb_fn, 'r') as fin:
                    return json.load(fin)['workbook_label']
            except Exception as e:
                logger.warning('Error loading workbook file %s:\n %s',
                               wb_fn, repr(e))
            return wb_fn
        # TODO add file path as tooltip
        workbook_titles, workbook_fns = [], []
        for fn in self.recent_files:
            wb_title = load_workbook_title(fn)
            if wb_title is not None:
                workbook_titles.append(wb_title)
                workbook_fns.append(fn)
        _selector_ui.recent_list.addItems(workbook_titles)

        def _cfg_fn():
            return workbook_fns[_selector_ui.recent_list.currentRow()]
        on_double_click = lambda i: self.open_configuration_file(_cfg_fn())
        _selector_ui.recent_list.itemDoubleClicked.connect(on_double_click)

        self.access_screen = QtWidgets.QWidget()
        self._access_ui = ui.access_ui.Ui_Form()
        self._access_ui.setupUi(self.access_screen)
        self._access_ui.button_cancel.clicked.connect(self.access_cancel) #TODO
        self._access_ui.button_ok.clicked.connect(self.access_process) #TODO
        access_ok_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Return"),
                                           self.access_screen)
        access_ok_shortcut.activated.connect(self.access_process)
        access_cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                                     self.access_screen)
        access_cancel_shortcut.activated.connect(self.access_cancel)

        self.login_screen = QtWidgets.QWidget()
        self._login_ui = ui.login_ui.Ui_Form()
        self._login_ui.setupUi(self.login_screen)
        self._login_ui.user_list.currentTextChanged.connect(self.login_preload_user)
        self._login_ui.button_cancel.clicked.connect(self.login_cancel)
        self._login_ui.button_ok.clicked.connect(self.login_process)
        login_ok_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Return"),
                                           self.login_screen)
        login_ok_shortcut.activated.connect(self.login_process)
        login_cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                              self.login_screen)
        login_cancel_shortcut.activated.connect(self.login_cancel)

        #self.workbook_screen = QtWidgets.QWidget()
        self.workbook_screen = WorkBookWindow()
        self._workbook_ui = self.workbook_screen.workbook_ui
        # self._workbook_ui = ui.workbook_ui.Ui_Form()
        # self._workbook_ui.setupUi(self.workbook_screen)

        self.current_widget = self.selector_screen

        self.screen_show = {
            PiccelLogic.STATE_WORKBOOK : self.show_workbook_screen,
            PiccelLogic.STATE_ACCESS : self.show_access_screen,
            PiccelLogic.STATE_LOGIN : self.show_login_screen,
            PiccelLogic.STATE_SELECTOR : self.show_screen(self.selector_screen)
            }

        self.default_user = user
        self.role_pwd = role_pwd
        self.access_pwd = access_pwd
        self.tab_indexes = {}

        if cfg_fn is not None:
            self.open_configuration_file(cfg_fn)
            if self.logic.workbook is not None and self.access_pwd is not None:
                self.access_process()
                if self.default_user is not None and self.role_pwd is not None:
                    self.login_process()

    def create(self):
        cfg_fn, self.access_pwd, self.default_user, self.role_pwd = \
            WorkBookCreateDialog.create(self)
        if cfg_fn is not None:
            self.open_configuration_file(cfg_fn)
            if self.logic.workbook is not None:
                self.access_process()
                self.login_process()
            else:
                logger.error('Workbook not properly loaded')

    def select_file(self):
        cfg_fn = QtWidgets.QFileDialog.getOpenFileName(self.selector_screen,
                                                       'Open file',
                                                       '', "Piccel files (*%s)" % \
                                                       PiccelLogic.CFG_FILE_EXT)
        logger.debug('getOpenFileName returned: %s', cfg_fn)
        self.open_configuration_file(cfg_fn[0])

    def open_configuration_file(self, cfg_fn):
        if cfg_fn is None or cfg_fn == '':
            return

        logger.debug('Open configuration file: %s', cfg_fn)
        filesystem = LocalFileSystem(op.dirname(cfg_fn))
        msg = self.logic.load_configuration(filesystem, op.basename(cfg_fn))
        if msg != 'ok':
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Critical)
            message_box.setText(msg)
            message_box.exec_()
        else:
            if not self.logic.workbook.has_write_access:
                message_box = QtWidgets.QMessageBox()
                message_box.setIcon(QtWidgets.QMessageBox.Critical)
                message_box.setText('Cannot write to %s. This could be an '\
                                    'unauthorized access in the cloud storage '\
                                    'client (ex Dropbox).' % \
                                    self.logic.workbook.filesystem.root_folder)
                message_box.exec_()
            self.refresh()

    def show_screen(self, screen):
        def _show():
            screen.show()
            return screen
        return _show

    def login_preload_user(self, user):
        self._login_ui.other_password_label.hide()
        self._login_ui.other_password_field.hide()
        self._login_ui.progressBar.hide()

        if user is not None and user != '':
            role = self.logic.workbook.get_user_role(user)
            logger.debug('Role of user %s: %s', user, role.name)
            if role == UserRole.ADMIN or \
               role == UserRole.MANAGER or \
               role == UserRole.EDITOR:
                self._login_ui.other_password_label.show()
                self._login_ui.other_password_field.show()
            if role == UserRole.ADMIN:
                self._login_ui.other_password_label.setText('Admin password')
            elif role == UserRole.EDITOR:
                self._login_ui.other_password_label.setText('Editor password')
            elif role == UserRole.MANAGER:
                self._login_ui.other_password_label.setText('Manager password')

    def access_cancel(self):
        self.logic.cancel_access()
        self.refresh()

    def access_process(self):
        logger.debug('Start access process')
        self._access_ui.button_ok.setEnabled(False)
        self._access_ui.button_cancel.setEnabled(False)

        error_message = None
        try:
            self.logic.decrypt(self._access_ui.access_password_field.text())
        except InvalidPassword:
            error_message = 'Invalid access password'

        if error_message is not None:
            message_box = QtWidgets.QErrorMessage()
            message_box.showMessage(error_message)
            message_box.exec_()

        logger.debug('End login process')
        self.refresh()

    def login_cancel(self):
        self.logic.cancel_login()
        self.refresh()

    def login_process(self):
        logger.debug('Start login process')
        self._login_ui.button_ok.setEnabled(False)
        self._login_ui.button_cancel.setEnabled(False)
        self._login_ui.progressBar.setValue(0)
        self._login_ui.progressBar.show()
        self.processEvents() # TODO: make it less ugly using signals and QThread

        def progress(value):
            self._login_ui.progressBar.setValue(value)
            self.processEvents()

        user = self._login_ui.user_list.currentText()
        role_pwd_input = self._login_ui.other_password_field.text()
        if role_pwd_input == '' or role_pwd_input is None:
            error_message = 'Password required'
        else:
            role_pwd = role_pwd_input
            error_message = None
            try:
                self.logic.login(user, role_pwd, progression_callback=progress)
                if self.refresh_rate_ms > 0:
                    self.timer = QtCore.QTimer(self)
                    logger.debug('Start data refresh timer with an interval of %d ms',
                                 self.refresh_rate_ms)
                    self.timer.setInterval(self.refresh_rate_ms)
                    self.timer.timeout.connect(self.logic.workbook
                                               .refresh_all_data)
                    self.timer.start()
            except UnknownUser:
                error_message = 'Unknown user: %s' %user
            except InvalidPassword:
                error_message = 'Invalid user password'

        if error_message is not None:
            message_box = QtWidgets.QErrorMessage()
            message_box.showMessage(error_message)
            message_box.exec_()

        logger.debug('End login process')
        self.refresh()

    def show_access_screen(self):
        self._access_ui.button_ok.setEnabled(True)
        self._access_ui.button_cancel.setEnabled(True)

        self._access_ui.workbook_label.setText(self.logic.workbook.label)
        self._access_ui.access_password_field.clear()
        if self.access_pwd is not None:
            self._access_ui.access_password_field.setText(self.access_pwd)
        self.access_screen.show()
        return self.access_screen

    def show_login_screen(self):
        # TODO: Add option to save debug log output in workbook
        self._login_ui.button_ok.setEnabled(True)
        self._login_ui.button_cancel.setEnabled(True)

        self._login_ui.user_list.clear()
        user_names = self.logic.get_user_names()
        if self.default_user in user_names:
            user_names = [self.default_user] + \
                [u for u in user_names if u != self.default_user]
        self._login_ui.user_list.addItems(user_names)
        self._login_ui.workbook_label.setText(self.logic.workbook.label)

        self._login_ui.other_password_field.clear()
        if self.role_pwd is not None:
            self._login_ui.other_password_field.setText(self.role_pwd)

        self.login_screen.show()
        return self.login_screen

    def make_text_editor(self, tab_widget, tab_label, text,
                         language, submit):
        text_editor_widget = QtWidgets.QWidget()
        _text_editor_ui = ui.text_editor_ui.Ui_Form()
        _text_editor_ui.setupUi(text_editor_widget)

        _text_editor_ui.textBrowser.setText(text)

        # __editor = Qsci.QsciScintilla()
        # __editor.setText(text)
        # __editor.setUtf8(True)
        # lexer = {
        #     'json' : lambda : Qsci.QsciLexerJSON(),
        #     'python' : lambda : Qsci.QsciLexerPython(),
        # }[language]()
        # __editor.setLexer(lexer)
        # vlayout = QtWidgets.QVBoxLayout(_text_editor_ui.frame_editor)
        # vlayout.setObjectName("vlayout_editor_frame")
        # vlayout.addWidget(__editor)

        tab_idx = tab_widget.addTab(text_editor_widget, tab_label)
        icon_style = QtWidgets.QStyle.SP_FileDialogListView
        tab_icon = QtGui.QIcon(':/icons/editor_icon')
        tab_widget.setTabIcon(tab_idx, tab_icon)
        tab_widget.setCurrentIndex(tab_idx)

        def _apply():
            submit(_text_editor_ui.textBrowser.toPlainText())

        def cancel():
            tab_widget.removeTab(tab_idx)

        def ok():
            _apply()
            tab_widget.removeTab(tab_idx)

        _text_editor_ui.button_cancel.clicked.connect(cancel)

        _text_editor_ui.button_apply.clicked.connect(_apply)
        _text_editor_ui.button_ok.clicked.connect(ok)

    def make_form_tab(self, tab_name, sheet_model, sheet_ui, tab_widget,
                      tab_idx, form):
        form_widget = QtWidgets.QWidget()
        _form_ui = ui.form_ui.Ui_Form()
        _form_ui.setupUi(form_widget)

        # Enable form buttons based on form notifications
        watchers = {
            'previous_section_available':
            [lambda: _form_ui.button_previous.setEnabled(True)],
            'previous_section_not_available' :
            [lambda: _form_ui.button_previous.setEnabled(False)],
            'next_section_available' :
            [lambda: _form_ui.button_next.setEnabled(True)],
            'next_section_not_available' :
            [lambda: _form_ui.button_next.setEnabled(False)],
            'ready_to_submit' :
            [lambda: _form_ui.button_submit.setEnabled(True)],
            'not_ready_to_submit' :
            [lambda: _form_ui.button_submit.setEnabled(False)],
        }
        logger.info('Make UI of live form "%s"', form.tr['title'])
        form.notifier.add_watchers(watchers)
        form.validate()

        #self.section_widget_stack = QtWidgets.QStackedWidget()
        section_widgets = {}
        # self.current_section_widget = None
        self.item_labels = []
        def make_section_widget(section_label, section):
            section_widget = QtWidgets.QWidget(form_widget)
            section_widget.setObjectName("section_widget_" + section_label + \
                                         section.tr.language)
            _section_ui = ui.section_ui.Ui_Form()
            _section_ui.setupUi(section_widget)
            refresh_title = refresh_text(section, 'title',
                                         _section_ui.title_label,
                                         hide_on_empty=True)
            refresh_title()
            section.notifier.add_watcher('language_changed', refresh_title)

            for item in section.items:
                if self.logic.workbook.user_role >= item.access_level:
                    item_widget = make_item_widget(section_widget, item)
                    _section_ui.verticalLayout.addWidget(item_widget)
            return section_widget

        def set_section_ui(section_label, section):
            #if self.current_section_widget is not None:
            #    self.current_section_widget.hide()
            logger.debug('Set section widget for %s, language: %s',
                         section_label, section.tr.language)
            if section_label not in section_widgets:
                section_widget = make_section_widget(section_label, section)
                section_widgets[section_label] = section_widget
                _form_ui.scroll_section_content_layout.addWidget(section_widget,
                                                                 0,
                                                                 QtCore.Qt.AlignTop)
            else:
                section_widget = section_widgets[section_label]
            logger.debug('set_section_ui, show widget of %s, ',
                         section_label)
            section_widget.show()

            #_form_ui.sections_stack.setCurrentWidget(section_widget)
            #_form_ui.scroll_section.setWidget(section_widget)
            #
            # self.stacked.addWidget(self.lineedit)
            # except RuntimeError:
            #     from IPython import embed; embed()
            #self.current_section_widget = section_widget
            #self.current_section_widget.show()

            # End of def set_section_ui

        set_section_ui(form.current_section_name, form.current_section)
        _form_ui.title_label.setText(form.tr['title'])

        tab_idx = tab_widget.insertTab(tab_idx, form_widget, tab_name)
        tab_icon = QtGui.QIcon(':/icons/form_input_icon')
        tab_widget.setTabIcon(tab_idx, tab_icon)
        tab_widget.setCurrentIndex(tab_idx)


        radio_language_group = QtWidgets.QButtonGroup(form_widget)
        frame = _form_ui.frame_language_select
        for idx,language in enumerate(sorted(form.tr.supported_languages)):
            radio_button = QtWidgets.QRadioButton(language_abbrev(language),
                                                  frame)
            radio_button.setObjectName("radio_button_" + language)
            _form_ui.language_select_layout.addWidget(radio_button, idx)
            radio_language_group.addButton(radio_button, idx)
            logger.debug('Set radio button for switching language '\
                         'of section %s to %s', form.current_section_name,
                         language)
            class ChoiceProcess:
                def __init__(self, language):
                    self.language = language
                def __call__(self, state):
                    if state:
                        logger.debug('Process language toggle to %s, '\
                                     'current section: %s ', self.language,
                                     form.current_section_name)
                        form.set_language(self.language)
            radio_button.toggled.connect(ChoiceProcess(language))
            if language == form.current_section.tr.language:
                radio_language_group.button(idx).setChecked(True)
        # Set button actions
        def prev_sec():
            # gen_section = lambda : set_section_ui(form.previous_section(),
            #                                       form.to_previous_section())
            # _form_ui.section_widget = \
            #     dict_lazy_setdefault(sections, form.previous_section(),
            #                          gen_section)
            logger.debug('Prev_sec, hide widget of %s, ',
                         form.current_section_name)
            section_widgets[form.current_section_name].hide()
            set_section_ui(form.previous_section(),
                           form.to_previous_section())
            _form_ui.scroll_section.ensureVisible(0, 0)
        _form_ui.button_previous.clicked.connect(prev_sec)

        def next_sec():
            # def gen_section():
            #     gen_section = lambda : set_section_ui(form.next_section(),
            #                                       form.to_next_section())
            # _form_ui.section_widget = \
            #     dict_lazy_setdefault(sections, form.next_section(),
            #                          gen_section)
            logger.debug('Next_sec, hide widget of %s',
                         form.current_section_name)
            section_widgets[form.current_section_name].hide()
            set_section_ui(form.next_section(),
                           form.to_next_section())
            _form_ui.scroll_section.ensureVisible(0, 0)

        _form_ui.button_next.clicked.connect(next_sec)

        def cancel():
            # TODO: adapt question if form is empty
            # TODO: see if init value are actually saved or only user-input?
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Question)
            message_box.setText('The current form entries can be saved '\
                                'for later or discarded. Click on "Cancel" '\
                                'to resume filling the form.')
            message_box.addButton(QtWidgets.QMessageBox.Discard)
            message_box.addButton(QtWidgets.QMessageBox.Cancel)
            message_box.addButton(QtWidgets.QMessageBox.Save)
            result = message_box.exec_()
            if result == QtWidgets.QMessageBox.Discard:
                form.cancel()
            if result != QtWidgets.QMessageBox.Cancel:
                tab_widget.removeTab(tab_idx)

        _form_ui.button_cancel.clicked.connect(cancel)
        cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                              form_widget)
        cancel_shortcut.activated.connect(cancel)

        def submit():
            #.setEnabled(False)
            _form_ui.button_submit.setFocus()
            try:
                form.submit()
            except Exception as e:
                msg = 'Error occured while submitting:\n%s' % repr(e)
                logger.error(msg)
                from IPython import embed; embed()
                message_box = QtWidgets.QMessageBox()
                message_box.setIcon(QtWidgets.QMessageBox.Critical)
                message_box.setText(msg)
                message_box.exec_()
            tab_widget.removeTab(tab_idx)

        _form_ui.button_submit.clicked.connect(submit)


    def close_workbook(self):
        self.logic.close_workbook()
        self.refresh()

    def show_workbook_screen(self):
        self._workbook_ui.tabWidget.clear()
        self.tab_indexes.clear()

        def make_tab_sheet(sh_name, sh):
            sheet_widget = QtWidgets.QWidget()
            _data_sheet_ui = ui.data_sheet_ui.Ui_Form()
            _data_sheet_ui.setupUi(sheet_widget)
            _data_sheet_ui.cell_value_frame.hide()
            if self.logic.workbook.user_role < UserRole.MANAGER:
                _data_sheet_ui.button_edit_entry.hide()

            button_icon = QtGui.QIcon(':/icons/close_icon')
            _data_sheet_ui.button_close.setIcon(button_icon)
            _data_sheet_ui.button_close.clicked.connect(self.close_workbook)

            view_icon = QtGui.QIcon(':/icons/view_icon').pixmap(QtCore.QSize(24,24))
            _data_sheet_ui.label_view.setPixmap(view_icon)

            # button_icon = QtGui.QIcon(':/icons/refresh_icon')
            # _data_sheet_ui.button_refresh.setIcon(button_icon)
            # _data_sheet_ui.button_refresh.clicked.connect(sh.refresh_data)

            model = DataSheetModel(sh)
            sh.notifier.add_watcher('appended_entry', model.update_after_append)
            sh.notifier.add_watcher('entry_set', model.update_after_set)
            sh.notifier.add_watcher('pre_delete_entry', model.update_before_delete)
            sh.notifier.add_watcher('deleted_entry', model.update_after_delete)
            sh.notifier.add_watcher('clear_data', model.update_after_clear)

            _data_sheet_ui.tableView.setModel(model)
            hHeader = _data_sheet_ui.tableView.horizontalHeader()
            hHeader.setMaximumSectionSize(400) # TODO expose param
            #hHeader.setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)

            vHeader = _data_sheet_ui.tableView.verticalHeader()
            #vHeader.setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)

            def resize_table_view(*args, **kwargs):
                _data_sheet_ui.tableView.resizeRowsToContents()
                _data_sheet_ui.tableView.resizeColumnsToContents()

            for notification in ['appended_entry', 'entry_set', 'pre_delete_entry',
                                 'deleted_entry', 'clear_data']:
                sh.notifier.add_watcher(notification, resize_table_view)

            resize_table_view()

            def f_cell_action(idx):
                row_df = model.entry_df(idx)
                column = row_df.columns[idx.column()-(row_df.index.name is not None)]
                action_result, action_label = sh.plugin.action(row_df, column)
                if isinstance(action_result, Form):
                    self.make_form_tab(action_label, model, _data_sheet_ui,
                                       self._workbook_ui.tabWidget,
                                       tab_idx=max(0,self.tab_indexes[sh_name]-1),
                                       form=action_result)
                else:
                    print('action result:', action_result)

            _data_sheet_ui.tableView.doubleClicked.connect(f_cell_action)

            def show_details(idx):
                _data_sheet_ui.cell_value.setText(model.data(idx))
                _data_sheet_ui.cell_value_frame.show()

            _data_sheet_ui.tableView.clicked.connect(show_details)

            def f_edit_entry():
                idx = _data_sheet_ui.tableView.currentIndex()
                entry_id = model.entry_id(idx)
                logger.debug('set_entry: idx.row=%s, entry_id=%s',
                             idx.row(), entry_id)
                self.make_form_tab(sh_name, model, _data_sheet_ui,
                                   self._workbook_ui.tabWidget,
                                   tab_idx=self.tab_indexes[sh_name]+1,
                                   form=sh.form_set_entry(entry_id))

            def f_delete_entry():
                idx = _data_sheet_ui.tableView.currentIndex()
                entry_id = model.entry_id(idx)
                logger.debug('delete_entry: idx.row=%s, entry_id=%s',
                             idx.row(), entry_id)
                sh.delete_entry(entry_id)

            if sh.form_master is not None: #TODO: and user is admin
                _data_sheet_ui.button_edit_entry.clicked.connect(f_edit_entry)
            else:
                _data_sheet_ui.button_edit_entry.hide()

            f_new_entry = lambda : \
                self.make_form_tab(sh_name, model, _data_sheet_ui,
                                   self._workbook_ui.tabWidget,
                                   tab_idx=self.tab_indexes[sh_name]+1,
                                   form=sh.form_new_entry())

            if sh.form_master is not None and \
               self.logic.workbook.has_write_access: #TODO: and user is admin
                _data_sheet_ui.button_new_entry.clicked.connect(f_new_entry)
                (_data_sheet_ui.button_delete_entry
                 .clicked.connect(f_delete_entry))
                # new_entry_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("N"),
                #                                      sheet_widget)
                # new_entry_shortcut.activated.connect(f_new_entry)
            else:
                _data_sheet_ui.button_new_entry.hide()


            _data_sheet_ui.comboBox_view.addItems(list(sh.views.keys()))
            _data_sheet_ui.comboBox_view.setCurrentText(sh.default_view)
            f = SheetViewChanger(_data_sheet_ui.comboBox_view, model)
            _data_sheet_ui.comboBox_view.currentIndexChanged.connect(f)

            self.tab_indexes[sh_name] = (self._workbook_ui.tabWidget
                                         .addTab(sheet_widget, sh_name))

            def make_form_editor(tab_widget, sheet, check_on_close):
                tab_closer = EditorTabCloser(tab_widget, check_on_close)
                try:
                    sheet_io = FormEditorSheetIO(sheet, close_callback=tab_closer)
                except FormEditionNotAvailable:
                    return
                editor_widget = FormEditor(sheet_io, parent=tab_widget)
                tab_label = '%s | Form edit' % sh_name
                tab_idx = tab_widget.addTab(editor_widget, tab_label)
                tab_closer.set_editor_tab(editor_widget)
                icon_style = QtWidgets.QStyle.SP_FileDialogListView
                tab_icon = QtGui.QIcon(':/icons/editor_icon')
                tab_widget.setTabIcon(tab_idx, tab_icon)
                tab_widget.setCurrentIndex(tab_idx)

            f_form_editor = partial(make_form_editor, self._workbook_ui.tabWidget,
                                    sh, self.workbook_screen.check_on_close)
            _data_sheet_ui.button_edit_form.clicked.connect(f_form_editor)

            _data_sheet_ui.button_edit_plugin.clicked.connect(
                lambda: self.make_text_editor(self._workbook_ui.tabWidget,
                                              sh_name,
                                              sh.get_plugin_code(),
                                              'python',
                                              lambda s : sh.set_plugin(s, overwrite=True)))

            if self.logic.workbook.user_role < UserRole.ADMIN:
                _data_sheet_ui.button_edit_plugin.hide()
            if self.logic.workbook.user_role < UserRole.ADMIN or \
               sh.form_master is None:
                _data_sheet_ui.button_edit_form.hide()
                _data_sheet_ui.button_delete_entry.hide()

            for form_id, form in sh.live_forms.items():
                logger.info('Load pending form "%s" (%s)',
                            form.tr['title'], form_id)
                self.make_form_tab(sh_name, model, _data_sheet_ui,
                                   self._workbook_ui.tabWidget,
                                   self.tab_indexes[sh_name]+1, form)

        if len(self.logic.workbook.sheets) > 0:
            # TODO: handle tab order
            # TODO: load pending forms
            # TODO: attach file change watcher to datasheet -> trigger refresh when change
            for sheet_name, sheet in self.logic.workbook.sheets.items():
                if self.logic.workbook.user_role >= sheet.access_level:
                    logger.info('Load sheet %s in UI', sheet_name)
                    make_tab_sheet(sheet_name, sheet)
                else:
                    logger.info('Sheet %s not loaded in UI because user role %s < %s',
                                sheet_name, self.logic.workbook.user_role,
                                sheet.access_level)
        self.workbook_screen.setWindowTitle(self.logic.workbook.label)
        self.workbook_screen.show()

        return self.workbook_screen

    def show(self):
        self.current_widget.show()

    def refresh(self):
        self.current_widget.hide()
        logger.debug('Current logic state: %s',
                     PiccelLogic.STATES[self.logic.state])
        self.current_widget = self.screen_show[self.logic.state]()

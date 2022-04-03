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
from traceback import format_stack, format_exc
import csv
from packaging import version

from . import sheet_plugin_template
from . import workbook_plugin_template
from .plugin_tools import map_set, And, Or #, Less, LessEqual, Greater, GreaterEqual
from .plugin_tools import DATE_FMT, DATETIME_FMT
from .plugin_tools import (LescaDashboard, InterviewTracker,
                           form_update_or_new,
                           DEFAULT_INTERVIEW_PLAN_SHEET_LABEL,
                           PollTracker, EmailledPollTracker,
                           ParticipantStatusTracker)

from .form import (Form, FormSection, FormItem, FormSheetEditor,
                   NotEditableError, DateTimeCollector, LanguageError,
                   FormWidget, FormFileEditor, FormItemKeyNotFound)

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
from .ui.widgets import (show_critical_message_box, show_info_message_box,
                         PasswordEdit)

from .core import (LazyFunc, df_index_from_value, if_none, on_str,
                   refresh_text, strip_indent)

from .core import UserRole, nexts, InputType
from .core import Hint, Hints
from .core import (FormEditionBlockedByPendingLiveForm, FormEditionLocked,
                   FormEditionNotOpen, FormEditionLockedType,
                   FormEditionOrphanError, FormEditionCancelled, SheetNotFound)

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

    # TODO: deprecate key -- not safe to store it
    #       Always rely on password, use password manager if needed
    def __init__(self, password, salt_bytes=None, key=None, get_password=None):
        self.get_password = get_password

        if key is None:
            self.salt_bytes = if_none(salt_bytes, os.urandom(32))
            self.key = derive_key(password, self.salt_bytes)
        else:
            self.key = key
            self.salt_bytes = salt_bytes
        self.fernet = Fernet(self.key)

    def set_password_input_func(self, password_func):
        self.get_password = password_func

    def get_key(self):
        return self.key.decode()

    @staticmethod
    def from_key(key_str, salt_bytes):
        return Encrypter(None, salt_bytes, key_str.encode())

    def encrypt_str(self, content_str):
        if self.salt_bytes is not None:
            salt_hex = self.salt_bytes.hex()
        else:
            raise Exception('salt undefined')
        logger.debug2('Encryption - save salt %s', salt_hex)
        return json.dumps({
            'salt_hex' : salt_hex,
            'crypted_content' :  (self.fernet.encrypt(content_str.encode())
                                  .decode())
        })

    def decrypt_to_str(self, crypted_str):
        old_format = False
        try:
            content = json.loads(crypted_str)
        except json.JSONDecodeError:
            logger.warning('Error loading json. Trying old encryption format.')
            content = {
                'salt_hex' : None,
                'crypted_content' :  crypted_str
            }
            old_format = True

        if not old_format and 'salt_hex' not in content:
            raise IOError('Bad format')

        if not old_format and self.salt_bytes is not None and \
           self.salt_bytes.hex() != content['salt_hex']:
            if self.salt_bytes is None:
                logger.warning('Different salt found in content to decrypt. '\
                               'Resquest password to build encryption key again.')
            else:
                logger.warning('No salt found in content to decrypt. '\
                               'Resquest password to build encryption key again.')
            if self.get_password is None:
                raise IOError('Cannot decrypt because cannot get password again')
            else:
                loaded_salt_bytes = bytes.fromhex(content['salt_hex'])
                key = derive_key(self.get_password(), loaded_salt_bytes)
                fernet = Fernet(key)
        else:
            fernet = self.fernet

        return fernet.decrypt(content['crypted_content'].encode()).decode()

class UnknownUser(Exception): pass
class InvalidPassword(Exception): pass
class PasswordReset(Exception): pass

def hash_password(password_str):
    return bcrypt.hashpw(password_str.encode('utf-8'),
                         bcrypt.gensalt()).decode('utf-8')

def password_is_valid(password_str, password_hash_str):
    return bcrypt.checkpw(password_str.encode('utf-8'),
                          password_hash_str.encode('utf-8'))

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
    def from_file(pwd_fn, salt_hex=None):
        if not op.exists(pwd_fn):
            logger.warning('Password file %s does not exist. Create one '\
                           'and add generated salt.' %pwd_fn)
            salt_hex = (salt_hex if salt_hex is not None
                        else os.urandom(32).hex())
            with open(pwd_fn, 'w') as fout:
                json.dump({PasswordVault.SALT_HEX_KEY : salt_hex,
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
        salt = bytes.fromhex(self.vault[PasswordVault.SALT_HEX_KEY])
        if key is None:
            self.check(user, password_str)

            logger.debug('Return encrypter using password and salt %s',
                         salt)
            encrypter = Encrypter(password_str, salt)
        else:
            logger.debug('Return encrypter from key')
            encrypter = Encrypter.from_key(key, salt_bytes=salt)
        return encrypter

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
    try:
        exec(code, module.__dict__)
    except:
        logger.error('Error while importing code:\n%s\nError:\n%s',
                     code, format_exc())
        raise
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

    def is_encrypted(self):
        return self.encrypter is not None

    def enable_track_changes(self, state=True):
        self.track_changes = state
        self.current_stats = self.file_stats()

    def file_stats(self, subfolder=''):
        """ reset file stats (remove change tracking) """
        stats = {}
        if self.track_changes:
            root = op.join(self.root_folder, subfolder)
            for wroot, dirs, files in os.walk(root):
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

    def accept_all_changes(self, subfolder=''):
        if subfolder == '':
            self.current_stats = {}
        self.current_stats.update(self.file_stats(subfolder=subfolder))

    def change_dir(self, folder, track_changes=False):
        """ Note: change tracking will be reset """
        if not self.exists(folder):
            raise IOError('%s does not exist' % folder)
        logger.debug('Create new filesystem with root %s' % folder)
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
                self.current_stats.pop(fn, None)

        logger.debug2('Remove folder %s', full_folder)
        shutil.rmtree(full_folder)

    def copy_to_tmp(self, fn, decrypt=False, tmp_dir=None, dest_afn=None):
        """ Return destination temporary file """
        if dest_afn is None:
            if tmp_dir is None:
                tmp_dir = tempfile.mkdtemp()
            tmp_fn = op.join(tmp_dir, op.basename(fn))
        else:
            tmp_fn = dest_afn
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

    def load(self, fn, crypted_content=True):
        afn = op.join(self.root_folder, fn)

        with open(afn, 'r') as fin:
            content_str = fin.read()

        if crypted_content and self.encrypter is not None:
            content_str = self.encrypter.decrypt_to_str(content_str)
        return content_str

class SheetUnsetUserError(Exception): pass
class InvalidSheetPlugin(Exception): pass
class InvalidSheetLabel(Exception): pass
class NoFormMasterError(Exception): pass
class NoPluginFileError(Exception): pass
class UndefinedUser(Exception): pass
class NonEmptyDataSheetError(Exception): pass
class LiveFormsPendingError(Exception): pass
class MasterFormLockError(Exception): pass

class Unformatter:
    def __init__(self, form, key, na_value=pd.NA):
        self.form = form
        self.key = key
        self.na_value = na_value
    def __call__(self, v):
        return self.form.unformat(self.key, v) if v!='' else self.na_value

from .sheet_plugin import SheetPlugin, UserSheetPlugin

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

class DataSheetSetupDialog(QtWidgets.QDialog):
    def __init__(self, sheet, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)

        self.setWindowTitle("Setup sheet %s" % sheet.label)
        self.sheet = sheet

        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        self.layout = QtWidgets.QVBoxLayout()
        # self.layout.addWidget(self.form_widget)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

    @staticmethod
    def edit_sheet(sheet, parent=None):
        dialog = DataSheetSetupDialog(sheet)
        result = dialog.exec_()
        if result == QtWidgets.QDialog.Accepted:
            return dialog.sheet
        else:
            return None

def if_plugin_valid(f):
    def wrapper(*args):
        if args[0].plugin_is_valid():
            return f(*args)
        else:
            logger.warning('Cannot call %s for sheet %s because plugin '\
                           'is invalid', f.__name__, args[0].label)
    return wrapper


class DictStrEditorWidget(QtWidgets.QWidget):
    def __init__(self, data_dict, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.formLayout = QtWidgets.QFormLayout(self)
        self.formLayout.setContentsMargins(4, 4, 9, 4)
        self.formLayout.setObjectName("formLayout")

        self.fields = {}
        for irow, (key, value) in enumerate(data_dict.items()):
            label = QtWidgets.QLabel(self)
            label.setText(key)
            self.formLayout.setWidget(irow+1, QtWidgets.QFormLayout.LabelRole,
                                      label)
            field = QtWidgets.QLineEdit(self)
            assert(value is None or isinstance(value, str))
            field.setText(if_none(value, ''))
            self.formLayout.setWidget(irow+1, QtWidgets.QFormLayout.FieldRole,
                                      field)
            self.fields[key] = field

    def get_dict(self):
        def none_if_empty(s):
            return s if len(s) > 0 else None
        return {k : none_if_empty(f.text()) for k,f in self.fields.items()}

class DataSheet:
    """
    Table data where entries where input is done with an associated form.
    Provide different views of the data table.
    Notify on data change.
    """
    CSV_SEPARATOR = '\t'
    DATA_FILE_EXT = '.csv'

    SHEET_LABEL_RE = re.compile('^[A-Za-z._-]+$')

    def __init__(self, label, form_master=None, df=None, user=None,
                 filesystem=None, live_forms=None, watchers=None,
                 workbook=None, plugin_code_str=None, user_role=None):
        """
        filesystem.root is the sheet-specific folder where to save all data
        and pending forms.
        ASSUME: all given objects are consistent with files in filesystem.
        Nothing is loaded or saved here.
        To initialise a DataSheet from files see method from_files
        To save logic to files see see method save_logic
        To save live data to files see see method save_live_data

        Tracking of file changes is reset here.
        """

        # TODO: check consistency between access level and given user role

        self.label = DataSheet.validate_sheet_label(label)

        if df is not None and form_master is None:
            raise Exception('Form master cannot be None if df is given')

        if form_master is not None and form_master.is_empty():
            logger.info('Form master associated to sheet %s is empty. '\
                        'It will be ignored.', self.label)
            form_master = None
        self.form_master = form_master
        self.live_forms = live_forms if live_forms is not None else {}
        self.user = user
        self.user_role = if_none(user_role, UserRole.VIEWER)

        self.filesystem = None
        if filesystem is not None:
            self.filesystem = filesystem
            if not self.filesystem.exists('master_form_alternates'):
                self.filesystem.makedirs('master_form_alternates')
            fs_label = DataSheet.get_sheet_label_from_filesystem(self.filesystem)
            if fs_label != self.label:
                raise InvalidSheetLabel('Sheet label (%s) is not the same as '\
                                        'containing folder (%s)' % \
                                        (self.label, fs_label))
            if not self.filesystem.exists('master_form_locks'):
                logger.info('Sheet %s: Create master form locks folder',
                            self.label)
                self.filesystem.makedirs('master_form_locks')

        self.has_write_access = (self.filesystem.test_write_access() \
                                 if self.filesystem is not None else False)

        self.default_view = 'full'
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

        # if self.filesystem is not None:
        #     self.reload_all_data()
        #     self.load_live_forms()

        self.workbook = workbook
        plugin_code_str = (plugin_code_str if plugin_code_str is not None
                           else inspect.getsource(sheet_plugin_template))
        self.set_plugin_from_code(plugin_code_str)

    @if_plugin_valid
    def access_level(self):
        return self.plugin.access_level()

    def set_user(self, user, user_role):
        self.user = user
        self.user_role = user_role
        self.live_forms.clear()
        self.load_live_forms()

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

    def change_filesystem(self, fs, save_logic=False, save_live_data=False):
        self.filesystem = fs
        self.filesystem.enable_track_changes()
        self.has_write_access = self.filesystem.test_write_access()
        if save_logic:
            self.save_logic()
        if save_live_data:
            self.save_live_data()

    @if_plugin_valid
    def set_workbook(self, workbook):
        self.plugin.set_workbook(workbook)

    @staticmethod
    def from_files(user, filesystem, user_role=None, watchers=None,
                   workbook=None):
        filesystem = filesystem.clone()
        filesystem.enable_track_changes()

        label = DataSheet.get_sheet_label_from_filesystem(filesystem)
        logger.debug('Load form master for sheet %s', label)
        form_master = DataSheet.load_form_master(filesystem)
        logger.debug('Create sheet %s for user %s, using filesystem(root=%s)',
                     label, user, filesystem.full_path(filesystem.root_folder))
        plugin_code = DataSheet.load_plugin_code_from_file(filesystem)
        sheet = DataSheet(label, form_master=form_master, df=None, user=user,
                          user_role=user_role, filesystem=filesystem,
                          watchers=watchers, workbook=workbook,
                          plugin_code_str=plugin_code)
        sheet.reload_all_data()
        sheet.load_live_forms()
        return sheet

    def base_views(self):
        return {'full' : lambda ddf: ddf,
                'latest' : self.latest_update_df}

    def latest_update_df(self, df=None):
        if df is None:
            df = self.df
            # fm = lambda x : x.loc[[x.index.max()]]
            # latest = df.groupby(level=0, group_keys=False).apply(fm)

        latest = self.empty_df_from_master()
        if df is not None:
            latest = df.groupby(level=0, group_keys=False).tail(1).sort_index()
        return latest

    def get_plugin_code(self):
        return self.plugin_code_str

    @staticmethod
    def load_plugin_code_from_file(filesystem):
        plugin_fn = 'plugin.py'
        plugin_code_str = None
        if filesystem.exists(plugin_fn):
            logger.info('Load plugin from %s', filesystem.full_path(plugin_fn))
            plugin_code_str = filesystem.load(plugin_fn)
        else:
            logger.info('No plugin to load because %s does not exists',
                        filesystem.full_path(plugin_fn))
        return plugin_code_str

    def set_plugin_from_code(self, code_str, first_attempt=True):
        """ Code is not saved. See save_plugin_code """
        logger.debug('Sheet %s, set plugin from code', self.label)

        self.plugin_code_str = code_str
        try:
            if code_str is None:
                self.plugin = SheetPlugin(self)
            else:
                self.plugin = (module_from_code_str(code_str)
                               .CustomSheetPlugin(self))

            self.plugin.set_workbook(self.workbook)
            self.plugin.access_level()
            self.plugin.update_watched_sheets()
            self.plugin.update(self, self.df)

            # cached views invalidated there:
            views = self.plugin.views(self.base_views())
            logger.debug('Sheet %s, load plugin views: %s',
                         self.label, ','.join(views))

            if self.form_master is not None:
                first_section = self.form_master[self.form_master
                                                 .first_section()]
                last_key = next(iter(first_section.items[-1].keys))
                self.plugin.hint(last_key, '')

            df_test = self.empty_df_from_master()
            for view in views.values():
                view(df_test)

            self.set_views(views)
            default_view = self.plugin.default_view()
            if default_view is not None:
                self.set_default_view(default_view)

        except Exception as e:
            if first_attempt and self.label == '__users__':
                logger.info('Trying to fix plugin code of sheet __user__')
                self.set_plugin_from_code(UserSheetPlugin.get_code_str(),
                                          first_attempt=False)
            logger.error('Could not load plugin of sheet %s '\
                         'from code:\n%s\nException:\n%s\nStack:\n%s',
                         self.label, code_str, repr(e),
                         format_exc())
            message = ('Could load plugin of sheet %s, exception: %s' %
                       (self.label, repr(e)))
            self.indicate_invalid_plugin(message)
            return

        # There has been an exception during first call but second call
        # call worked so save fixes
        if not first_attempt and self.filesystem is not None:
            self.save_plugin_code(overwrite=True)

        self.indicate_valid_plugin()

    def indicate_valid_plugin(self):
        self.plugin_valid = True
        self.plugin_error_reporting = None
        self.notifier.notify('plugin_valid')

    def indicate_invalid_plugin(self, reporting=None):
        self.plugin_valid = False
        self.plugin = None
        self.plugin_error_reporting = reporting
        self.notifier.notify('plugin_invalid', reporting)

    def plugin_is_valid(self):
        return self.plugin_valid

    @staticmethod
    def ___load_properties_from_file(filesystem):
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

    def ___update_properties(self, properties):
        if 'access_level' in properties:
            self.access_level = properties.pop('access_level')
        self.properties.update(properties)

    def get_property(self, label):
        return self.plugin.get_property(label)

    def ___save_properties(self, overwrite=False):
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
        """ Data is cleared before loading """
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
                    self.delete_all_entries()
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
            self.filesystem.accept_all_changes(data_folder)
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
            logger.debug2('Files externally added: %s', new_files)
            logger.debug2('Files externally modified: %s', modified_files)
            logger.debug2('Files externally deleted: %s', deleted_files)

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
            self.filesystem.accept_all_changes('data')

    def users_with_master_form_lock(self):
        lock_dir = 'master_form_locks'
        lock_fns = self.filesystem.listdir(lock_dir)
        return [self.filesystem.load(op.join(lock_dir, fn)) for fn in lock_fns]

    def get_form_for_edition(self, ignore_edition_locks=False):
        # Insure that there is no pending live forms
        users_with_live_forms = self.users_with_pending_live_forms()
        if len(users_with_live_forms) > 0:
            locking_users = ', '.join(users_with_live_forms)
            logger.error('Form master of sheet %s is locked for edition by %s',
                         self.label, locking_users)
            raise FormEditionBlockedByPendingLiveForm(locking_users)

        if not ignore_edition_locks:
            # Insure that there is no edition lock
            lock_users = self.users_with_master_form_lock()
            if len(lock_users) > 0:
                raise FormEditionLocked(lock_users)

        self.lock_form_master_edition()
        if self.form_master is None:
            return Form(default_language='English',
                        supported_languages=['English', 'French'])
        else:
            return self.form_master.new()

    def get_alternate_master_forms(self):
        return self.filesystem.listdir('master_form_alternates')

    def open_alternate_master_form(self, form_bfn):
        return Form(self.filesystem.load(op.join('master_form_alternates',
                                                 form_bfn)))

    def save_alternate_master_form(self, form_bfn, form):
        logger.info('Save alternate version of form %s as %s (sheet: %s)',
                    form.label, form_bfn, self.label)
        self.filesystem.save(op.join('master_form_alternates', form_bfn),
                             form.to_json(), overwrite=True)

    def get_alternate_form_fn(self):
        date_fmt = '%Y_%m_%d_%Hh%Mm%Ss'
        return '%s_%s' % (datetime.now().strftime(date_fmt),
                          protect_fn(self.user))

    def lock_form_master_edition(self):
        self.filesystem.save(op.join('master_form_locks',
                                     protect_fn(self.user)),
                             self.user, overwrite=True)

    def unlock_form_master_edition(self):
        lock_fn = op.join('master_form_locks', protect_fn(self.user))
        if self.filesystem.exists(lock_fn):
            self.filesystem.remove(lock_fn)

    def close_form_edition(self):
        self.unlock_form_master_edition()

    def save_edited_form(self, edited_form):
        lock_fn = op.join('master_form_locks', protect_fn(self.user))
        if not self.filesystem.exists(lock_fn):
            raise  FormEditionNotOpen()

        if self.df is not None and self.df.shape[0] > 0:

            # Check that existing variables keep the same vtype
            # in the edited form
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

            # Check that the edited form does not create orphan variables
            # (that in current form master but not in new one)
            logger.debug('Variables in current form: %s',
                         list(sorted(current_vtypes)))
            logger.debug('Variables in edited form: %s',
                         list(sorted(edited_vtypes)))
            orphan_variables = set(current_vtypes).difference(edited_vtypes)
            logger.debug('Orphan variables: %s', list(sorted(orphan_variables)))
            if len(orphan_variables) > 0:
                raise FormEditionOrphanError(list(sorted(orphan_variables)))

        self.set_form_master(edited_form, save=True, overwrite=True)

    def ___get_orphan_variables(self, current_vtypes=None):
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
            self.notifier.notify('pre_header_change')
            self.df = self.empty_df_from_master()
            self.notifier.notify('header_changed')
            self.reload_all_data()

    def _remove_from_value_to_index(self, entry_df):
        # TODO utest that value indexes are properly maintained
        # after entry deletion
        entry_cols_set = set(entry_df.columns)
        for cols, value_to_index in self.value_to_index:
            if entry_cols_set.issubset(cols):
                for col_values, df_index in entry_df[list(cols)].groupby():
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

    def save_logic(self, overwrite=False):
        if self.filesystem is None:
            raise IOError('Cannot save logic of sheet %s (no associated '\
                          'filesystem)')

        self.save_form_master(overwrite=overwrite)
        self.save_plugin_code(overwrite=overwrite)

    def export_logic(self, output_dir):
        if self.plugin_code_str is not None:
            plugin_fn = '%s.py' % self.label
            logger.info('Export plugin of sheet %s to %s', self.label,
                        op.join(output_dir, plugin_fn))
            self.filesystem.copy_to_tmp('plugin.py', decrypt=True,
                                        dest_afn=op.join(output_dir, plugin_fn))

        if self.form_master is not None:
            form_fn = '%s.form' % self.label
            logger.info('Export form of sheet %s to %s', self.label,
                        op.join(output_dir, form_fn))
            self.filesystem.copy_to_tmp('master.form', decrypt=True,
                                        dest_afn=op.join(output_dir, form_fn))

    def save_plugin_code(self, overwrite=False):
        if self.plugin_code_str is not None:
            self.filesystem.save('plugin.py', self.plugin_code_str,
                                 overwrite=overwrite)

    def save_live_data(self, overwrite=False):
        if self.filesystem is None:
            raise IOError('Cannot save live data of sheet %s (no associated '\
                          'filesystem)')

        self.save_all_data(overwrite=overwrite)
        for form_id, form in self.live_forms.items():
            for section_name, section in form.sections.items():
                for item in section.items:
                    for key, value_str in item.values_str:
                        self.save_live_form_input(form_id, section_name,
                                                  key, value_str)
    def __save(self, overwrite=False):
        if self.filesystem is None:
            raise IOError('Cannot save data of sheet %s (no associated '\
                          'filesystem)')

        if not self.filesystem.exists('data'):
            self.filesystem.makedirs('data')

        self.save_form_master(overwrite=overwrite)
        self.save_all_data(overwrite=overwrite)
        for form_id, form in self.live_forms.items():
            for section_name, section in form.sections.items():
                for item in section.items:
                    for key, value_str in item.values_str:
                        self.save_live_form_input(form_id, section_name,
                                                  key, value_str)

    def save_all_data(self, entry_df=None, overwrite=False):
        # TODO: admin role + lock !
        if not self.filesystem.exists('data'):
            logger.info('Sheet %s: Create data folder', self.label)
            self.filesystem.makedirs('data')

        if self.df is not None and self.df.shape[0] > 0:
            main_data_fn = 'main.csv'
            logger.info('Sheet %s: Save all data', self.label)
            self.filesystem.save(op.join('data', main_data_fn),
                                 self.df_to_str(self.df.drop(columns='__fn__')),
                                 overwrite=overwrite)

            logger.info('Remove all single data entries of sheet %s',
                        self.label)
            for entry_idx, data_fn in self.df['__fn__'].iteritems():
                if not pd.isna(data_fn):
                    logger.info('Delete file of entry %s: %s',
                                data_fn, entry_idx)
                    self.filesystem.remove(data_fn)
                else:
                    logger.info('No file to delete for entry %s', entry_idx)

            self.df['__fn__'] = pd.NA

    @if_plugin_valid
    def load_live_forms(self):
        if self.user is None:
            return
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
                        print('rmtree fs error')
                        pprint(self.filesystem.current_stats)
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
                    conflict_idx_str = (saved_entries[first_section]
                                        .pop('__conflict_idx__'))
                    submission = (saved_entries[first_section]
                                  .pop('__submission__'))

                    logger.debug2('Loaded from live from %s: '\
                                 '__entry_id__ = %s, __update_idx__ = %s ',
                                  live_form_folder, entry_id_str, update_idx_str)

                    form_id = int(form_id_str) # TODO factorize
                    entry_idx = (entry_id, np.int64(update_idx_str),
                                 np.int64(conflict_idx_str))
                    form_func = {'append' : self.form_new_entry,
                                 'update' : self.form_update_entry,
                                 'set': self.form_set_entry}[submission]
                    live_form = form_func(entry_idx, form_id)

                    # From this point form input saving callback is active
                    for section, entries in saved_entries.items():
                        for key, value_str in entries.items():
                            live_form[section][key].set_input_str(value_str,
                                                                  use_callback=False,
                                                                  force=True)

                    first_section = live_form[live_form.first_section()]
                    (first_section['__entry_id__']
                     .set_input_str(entry_id_str, use_callback=False,
                                    force=True))
                    (first_section['__update_idx__']
                     .set_input_str(update_idx_str, use_callback=False,
                                    force=True))
                    (first_section['__conflict_idx__']
                     .set_input_str(conflict_idx_str, use_callback=False,
                                    force=True))
                    (first_section['__submission__']
                     .set_input_str(submission, use_callback=False,
                                    force=True))

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

        if not self.filesystem.exists('master_form_locks'):
            logger.info('Sheet %s: Create master form locks folder',
                        self.label)
            self.filesystem.makedirs('master_form_locks')

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

    @staticmethod
    def validate_sheet_label(label):
        # DataSheet.SHEET_LABEL_RE.match(label) is None
        if not label.isidentifier():
            raise InvalidSheetLabel("Sheet label %s has invalid format" % \
                                    label)
        return label

    def after_workbook_load(self):
        try:
            self.plugin.after_workbook_load()
        except Exception as e:
            code = '\n'.join('%03d: %s'%(i,l)
                             for i,l in enumerate(self.plugin_code_str.split('\n')))
            logger.error('Error in after_workbook_load for sheet %s. '\
                         'Plugin code:\n%s\nException:\n%s\nStack:\n%s',
                         self.label, code, repr(e), format_exc())
            logger.error('Disable plugin of sheet %s', self.label)
            self.indicate_invalid_plugin(reporting=repr(e))

    @if_plugin_valid
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
                             'Shape %s. Columns: %s', view_label,
                             validity_df.shape, ', '.join(validity_df.columns))
            else:
                logger.warning('Update cached  view validity "%s": None',
                               view_label)
            if self.df is not None:
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
                df[[col]] = df[[col]].applymap(f)

        df = df.reset_index()
        df['__entry_id__'] = df['__entry_id__'].apply(lambda x: hex(x))
        df['__update_idx__'] = df['__update_idx__'].apply(str)
        content = df.to_csv(sep=DataSheet.CSV_SEPARATOR, index=False,
                            quoting=csv.QUOTE_NONNUMERIC)
        return content

    def invalidate_cached_views(self):
        logger.debug('Sheet %s - invalidate cached views', self.label)
        for view in self.views:
            self.cached_views[view] = None
            self.cached_validity[view] = None
            self.cached_inconsistent_entries = None
        self.notifier.notify('views_refreshed')

    @if_plugin_valid
    def get_df_view(self, view_label=None):

        if not self.plugin.all_watched():
            logger.debug('Cannot retrieve view %s for sheet %s because of '\
                         'missing sheets to watch', view_label, self.label)
            return pd.DataFrame(['Missing watched sheets'], columns=['Error'])

        if view_label is None:
            view_label = self.default_view
        cached_views = self.cached_views

        view_df = cached_views[view_label]
        if view_df is None:
            view_df = self.views[view_label](self.df)
            if view_df is not None:
                logger.debug('Sheet %s: Update cached view "%s". Shape %s. '\
                             'Columns: %s', self.label, view_label,
                             view_df.shape,
                             ', '.join(view_df.columns))
                if '__fn__' in view_df.columns:
                    view_df = view_df.drop(columns=['__fn__'])
            else:
                logger.debug('Sheet %s: Update cached view "%s": None',
                             self.label,
                             view_label)
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
            if next((i.allow_None for i in self.form_master.key_to_items[col]),
                    False):
                latest_df.dropna(subset=[col], inplace=True)
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

    def validate_unique(self, key, value, update_idx, entry_id, conflict_idx,
                        ignore_na=False):
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
        if ignore_na:
            tmp_df.dropna(subset=[key], inplace=True)
        duplicate_entry_ids = self.duplicate_entries(tmp_df,
                                                     cols_to_check=[key])
        duplicate_entry_ids.difference_update(self.concurrent_updated_entries(tmp_df))
        duplicate_candidate_ids = [ii[0] for ii in duplicate_entry_ids]
        unique_ok = tmp_entry_df.index[0][0] not in duplicate_candidate_ids
        logger.debug2('Checked if %s is in duplicate candidates %s', entry_id,
                      duplicate_candidate_ids)
        if not unique_ok:
            logger.warning('Value %s for key %s is not unique', value, key)

        return unique_ok

    @if_plugin_valid
    def action(self, entry_df, selected_column):
        return self.plugin.action(entry_df, selected_column)

    @if_plugin_valid
    def hint(self, column, value):
        return self.plugin.hint(column, value)

    @if_plugin_valid
    def show_index_in_ui(self):
        return self.plugin.show_index_in_ui()

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
            # TODO: this should be an internal behavior of form,
            #       not managed outside
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
        form = self._new_form('append', form_id=form_id)
        return self.plugin.form_new_entry(form)

    def form_set_entry(self, entry_idx, form_id=None):
        if not self.has_write_access:
            return None
        entry_dict = self.df.loc[[entry_idx]].to_dict('record')[0]
        form = self._new_form('set', entry_dict=entry_dict, form_id=form_id,
                              entry_id=entry_idx[0], update_idx=entry_idx[1],
                              conflict_idx=entry_idx[2])
        return form

    def _new_form(self, submission, entry_dict=None, entry_id=None,
                  form_id=None, update_idx=np.int64(0),
                  conflict_idx=np.int64(0)):
        if self.user is None:
            raise SheetUnsetUserError()

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
                                             form_id=form_id,
                                             overwrite=True))

        entry_id = entry_id if entry_id is not None else self.new_entry_id()

        form.set_values_from_entry(entry_dict)

        logger.debug2('Sheet %s: set unique validator', self.label)

        form.set_unique_validator(partial(self.validate_unique,
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
            try:
                self.save_live_form_input(form_id, first_section,
                                          '__entry_id__', entry_id_str)
                self.save_live_form_input(form_id, first_section,
                                          '__update_idx__', update_idx_str)
                self.save_live_form_input(form_id, first_section,
                                          '__conflict_idx__', conflict_idx_str)
                self.save_live_form_input(form_id, first_section,
                                          '__submission__', submission)
            except FileExistsError:
                # Happens when live form is reloaded
                pass

        logger.debug2('Sheet %s: call form.set_on_submission', self.label)
        form.set_on_submission(LazyFunc(self.on_submitted_entry, form_id=form_id))
        form.set_on_cancel(LazyFunc(self.clean_live_form, form_id=form_id))

        self.live_forms[form_id] = form

        return form

    # @check_role(UserRole.EDITOR) # TODO
    def save_live_form_input(self, form_id, form_section, item_key, input_str,
                             overwrite=False):
        fn = self.get_live_form_entry_fn(form_id, form_section,
                                         item_key, input_str)
        logger.debug2('Save input of form %d, section "%s" and key "%s" to '\
                     'file %s', form_id, form_section, item_key, fn)
        entry = (form_section, item_key, input_str)
        self.filesystem.save(fn, json.dumps(entry), overwrite=overwrite)

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
                      on_str(partial(', '.join,
                                     (str(fid) for fid in self.live_forms))))

    def add_entry(self, entry_dict, entry_idx, process_entry_df,
                  save_func=None):
        if save_func is None:
            save_func = self.save_single_entry
        if logger.level >= logging.DEBUG:
            logger.debug('Sheet %s: Add entry %s, (keys: %s)',
                         self.label, entry_idx,
                         on_str(partial(','.join, entry_dict.keys())))

        # Convert entry dict to pandas.DataFrame and set index
        idx_arrays = [np.array([entry_idx[0]], dtype=np.int64),
                      np.array([entry_idx[1]], dtype=np.int64),
                      np.array([entry_idx[2]], dtype=np.int64)]
        index = pd.MultiIndex.from_arrays(idx_arrays,
                                          names=('__entry_id__',
                                                 '__update_idx__',
                                                 '__conflict_idx__'))
        entry_df = pd.DataFrame([entry_dict], index=index)
        self.fix_types(entry_df)
        logger.debug('Sheet %s: process addition of entry_df: index=%s, cols=%s',
                     self.label, entry_df.index.name,
                     on_str(partial(','.join, entry_df.columns)))

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
                          'filesystem)', self.label,
                          on_str(entry_df.index.to_list))
        return None

    def add_new_entry(self, entry_dict):
        form = self.form_new_entry()
        form.set_values_from_entry(entry_dict)
        form.submit()
        return form

    def append_entry(self, entry_dict, entry_idx=None):
        if entry_idx is None:
            entry_idx = (self.new_entry_id(), 0, 0)
        self.add_entry(entry_dict, entry_idx, self._append_df)

    def delete_all_entries(self):
        self.notifier.notify('pre_clear_data')
        self.df.drop(self.df.index, inplace=True)
        self.notifier.notify('cleared_data')

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
                self.save_all_data(overwrite=True)

        # TODO: update conflit idx!
        self.resolve_conflicting_entries(entry_idx)
        self.invalidate_cached_views()
        self.notifier.notify('deleted_entry', entry_df=deleted_entry)

    def set_entry(self, entry_dict, entry_idx):
        """ WARNING: this is an admin feature, not conflict-free! """
        self.add_entry(entry_dict, entry_idx, self.set_entry_df,
                       save_func=partial(self.save_all_data, overwrite=True))

    def fix_types(self, df):

        # dkeys = self.form_master.datetime_keys
        # datetime_cols = list(set(entry_df.columns).intersection(dkeys))
        # other_cols =  list(set(entry_df.columns).difference(dkeys))
        # entry_df[other_cols] = entry_df[other_cols].fillna(pd.NA)
        # entry_df[datetime_cols] = entry_df[datetime_cols].fillna(pd.NaT)

        # TODO: fix date types
        master_df = self.empty_df_from_master()
        master_cols = set(master_df.columns)

        for extra_col in master_cols.difference(df.columns):
            master_dt_col = master_df.dtypes[extra_col]
            if master_dt_col.name.startswith('float'):
                df[extra_col] = np.nan
            elif master_dt_col.name.startswith('date'):
                df[extra_col] = pd.NaT
            else:
                df[extra_col] = pd.NA
            df[extra_col] = df[extra_col].astype(master_dt_col)

        for col in df.columns:
            dt_col = df.dtypes[col]
            master_dt_col = master_df.dtypes[col]
            logger.debug2('Check type of %s', col)
            if dt_col.name != master_dt_col.name:
                logger.debug2('Inconsistent type: %s (master: %s)',
                              dt_col.name, master_dt_col.name)
                if master_dt_col.name.startswith('float'):
                    tmp = pd.Series(np.zeros(df[col].shape[0]),
                                    dtype=master_dt_col,
                                    index=df[col].index)
                    m_na = pd.isna(df[col])
                    tmp[~m_na] = df[col].to_numpy()[(~m_na).to_numpy()]
                    tmp[m_na] = np.nan
                    df[col] = tmp
                elif master_dt_col.name.startswith('date'):
                    df[col].fillna(pd.NaT)
                    df[col] = df[col].astype(master_dt_col)
                else:
                    df[col] = df[col].astype(master_dt_col)
                    df[col].fillna(pd.NA)

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

        self.fix_types(entry_df)

        prev_dtypes = self.df.dtypes.copy()
        logger.debug2('Sheet %s, dtypes before addition: %s', self.label,
                     self.df.dtypes)
        self.df = pd.concat((self.df, entry_df), join='outer')
        logger.debug2('Sheet %s, dtypes after addition: %s', self.label,
                     self.df.dtypes)
        # if any(new_dtype.name != prev_dtypes[col].name
        #        for col, new_dtype in self.df.dtypes.items()):
        #     logger.warning('dtype changed ... fixing ...')
        #     self.fix_types(self.df)

        for col, new_dtype in self.df.dtypes.items():
            if prev_dtypes[col].name != new_dtype.name:
                msg = ('dtype changed for %s: was %s, now %s' % 
                       (col, prev_dtypes[col].name, new_dtype.name))
                logger.error(msg)
                raise TypeError(msg)

        self.df.sort_index(inplace=True)
        idx_to_track = entry_df.index[0]
        entry_index = self.fix_conflicting_entries(index_to_track=idx_to_track)
        logger.debug2('Entry index after fixing: %s', entry_index)
        logger.debug2('Entry has been appended to sheet %s', self.label)
        logger.debug2('Resulting df has columns: %s)',
                      on_str(partial(','.join, self.df.columns)))
        self.invalidate_cached_views()
        logger.debug("Sheet %s notifies 'appended_entry'", self.label)
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
        logger.setLevel(logging.DEBUG)
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
            ('Age', pd.array([22, 50, pd.NA], dtype=pd.Int64Dtype())),
            ('Taille', [np.nan, 1.7, 1.7]),
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
        self.filesystem = LocalFileSystem(self.sheet_folder,
                                          track_changes=True)
        self.sheet = DataSheet(self.sheet_id, form, None,
                               self.user, self.filesystem)

        self.sheet_ts = DataSheet(self.sheet_id,
                                  Form.from_dict(self.form_def_ts_data),
                                  self.data_df_ts_data,
                                  self.user, self.filesystem)
        self.sheet_ts.save_logic()
        self.sheet_ts.save_live_data()
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

    def test_module_from_code(self):
        code = \
"""
import numpy as np
def foo():
    return np.array([1])
"""
        module = module_from_code_str(code)
        self.assertEqual(module.foo()[0], 1)

    def test_properties(self):
        class PPSheetPlugin(SheetPlugin):
            def access_level(self):
                return UserRole.MANAGER
            def get_property(self, property_name):
                if property_name == 'lesca_participant_sheet':
                    return True
                return None
        self.sheet_ts.set_plugin_from_code(PPSheetPlugin.get_code_str())
        self.sheet_ts.save_plugin_code(overwrite=True)
        self.assertEqual(self.sheet_ts.access_level(), UserRole.MANAGER)

        self.assertEqual(self.sheet.access_level(), UserRole.VIEWER)
        self.assertIsNone(self.sheet.get_property('unknown_prop'))

        sheet_ts2 = DataSheet.from_files(self.user,
                                         self.sheet_ts.filesystem.clone(), None)
        self.assertEqual(sheet_ts2.access_level(), UserRole.MANAGER)
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
        user_value = form_master['section1']['User'].get_value()
        self.assertTrue(pd.isna(user_value), user_value)
        sheet = DataSheet(sheet_id, form_master, None, user, filesystem)
        form = sheet.form_new_entry()
        user_value = form_master['section1']['User'].get_value()
        self.assertTrue(pd.isna(user_value), user_value)
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

    def test_unique_allow_empty(self):
        form_def = {
            'title' : {'French' : 'Un formulaire'},
            'default_language' : 'French',
            'supported_languages' : {'French'},
            'sections' : {
                'section1' : {
                    'items' : [
                        {'keys' : {'Participant_ID' :
                                   {'French':'Code Participant'}},
                         'allow_empty' : True,
                         'unique' : True,
                        },
                        {'keys' : {'Name' : {'French':'Nom'}}}
                    ]
                }
            }
        }
        data = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['P1', 'P2', None, 'P3']),
            ('__entry_id__',   np.array([0, 1, 2, 2], dtype=np.int64)),
            ('__update_idx__', np.array([0, 0, 0, 1], dtype=np.int64)),
            ('__conflict_idx__', np.array([0, 0, 0, 0], dtype=np.int64)),
            ('Name', ['John', 'Jon', 'Robert', 'Robert']),
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
        form.set_values_from_entry({'Participant_ID' : None})
        self.assertTrue(form.is_valid())
        form.submit()

        logger.debug('utest: create update form')
        form = sheet.form_update_entry(sheet.df.index[3])
        self.assertTrue(form.is_valid())

        logger.debug('-- utest: set PID to P1 in form. Expect duplicate')
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
                        {'keys' : {'Name' : {'French':'Nom'}}},
                        {'keys' : {'Extra' : {'French':'Extra'}}}
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
        form = sheet.form_update_entry((2,1,0))
        self.assertRaises(FormItemKeyNotFound, form.set_values_from_entry,
                          {'Unknown' : 'waza'})

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
        lock_exception_raised = False
        try:
            self.sheet_ts.get_form_for_edition()
        except FormEditionLocked as e:
            self.assertEqual(e.args[0], [self.user])
            lock_exception_raised = True
        self.assertTrue(lock_exception_raised)
        self.sheet_ts.close_form_edition()

        self.assertTrue(self.sheet_ts.get_form_for_edition() is not None)

    def test_form_edition_multiple_locks(self):
        form = self.sheet_ts.get_form_for_edition()
        self.sheet_ts.set_user('another user', UserRole.EDITOR)
        form2 = self.sheet_ts.get_form_for_edition(ignore_edition_locks=True)
        self.assertTrue(form2 is not None)

        lock_exception_raised = False
        try:
            self.sheet_ts.get_form_for_edition()
        except FormEditionLocked as e:
            self.assertEqual(set(e.args[0]), {self.user, 'another user'})
            lock_exception_raised = True
        self.assertTrue(lock_exception_raised)
        self.sheet_ts.close_form_edition() # remove lock for "another user"

        lock_exception_raised = False
        try:
            self.sheet_ts.get_form_for_edition()
        except FormEditionLocked as e:
            self.assertEqual(e.args[0], [self.user])
            lock_exception_raised = True
        self.assertTrue(lock_exception_raised)

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

    def test_form_edition_locked_types_no_data(self):
        sheet_id = 'Empty_Sheet'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder, track_changes=True)
        sheet = DataSheet(sheet_id, Form.from_dict(self.form_def_ts_data),
                          None, self.user, filesystem)

        form_master = sheet.get_form_for_edition()
        form_master['section1'].items[1].vtype = 'text'
        sheet.save_edited_form(form_master)

    def test_form_edition_locked_types_with_existing_data(self):
        form_master = self.sheet_ts.get_form_for_edition()
        form_master['section1'].items[1].vtype = 'text'
        self.assertRaises(FormEditionLockedType,
                          self.sheet_ts.save_edited_form,
                          form_master)

    def test_form_edition_orphan_variable_with_no_data(self):
        sheet_id = 'Empty_Sheet'
        sheet_folder = op.join(self.tmp_dir, sheet_id)
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder, track_changes=True)
        sheet = DataSheet(sheet_id, Form.from_dict(self.form_def_ts_data),
                          None, self.user, filesystem)

        form_master = sheet.get_form_for_edition()
        age_item = form_master['section1'].items[1]
        save_age_item = FormItem(**age_item.to_dict())
        form_master.remove_item('section1', age_item)
        sheet.save_edited_form(form_master)
        sheet.close_form_edition()

        form_master = sheet.get_form_for_edition()
        form_master.add_item('section1', age_item)
        sheet.save_edited_form(form_master)

    def test_form_edition_orphan_variable_with_existing_data(self):
        form_master = self.sheet_ts.get_form_for_edition()
        age_item = form_master['section1'].items[1]
        save_age_item = FormItem(**age_item.to_dict())
        form_master.remove_item('section1', age_item)
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

    def test_bad_plugin_from_file(self):
        sheet_folder = op.join(self.tmp_dir, 'sh_plugin_bad')
        os.makedirs(sheet_folder)
        filesystem = LocalFileSystem(sheet_folder)

        sheet = DataSheet('sh_plugin_bad',
                          Form.from_dict(self.form_def_ts_data),
                          df=self.data_df_ts_data,
                          filesystem=filesystem)
        sheet.plugin_code_str = "baaad"
        sheet.save_logic()
        sheet.save_live_data()

        sheet2 = DataSheet.from_files('me', filesystem)
        self.assertFalse(sheet2.plugin_is_valid())
        self.assertIsNone(sheet2.action(None, None))
        self.assertIsNone(sheet2.plugin)
        self.assertIsNone(sheet2.get_df_view())

        # Fix plugin:
        sheet2.set_plugin_from_code(SheetPlugin.get_code_str())
        self.assertTrue(sheet2.plugin_is_valid())

        form, action_label = sheet2.action(sheet2.df.loc[[(0,0,0)]],
                                           'Participant_ID')
        self.assertEqual(action_label, '%s | update' % sheet2.label)
        self.assertTrue(sheet2.plugin is not None)
        self.assertTrue(sheet2.get_df_view() is not None)

    def test_plugin_reload(self):

        class Plugin1(SheetPlugin):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                logger.debug('Plugin 1.init')
                self.df = pd.DataFrame(['init p1'], columns=['Field'])

            def update(self, sheet_source, changed_entry,
                       deletion=False, clear=False):
                logger.debug('Plugin 1.update(sheet_source=%s,\n' \
                             '                changed_entry=%s,\n' \
                             '                deletion=%s,\n' \
                             '                clear=%s)',
                             sheet_source, changed_entry, deletion, clear)
                self.df.iat[0,0] = 'plugin 1 was here'

            def views(self, views):
                return {'full' : lambda df: self.df}
        self.sheet_ts.set_plugin_from_code(Plugin1.get_code_str())

        self.assertEqual(self.sheet_ts.get_df_view().iat[0,0], 'plugin 1 was here')


        class Plugin2(SheetPlugin):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                logger.debug('Plugin 2.init')
                self.df = pd.DataFrame(['init p2'], columns=['Field'])

            def update(self, sheet_source, changed_entry,
                       deletion=False, clear=False):
                logger.debug('Plugin 2.update(sheet_source=%s,\n' \
                             '                changed_entry=%s,\n' \
                             '                deletion=%s,\n' \
                             '                clear=%s)',
                             sheet_source, changed_entry, deletion, clear)
                self.df.iat[0,0] = 'plugin 2 was here'

            def views(self, views):
                return {'full' : lambda df: self.df}
        self.sheet_ts.set_plugin_from_code(Plugin2.get_code_str())

        self.assertEqual(self.sheet_ts.get_df_view().iat[0,0], 'plugin 2 was here')

    def test_plugin_views(self):
        # TODO: test against all versions of plugin API (may change overtime)

        class TestViewSheetPlugin(SheetPlugin):
            def views(self, base_views):
                base_views.update({'young' : lambda df: df[df.Age<50]})
                return base_views
            def default_view(self):
                return 'latest'
            def view_validity(self, df, view):
                return pd.DataFrame(index=df.index, columns=df.columns,
                                    data=np.ones(df.shape, dtype=bool))

        self.sheet_ts.set_plugin_from_code(TestViewSheetPlugin.get_code_str())

        df_young = self.sheet_ts.get_df_view('young')
        mask = df_young.Participant_ID=='CE0004'
        self.assertEqual(df_young.loc[mask, 'Age'].values[0], 22)
        validity = self.sheet_ts.view_validity('young')
        self.assertEqual(validity.shape, df_young.shape)
        self.assertTrue((validity.dtypes == bool).all())

    def test_validity(self):
        class ValiditySheetPlugin(SheetPlugin):

            def views(self, base_views):
                return base_views

            def default_view(self):
                return 'latest'

            def view_validity(self, df, view):
                validity = pd.DataFrame(index=df.index, columns=df.columns,
                                        dtype=bool)
                col = 'Taille'
                validity[col] = ~df[col].duplicated(keep=False).to_numpy()
                return validity

        self.sheet_ts.set_plugin_from_code(ValiditySheetPlugin.get_code_str())

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

        view = self.sheet_ts.get_df_view('full')
        validity = self.sheet_ts.view_validity('full')
        expected_validity = pd.DataFrame(data=np.ones(view.shape, dtype=bool),
                                         index=view.index, columns=view.columns)
        expected_validity['Taille'] = [True, False, False, True]
        assert_frame_equal(validity, expected_validity)

        self.sheet_ts.invalidate_cached_views()
        view = self.sheet_ts.get_df_view('full')
        validity = self.sheet_ts.view_validity('full')
        expected_validity = pd.DataFrame(data=np.ones(view.shape, dtype=bool),
                                         index=view.index, columns=view.columns)
        expected_validity['Taille'] = [True, False, False, True]
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
        form, alabel = self.sheet_ts.action(self.sheet_ts.df.iloc[[1]],
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
        sh2 = DataSheetFormHook.from_files(self.user, self.filesystem)

        self.assertFalse(sh2.filesystem.exists(sh2.get_live_form_folder(form_id)))

    def test_refresh_sheet(self):
        sheet_ts2 = DataSheet(self.sheet_id,
                              Form.from_dict(self.form_def_ts_data),
                              self.data_df_ts_data,
                              self.user, self.filesystem.clone())
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
    State: Decrypt
        - decrypt workbook with password -> Login
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
        self.workbook.decrypt(access_pwd)
        self.state = PiccelLogic.STATE_LOGIN

    def get_user_names(self):
        last_user = self.system_data.get_last_user()
        users = self.workbook.get_users()
        if last_user is not None and last_user in users:
            last_user = [last_user]
        else:
            last_user = []
        return last_user + [u for u in users if len(last_user)==0 or \
                            u != last_user[0]]

    def get_user_role(self, user):
        return self.workbook.get_user_role(user)

    def get_security_word(self, user):
        return self.workbook.get_security_word(user)

    def password_reset_needed(self, user):
        return self.workbook.password_reset_needed(user)

    def check_access_password(self, password_str):
        return self.workbook.access_password_is_valid(password_str)

    def check_user_password(self, user, password_str):
        return self.workbook.user_password_is_valid(user, password_str)

    def set_user_password(self, user, password_str):
        return self.workbook.set_user_password(user, password_str)

    def cancel_access(self):
        self.cancel_login()

    def cancel_login(self):
        self.filesystem = None
        self.cfg = None
        self.workbook = None
        self.state = PiccelLogic.STATE_SELECTOR

    def login(self, user, pwd, user_role=None, progression_callback=None):
        """
        Create encrypter using given access password.
        Load workbook using given user.
        """

        self.workbook.user_login(user, pwd, user_role=user_role,
                                 progress_callback=progression_callback)

        logger.debug('Record that last user is %s', user)
        self.system_data.set_last_user(user)

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
        self.access_pwd = '1234'
        self.admin_pwd = '5425'
        self.admin_user = 'thomas'
        wb_label = 'Test_WB'
        wb = WorkBook.create(wb_label, filesystem,
                             access_password=self.access_pwd,
                             admin_password=self.admin_pwd,
                             admin_user=self.admin_user)
        self.cfg_bfn = protect_fn(wb_label) + '.psh'

        sh_users = wb['__users__']
        for user, role, pwd in [('simon' , UserRole.EDITOR, 'pwd_simon'),
                                ('catherine' , UserRole.MANAGER, 'pwd_cath'),
                                ('guest' , UserRole.VIEWER, 'pwd_guest')]:
            sh_users.add_new_entry({'User_Name' : user, 'Role' : role.name,
                                    'Security_Word' : 'yata ' + user})
            wb.set_user_password(user, pwd)

    def tearDown(self):
        self.udata.clear()
        shutil.rmtree(self.tmp_dir)

    def test_selector(self):
        sheeter = PiccelLogic(self.udata)
        self.assertEqual(sheeter.state, sheeter.STATE_SELECTOR)
        self.assertEqual(sheeter.get_recent_files(), [])
        filesystem = LocalFileSystem(self.tmp_dir)
        msg = sheeter.load_configuration(filesystem, self.cfg_bfn)
        self.assertEqual(msg, 'ok')
        self.assertEqual(sheeter.state, sheeter.STATE_ACCESS)

    def test_decrypt(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        logic.decrypt(self.access_pwd)
        self.assertEqual(logic.state, logic.STATE_LOGIN)

    def test_login_unknown_user(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        logic.decrypt(self.access_pwd)
        self.assertRaises(UnknownUser, logic.login, 'chouchou', 'bobbie')

    def test_login_invalid_password(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        logic.decrypt(self.access_pwd)
        self.assertRaises(InvalidPassword, logic.login, 'thomas', 'nope')
        self.assertRaises(InvalidPassword, logic.login, 'thomas',
                          self.access_pwd)

    def test_check_passwords(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        self.assertTrue(logic.check_access_password(self.access_pwd))
        logic.decrypt(self.access_pwd)
        self.assertTrue(logic.check_user_password('thomas', self.admin_pwd))
        self.assertTrue(logic.check_user_password('simon', 'pwd_simon'))
        self.assertTrue(logic.check_user_password('guest', 'pwd_guest'))
        self.assertTrue(logic.check_user_password('catherine', 'pwd_cath'))

        self.assertFalse(logic.check_user_password('thomas', 'nope'))
        self.assertFalse(logic.check_user_password('simon', 'nope'))
        self.assertFalse(logic.check_user_password('catherine', 'nope'))
        self.assertFalse(logic.check_user_password('guest', 'nope'))

    def test_last_user_first(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        logic.decrypt(self.access_pwd)
        logic.login('simon', 'pwd_simon')

        filesystem.unset_encrypter()
        logic2 = PiccelLogic(self.udata)
        logic2.load_configuration(filesystem, self.cfg_bfn)
        logic2.decrypt(self.access_pwd)
        self.assertEqual(logic2.get_user_names()[0], 'simon')

    def test_correct_login(self):
        logic = PiccelLogic(self.udata)
        filesystem = LocalFileSystem(self.tmp_dir)
        logic.load_configuration(filesystem, self.cfg_bfn)
        logic.decrypt(self.access_pwd)
        logic.login('thomas', self.admin_pwd)
        logic.login('simon', 'pwd_simon')
        logic.login('guest', 'pwd_guest')
        self.assertIsNotNone(logic.workbook)
        self.assertEqual(logic.state, PiccelLogic.STATE_WORKBOOK)

        # Check:
        #     - user-specific log file exists -> this has to be explicitely enabled
        #     - workbook is loaded

class WorkBookFileError(Exception): pass
class SheetLabelAlreadyUsed(Exception): pass
class SheetDataOverwriteError(Exception): pass
from .core import UnauthorizedRole
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
                                       'must be at least %s' % \
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

class WorkBookExistsError(Exception): pass
class WorkBookLoginError(Exception): pass


roles_tr = {r.name : {language : (r.name[0].upper()+r.name[1:].lower())
                      for language in ['French', 'English']}
            for r in UserRole}

UF_ITEMS = [FormItem({'User_Name' :
                      {'French' : "Nom d'utilisateur.rice",
                       'English' : "User name"}},
                     description={
                         'French' : 'Doit être unique',
                         'English' : 'Must be unique'
                     },
                     allow_empty=False,
                     unique=True,
                     freeze_on_update=True,
                     default_language='French',
                     supported_languages={'French', 'English'}),
            FormItem(keys={'Role':None},
                     description={
                         'French' :
                         ("<ul>" \
                          "<li><i>Viewer:</i> accès en lecture seule" \
                          "<li><i>Editor:</i> soumission de données" \
                          "<li><i>Reviewer:</i> révision des données soumises" \
                          "<li><i>Manager:</i> gestion des utilisateurs, actions de suivi critique (ex: indication d'un drop-out), édition de formulaires" \
                          "<li><i>Admin:</i> édition du code, altération de données" \
                          "</ul>"),
                         'English' :
                         ("<ul>" \
                          "<li><i>Viewer:</i> read-only access" \
                          "<li><i>Editor:</i> submit data" \
                          "<li><i>Reviewer:</i> revise submitted data" \
                          "<li><i>Manager:</i> edit users, critical follow-up actions (ex: indicate a drop-out), edit forms" \
                          "<li><i>Admin:</i> edit code, alter data" \
                          "</ul>")
                     },
                     choices=roles_tr,
                     allow_empty=False,
                     init_values={'Role' : 'EDITOR'},
                     supported_languages={'French', 'English'},
                     default_language='French'),
            FormItem(keys={'Status':{'French' : 'Statut',
                                     'English' : 'Status'}},
                     description={
                         'French' : "Si non actif, l'utilisateur.rice ne pourra pas se connecter au classeur.<br>Utiliser ce statut pour désactiver un accès tout en gardant une trace des accès précédents.<br><b>Important :</b> le cas échéant, <b>désactiver l'accès cloud</b> au répertoire du classeur.",
                         'English' : 'If not active, the user will not be able to connect to the workbook.<br>Use this status to desactivate an access while keeping a trace of previous access.<br><b>Important :</b> If needed, also desactivate access to the folder shared on the cloud.'
                     },
                     choices={'active' : {'French' : 'Actif.ve',
                                          'English' : 'Active'},
                              'non_active' : {'French' : 'Non actif.ve',
                                              'English' : 'Not active'}},
                     allow_empty=False,
                     init_values={'Status' : 'active'},
                     supported_languages={'French', 'English'},
                     default_language='French'),
            FormItem({'Password_Reset' :
                      {'French' : "Réinitialiser le mot de passe",
                       'English' : "Reset password"}},
                     description={
                         'French' : "Si oui, l'utilisateur.rice devra réinitialiser son mot de passe lors de sa prochaine connexion au classeur.",
                         'English' : 'If yes, the user will have to reinitialize their password on their next login into the workbook.'
                     },
                     allow_empty=False,
                     vtype='boolean',
                     choices={'True' : {'French' : 'Oui', 'English' : 'Yes'},
                              'False' : {'French' : 'Non', 'English' : 'No'}},
                     init_values={'Password_Reset' : 'True'},
                     default_language='French',
                     supported_languages={'French', 'English'}),
            FormItem({'Security_Word' :
                      {'French' : "Mot de sécurité",
                       'English' : "Security word"}},
                     description={'French' : "Transmettre ce mot à "\
                                  "l'utilisateur lors de la réinitialisation du mot de passe. Sert à éviter qu'un.e autre utilisateur.rice ne puisse faire la réinitialisation.<br>Doit être unique.",
                                  'English' : "Give this word to the user when reseting their password. It is used to prevent that the reset is done by another user."},
                     allow_empty=False,
                     unique=True,
                     default_language='French',
                     supported_languages={'French', 'English'}),
            FormItem({'Password_Hash' :
                      {'French' : "Mot de passe crypté",
                       'English' : "Crypted password"}},
                     description={'French' : "Stockage d'une version cryptée du mot de passe de l'utilisateur.rice, à des fins de vérification durant la connexion au classeur.<br><b>Ne doit pas être modifié manuellement</b>.",
                                  'English' : "Store a crypted version of the user password, for checking during login.<br><b>Must not be modified manually</b>."},

                     access_level=UserRole.ADMIN,
                     default_language='French',
                     supported_languages={'French', 'English'}),
            FormItem(keys={'User' : None},
                     vtype='user_name',
                     access_level=UserRole.ADMIN,
                     allow_empty=False,
                     supported_languages={'French', 'English'},
                     default_language='French'),
            FormItem(keys={'Timestamp_Submission':None},
                     vtype='datetime', generator='timestamp_creation',
                     supported_languages={'French', 'English'},
                     default_language='French',
                     access_level=UserRole.ADMIN)]
UF_SECTIONS = {'section_main' : \
               FormSection(UF_ITEMS, default_language='French',
                           supported_languages={'French', 'English'})}
USERS_FORM = Form(UF_SECTIONS, default_language='French',
                  supported_languages={'French', 'English'},
                  title={'French': 'Utilisateur du classeur',
                         'English': 'Workbook user'},
                  version='1.20220331')

class InvalidWorbookLabel(Exception): pass
class InvalidJobName(Exception): pass
class JobDisabled(Exception): pass
class JobNotFound(Exception): pass
class InvalidJobCode(Exception):
    def __init__(self, error_message):
        self.error_message = error_message

class InvalidJobs(Exception):
    def __init__(self, invalid_jobs):
        self.invalid_jobs = invalid_jobs
class NoJobInputDefined(Exception): pass

job_source_header = \
"""
import sys
import os
import os.path as op
import pandas as pd
import numpy as np
from piccel import (Job, UserRole, InputType, show_critical_message_box,
                    show_info_message_box)
from piccel.logging import logger
from datetime import datetime

from PyQt5 import QtGui
"""
class JobBase:
    def __init__(self, workbook):
        self.workbook = workbook

    def who_can_run(self):
        return None

    def min_access_level(self):
        return UserRole.ADMIN

    def icon(self):
        return QtGui.QIcon(':/icons/bolt_icon')

    def description(self):
        return None

    def run(self, ask_input, **kwargs):
        pass

class Job(JobBase):

    @classmethod
    def get_code_str(cls):
        return (job_source_header + \
                strip_indent(inspect.getsource(cls)
                             .replace(cls.__name__, 'CustomJob')))

class ExportJob(Job):
    def who_can_run(self):
        return None

    def min_access_level(self):
        return UserRole.MANAGER

    def description(self):
        return 'Export plugin code and form for all sheets'

    def icon(self):
        return QtGui.QIcon(':/icons/settings_export_icon')

    def run(self, ask_input, export_root_dir=None):
        if export_root_dir is None:
            export_root_dir = ask_input('Output folder',
                                        input_type=InputType.FOLDER)
        if export_root_dir is None:
            return

        date_fmt = '%Y_%m_%d_%Hh%Mm%Ss'
        export_dir = op.join(export_root_dir,
                             "%s_%s" % (self.workbook.label,
                                        datetime.now().strftime(date_fmt)))
        if op.exists(export_dir):
            show_critical_message_box("Don't spam this button so hard!")
            return
        else:
            os.makedirs(export_dir)

        self.workbook.export_all_logic(export_dir)
        show_info_message_box('Logic successfully exported to %s' % export_dir)

class WorkBook:
    """
    Workflow:
    - load workbook
    - decryption using access password (self.decrypted is True)
    - login user with role-specific password (self.user is not None)
    """
    ACCESS_KEY = 'data_access'
    SHEET_FOLDER = 'sheets'
    JOBS_FOLDER = 'jobs'
    JOB_EXT = '.py'
    ENCRYPTION_FN = 'encryption.json'

    def __init__(self, label, data_folder, filesystem, password_vault=None,
                 linked_book_fns=None, salt_hex=None, color_hex_str=None):
        """
        Create workbook from basic configuration: where is the main data folder
        and passwords for every role.
        The list of users will be loaded when the woorkbook is decrypted using
        the access password. Data will be loaded when user logs in.

        A workbook can be created from scratch:
        wb = WorkBook('my_wb', 'data_path_relative_to_root ',
                      LocalFileSystem('path_to_root'))
        # TODO helper with more natural path definition:
        wb = WorkBook.create('my_wb', 'data_path', 'cfg_fn')
        # Set access password (saved to data_path/encryption.json):
        wb.set_access_password('access_pwd')

        # Change user status:
        wb.user_update('me', status='inactive')

        # Set password for given role (saved to data_path/encryption.json):
        wb.set_password(UserRole.ADMIN, 'admin_pwd')
        wb.save_configuration_file('../my_wb.psh')
        """
        if not label.isidentifier():
            raise InvalidWorbookLabel(label)

        self.label = label
        # TODO: validate color format
        self.color_hex_str = color_hex_str

        self.filesystem = filesystem

        self.has_write_access = filesystem.test_write_access()
        # TODO: obviously in case no write access, the following will crash...

        if self.filesystem.encrypter is not None:
            logger.warning('Init of workbook %s: Encrypter already associated '\
                           'with filesystem but will be reset after login',
                           label)
        if not filesystem.exists(data_folder):
            logger.info('WorkBook %s: Data folder %s not found, create it',
                        self.label, data_folder)
            filesystem.makedirs(data_folder)

        self.data_folder = data_folder

        sheet_folder = op.join(data_folder, WorkBook.SHEET_FOLDER)
        if not filesystem.exists(sheet_folder):
            logger.info('WorkBook %s: Create sheet subfolder', self.label)
            filesystem.makedirs(sheet_folder)
        self.sheet_folder = sheet_folder

        jobs_folder = op.join(data_folder, WorkBook.JOBS_FOLDER)
        if not filesystem.exists(jobs_folder):
            logger.info('WorkBook %s: Create job subfolder', self.label)
            filesystem.makedirs(jobs_folder)

        if password_vault is None:
            logger.info('WorkBook %s: Create password vault', self.label)
            pwd_rfn = op.join(data_folder, WorkBook.ENCRYPTION_FN)
            pwd_fn = self.filesystem.full_path(pwd_rfn)
            password_vault = PasswordVault.from_file(pwd_fn, salt_hex=salt_hex)
            logger.info('WorkBook %s: Save password vault to %s',
                        self.label, pwd_fn)
            password_vault.save()
        self.password_vault = password_vault

        self.user = None
        self.user_role = None

        self.linked_book_fns = (linked_book_fns if linked_book_fns is not None \
                                else {})
        self.linked_books = []
        self.linked_sheets = []

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
        self.read_only_sheets = {}
        self.jobs = {}
        self.jobs_code = {}
        self.jobs_invalidity = {}

        self.decrypted = False
        self.logged_in = False

    @staticmethod
    def create(label, filesystem, access_password, admin_password,
               admin_user, data_folder=None, salt_hex=None,
               color_hex_str=None):
        data_folder = (data_folder if data_folder is not None
                       else protect_fn(label) + '_files')
        cfg_bfn = protect_fn(label) + '.psh'
        if filesystem.exists(data_folder) or filesystem.exists(cfg_bfn):
            raise WorkBookExistsError()
        wb = WorkBook(label, data_folder, filesystem, salt_hex=salt_hex,
                      color_hex_str=color_hex_str)
        wb.set_access_password(access_password)
        assert(admin_password is not None)
        wb.decrypt(access_password)
        wb.user = admin_user
        wb.user_role = UserRole.ADMIN
        wb.logged_in = True

        sheet_id = '__users__'
        sh1 = DataSheet(sheet_id, USERS_FORM.new(), user=admin_user)
        sh1.set_plugin_from_code(UserSheetPlugin.get_code_str())
        wb.add_sheet(sh1) # TODO insure that logic is properly saved
        sh1.add_new_entry({'User_Name' : admin_user,
                           'Role' : UserRole.ADMIN.name,
                           'Security_Word' : 'azerty',
                           'Password_Reset' : False,
                           'Password_Hash' : hash_password(admin_password)})

        wb.save_configuration_file(cfg_bfn)
        return wb

    def set_job_code(self, job_name, job_code_str, save=False):
        logger.debug('Set code of job %s', job_name)
        success = True
        if not job_name.isidentifier():
            raise InvalidJobName(job_name)

        self.jobs_code[job_name] = job_code_str
        if save:
            self.save_job_code(job_name, job_code_str)
        self.jobs_invalidity.pop(job_name, None)
        try:
            self.jobs[job_name] = self.job_from_code(job_name, job_code_str)
        except InvalidJobCode as e:
            logger.warning('Code of job %s is invalid', job_name)
            self.jobs_invalidity[job_name] = e.args[0]
            success = False
        return success

    def delete_job(self, job_name):
        logger.debug('Delete code of job %s', job_name)
        if job_name not in self.jobs_code:
            raise JobNotFound(job_name)

        self.jobs.pop(job_name, None)
        self.jobs_code.pop(job_name)
        self.jobs_invalidity.pop(job_name, None)
        jobs_folder = op.join(self.data_folder, WorkBook.JOBS_FOLDER)
        self.filesystem.remove(op.join(jobs_folder, '%s.py' % job_name))

    def save_job_code(self, job_name, job_code_str):
        assert(self.logged_in)
        logger.debug('Save code of job %s', job_name)
        jobs_folder = op.join(self.data_folder, WorkBook.JOBS_FOLDER)
        self.filesystem.save(op.join(jobs_folder, '%s.py' % job_name),
                             job_code_str, overwrite=True)

    def get_job_code(self, job_name):
        return self.jobs_code[job_name]

    def job_from_code(self, job_name, job_code_str):
        logger.debug('Import code of job %s', job_name)
        try:
            job_module = module_from_code_str(job_code_str)
        except:
            raise InvalidJobCode('Error during code import:\n %s' % format_exc())

        logger.debug('Create instance of job %s', job_name)
        try:
            job = job_module.CustomJob(self)
        except AttributeError:
            raise InvalidJobCode('Class CustomJob not found in job %s' % job_name)

        logger.debug('Check instance of job %s', job_name)
        if not isinstance(job, Job):
            raise InvalidJobCode('job %s does not use a subclass of piccel.Job' %
                                 job_name)

        def _check_func(job, fname, check_result, expected_result_descr):
            error_message = None
            try:
                result = eval('job.%s()' % fname)
            except:
                error_message = ('Error in function %s of job %s' %
                                 (fname, job_name))
                details = format_exc()
                logger.error('%s\n%s', error_message, details)
                return error_message

            if not check_result(result):
                error_message =  ('%s.%s does not return %s' % \
                                  (job_name, fname, expected_result_descr))
                logger.error('%s\n%s', error_message)
            return error_message

        errors = []
        for func, validation, rdescr in [('who_can_run',
                                          lambda r: (r is None or
                                                     isinstance(r, str)),
                                          'string or None'),
                                         ('description',
                                          lambda r: (r is None or
                                                     isinstance(r, str)),
                                          'string or None'),
                                         ('min_access_level',
                                          lambda r: (r is None or
                                                     isinstance(r, UserRole)),
                                          'UserRole or None'),
                                         ('icon',
                                          lambda r: (r is None or
                                                     isinstance(r, QtGui.QIcon)),
                                          'QIcon or None')]:
            logger.debug('Check method %s of job %s', func, job_name)
            err_msg = _check_func(job, func, validation, rdescr)
            if err_msg is not None:
                errors.append(err_msg)

        if len(errors) > 0:
            message = ('Error while setting job %s:\n%s' %
                       (job_name, '\n'.join([' - %s' % e for e in errors])))
            logger.error(message)
            raise InvalidJobCode(message)

        return job

    def run_job(self, job_name, ask_input=None, **job_kwargs):
        if job_name not in self.jobs:
            if job_name in self.jobs_invalidity:
                raise JobDisabled(job_name)
            elif job_name not in self.jobs:
                raise JobNotFound(job_name)
        def error_input(*args, **kwargs):
            raise NoJobInputDefined()
        ask_input = if_none(ask_input, error_input)
        self.jobs[job_name].run(ask_input, **job_kwargs)

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
        if not self.logged_in:
            raise WorkBookLoginError()
        if sheet_label not in self.sheets:
            logger.error('WorkBook %s: cannot find sheet %s in %s',
                         self.label, sheet_label, ', '.join(self.sheets))
            raise SheetNotFound(sheet_label)
        return self.sheets[sheet_label]

    def has_sheet(self, sheet_label):
        return sheet_label in self.sheets

    def save_configuration_file(self, workbook_fn):
        cfg = {
            'workbook_label' : self.label,
            'color_hex_str' : self.color_hex_str,
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
        'color_hex_str' : 'color_for_main_titles',
        'linked_sheets' : {
            'path_to_other_workbook' : 'sheet_label_regexp'
            }
        }
        Decryption pwd is not entered and user is not logged in at this point
        """
        if filesystem is None:
            filesystem = LocalFileSystem(op.dirname(workbook_fn))
            workbook_fn = op.basename(workbook_fn)
        cfg = json.loads(filesystem.load(workbook_fn, crypted_content=False))
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
                        linked_book_fns=cfg['linked_sheets'],
                        color_hex_str=cfg.get('color_hex_str', None))

    def export_all_logic(self, output_dir, export_linked=False):
        assert(self.logged_in)
        plugin_fn = op.join(self.data_folder, 'plugin_common.py')
        self.filesystem.copy_to_tmp(plugin_fn, decrypt=True, tmp_dir=output_dir)
        jobs_folder = op.join(self.data_folder, WorkBook.JOBS_FOLDER)
        job_output_dir = op.join(output_dir, WorkBook.JOBS_FOLDER)
        if not op.exists(job_output_dir): os.makedirs(job_output_dir)
        for job_name in self.jobs_code:
            if not job_name.startswith('__'):
                self.filesystem.copy_to_tmp(op.join(jobs_folder, '%s.py' % job_name),
                                            decrypt=True, tmp_dir=job_output_dir)

        sheet_output_dir = op.join(output_dir, 'sheets')
        if not op.exists(sheet_output_dir): os.makedirs(sheet_output_dir)
        for sheet in self.sheets.values():
            if (sheet.label != '__users__' and
                (export_linked or sheet.label not in self.linked_sheets)):
                sheet.export_logic(sheet_output_dir)

    def set_user_password(self, user, new_pwd):
        assert(self.decrypted)
        users_sheet = self.request_read_only_sheet('__users__', user=user)
        users = users_sheet.get_df_view('latest')
        logger.debug('Set password for user %s', user)
        entry_index = users_sheet.df_index_from_value({'User_Name' : user},
                                                      view='latest')
        if len(entry_index) == 0:
            raise UnknownUser(user)

        if len(entry_index) > 1:
            logger.warning('Multiple entries for user %s: %s',
                           user, entry_index)

        form = users_sheet.form_update_entry(entry_index[-1])
        form.set_values_from_entry({'Password_Hash' : hash_password(new_pwd),
                                    'Password_Reset' : False,
                                    'User' : user})
        # TODO: remove this when no longer need
        if 'Security_Word' in form.get_invalid_keys():
            logger.warning('No security word defined for user %s in __users__.'\
                           'Using default one')
            form.set_values_from_entry({'Security_Word' : '1234'})
        form.submit()

    def set_access_password(self, pwd):
        if self.password_vault.has_password_key(WorkBook.ACCESS_KEY):
            raise PasswordChangeError('Cannot overwrite existing encryption key')
        logger.debug('Set data access password')
        self.password_vault.set_password(WorkBook.ACCESS_KEY, pwd)
        logger.debug('Set VIEWER role password = data access password')
        self.password_vault.set_password(UserRole.VIEWER.name, pwd)
        self.password_vault.save()

    def decrypt(self, access_pwd=None, key_afn=None):
        """
        Load user list and resolve linked books
        Must be called before user login.
        """
        logger.info('WorkBook %s: decrypt...', self.label)

        if access_pwd is not None or key_afn is not None:
            if key_afn is None:
                if not self.access_password_is_valid(access_pwd):
                    logger.error('Invalid password for data access')
                    raise InvalidPassword('Data access')
                encrypter = self.password_vault.get_encrypter(WorkBook.ACCESS_KEY,
                                                              access_pwd)
            else:
                with open(key_afn, 'r') as fin:
                    key = fin.read()
                encrypter = self.password_vault.get_encrypter(None, None, key)
            self.filesystem.set_encrypter(encrypter)

        self.decrypted = True

        plugin_fn = op.join(self.data_folder, 'plugin_common.py')
        if not self.filesystem.exists(plugin_fn):
            logger.info('WorkBook %s: plugin file "%s" does not exist. '\
                        'Dump default one', self.label, plugin_fn)
            self.dump_common_plugin()

        try:
            users_sheet = self.request_read_only_sheet('__users__')
        except SheetNotFound:
            users_sheet = None

        if users_sheet is not None:
            if users_sheet.form_master is None:
                logger.info('Set form master for __users__ sheet (None loaded)')
                users_sheet.set_form_master(USERS_FORM.new(),
                                            save=True, overwrite=True)
            else:
                logger.info('current version of form of loaded sheet __users__: %s',
                            users_sheet.form_master.version())
                logger.info('current version of USERS_FORM : %s',
                            USERS_FORM.version())

                if (version.parse(users_sheet.form_master.version()) <
                    version.parse(USERS_FORM.version())):
                    logger.info('Update form master for __users__ sheet')
                    users_sheet.set_form_master(USERS_FORM.new(),
                                                save=True, overwrite=True)

                loaded_users_plugin_ver = users_sheet.plugin.version()
                logger.info('current version of plugin for __users__: %s',
                            loaded_users_plugin_ver)
                current_users_plugin_ver = UserSheetPlugin(None).version()
                logger.info('current version of UserSheetPlugin : %s',
                            current_users_plugin_ver)

            if (version.parse(loaded_users_plugin_ver) <
                version.parse(current_users_plugin_ver)):
                logger.info('Set plugin for __users__ sheet (obsolete version)')
                users_sheet.set_plugin_from_code(UserSheetPlugin.get_code_str(),
                                                 first_attempt=False)

        # try:
        #     users_sheet = self.request_read_only_sheet('__users__')
        #     if not users_sheet.form_master.has_key('Password_Hash') or \
        #        not users_sheet.form_master.has_key('Security_Word'):
        #         logger.info('Fix form master for __users__ sheet')
        #         users_sheet.set_form_master(USERS_FORM.new(),
        #                                     save=True, overwrite=True)
        # except SheetNotFound:
        #     logger.debug('__users__ sheet not found. Could not check it')

        # TODO: fix handling roles in linked workbooks

        # self.user_roles = self._load_user_roles()
        # logger.info('WorkBook %s: Loaded users:\n %s', self.label,
        #              pformat(self.user_roles))

        # for linked_wb, sheet_filter in self.linked_books:
        #     linked_wb.decrypt(access_pwd)
        #     linked_user_roles = linked_wb._load_user_roles()
        #     for user, role in self.user_roles.copy().items():
        #         if user in linked_user_roles:
        #             if linked_user_roles[user] > role:
        #                 logger.info('Use higher role %s from linked workbook %s'\
        #                             'instead of role %s for user %s',
        #                             linked_user_roles[user],
        #                             linked_wb.label, role, user)
        #                 self.user_roles[user] = linked_user_roles[user]
        #         else:
        #             raise UnknownUser('%s in %s', linked_wb.label)

        return True


    def dump_access_key(self, key_afn):
        assert(self.decrypted)
        with open(key_afn, 'w') as fout:
            fout.write(self.filesystem.encrypter.get_key())

    def refresh_all_data(self):
        logger.debug2('Workbook %s: Refresh data', self.label)
        for sheet in self.sheets.values():
            sheet.refresh_data()

    def get_users(self):
        assert(self.decrypted)
        users_sheet = self.request_read_only_sheet('__users__')
        active_users = users_sheet.get_df_view('active')
        return {row['User_Name'] : UserRole[row['Role']]
                for _, row in active_users.iterrows()}

    def get_user_role(self, user=None):
        assert(self.decrypted)
        if user is None:
            if self.user is None:
                raise WorkBookLoginError()
            else:
                user = self.user
        users_sheet = self.request_read_only_sheet('__users__')
        try:
            users_info = (users_sheet.get_df_view('active')
                          .set_index('User_Name'))
            user_role = UserRole[users_info.loc[user, 'Role']]
        except KeyError:
            logger.error('Unknown user %s while getting role in %s',
                         user, self.label)
            raise UnknownUser(user)

        return user_role

    def access_password_is_valid(self, pwd):
        try:
            return self.password_vault.password_is_valid(WorkBook.ACCESS_KEY, pwd)
        except UnknownUser:
            raise NoAccessPasswordError()

    def get_security_word(self, user):
        assert(self.decrypted)
        users_sheet = self.request_read_only_sheet('__users__')
        users = users_sheet.get_df_view('latest').set_index('User_Name')

        if user not in users.index:
            raise UnknownUser(user)

        security_word = users.loc[user, 'Security_Word']
        if pd.isna(security_word):
            logger.warning('Security word for user %s is empty. '\
                           'Using default one', user)
            security_word = '1234'
        return security_word

    def password_reset_needed(self, user):
        assert(self.decrypted)
        users_sheet = self.request_read_only_sheet('__users__')
        users = users_sheet.get_df_view('latest').set_index('User_Name')

        if user not in users.index:
            logger.error('User "%s" not in: %s', user, ', '.join(users.index))
            raise UnknownUser(user)

        return (users.loc[user, 'Password_Reset'] or
                pd.isna(users.loc[user, 'Password_Hash']))

    def user_password_is_valid(self, user, pwd):
        assert(self.decrypted)
        users_sheet = self.request_read_only_sheet('__users__')
        users = users_sheet.get_df_view('latest').set_index('User_Name')

        if user not in users.index:
            raise UnknownUser(user)

        if users.loc[user, 'Password_Reset']:
            raise PasswordReset(user)

        return (not pd.isna(users.loc[user, 'Password_Hash']) and
                password_is_valid(pwd, users.loc[user, 'Password_Hash']))

    def request_read_only_sheet(self, sheet_label, user=None):
        if self.logged_in:
            if sheet_label not in self.sheets:
                raise SheetNotFound(sheet_label)
            sheet = self[sheet_label]
        elif sheet_label in self.read_only_sheets:
            sheet = self.read_only_sheets[sheet_label]
        else:
            user = if_none(user, self.user)
            sheet_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER)
            if not self.filesystem.exists(op.join(sheet_folder,
                                                  sheet_label)):
                raise SheetNotFound(sheet_label)
            sh_fs = self.filesystem.change_dir(op.join(sheet_folder,
                                                       sheet_label))
            logger.debug('Create requested r-o sheet %s for user %s',
                         sheet_label, user)
            sheet = DataSheet.from_files(user, sh_fs, None, workbook=self)
            self.read_only_sheets[sheet_label] = sheet

        return sheet

    def user_login(self, user, pwd=None, user_role=None, progress_callback=None,
                   load_sheets=True):
        """
        Note:
        If a user has write access to the workbook files and has the data access
        password, then they can modify workbook files as they want.
        There is no mechanism that strictly protects admin operations.

        Write access must be handled by the file system.
        """
        assert(self.decrypted)
        self.user = user
        main_role = self.get_user_role()
        if user_role is not None:
            if user_role > main_role:
                raise UnauthorizedRole('%s has main role %s, cannot be %s' %
                                       user, main_role, user_role)
            self.user_role = user_role
        else:
            self.user_role = main_role
        logger.info('Logging as user %s with role %s',
                    self.user, self.user_role)

        if pwd is not None and not self.user_password_is_valid(user, pwd):
            logger.error('Invalid password for %s', user)
            raise InvalidPassword(user)

        for linked_book, sheet_filter in self.linked_books:
            linked_book.user_login(user, pwd, user_role=user_role,
                                   load_sheets=load_sheets)

        self.logged_in = True

        if load_sheets:
           self.reload(progress_callback)

    def get_sheet(self, sheet_label):
        if not self.logged_in:
            raise WorkBookLoginError()
        return self.sheets[sheet_label]

    def get_nb_sheets(self, sheet_re):
        if isinstance(sheet_re, str):
            sheet_re = re.compile(sheet_re)
        sheet_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER)
        return sum(1 for sh in self.filesystem.listdir(sheet_folder) \
                   if sheet_re.match(sh))

    def dump_common_plugin(self, plugin_code=None):
        plugin_fn = op.join(self.data_folder, 'plugin_common.py')
        logger.debug('Dump workbook plugin in %s', plugin_fn)
        if plugin_code is None:
            plugin_code = inspect.getsource(workbook_plugin_template)
        self.filesystem.save(plugin_fn, plugin_code, overwrite=True)

    def reload(self, progress_callback=None):
        progress_callback = if_none(progress_callback, lambda s: None)

        if not self.decrypted:
            logger.error('WorkBook %s: decryption not setup, cannot reload.')
            return

        if self.user is None:
            logger.error('WorkBook %s: user not logged in, cannot reload.')
            return

        self.load_plugin()
        self.load_jobs()

        # TODO: sort out sheet filtering
        # ASSUME all sheet labels are unique
        self.sheets.clear()
        self.sheets = self.load_sheets(parent_workbook=self)
        logger.debug('WorkBook %s: Load linked workbooks: %s',
                     self.label, ','.join('"%s"'%l for l,b in self.linked_books))
        self.linked_sheets = []
        for linked_book, sheet_regexp in self.linked_books:
            progress_callback('Load sheets from linked workbook %s' \
                              % linked_book.label)
            linked_sheets = linked_book.load_sheets(sheet_regexp,
                                                    progress_callback,
                                                    parent_workbook=self)
            self.sheets.update(linked_sheets)
            self.linked_sheets.extent(linked_sheets)
        self.after_workbook_load()

    def dump_default_job(self, export_job_name):
        assert(export_job_name == '__job_export_logic__')

        self.set_job_code(export_job_name, ExportJob.get_code_str(), save=True)

    def load_jobs(self, first_attempt=True):

        jobs_folder = op.join(self.data_folder, WorkBook.JOBS_FOLDER)
        export_job_name = '__job_export_logic__'
        if not self.filesystem.exists(op.join(jobs_folder,
                                              '%s.py' % export_job_name)):
            logger.debug('Dump default job %s', export_job_name)
            self.dump_default_job(export_job_name)

        self.jobs.clear()
        self.jobs_invalidity.clear()

        for job_fn in self.filesystem.listdir(jobs_folder):
            if job_fn.endswith(WorkBook.JOB_EXT):
                job_name = op.splitext(job_fn)[0]
                logger.debug('Load job from %s', op.join(jobs_folder,
                                                            job_fn))
                job_code_str = self.filesystem.load(op.join(jobs_folder,
                                                            job_fn))

                if (first_attempt and
                    not self.set_job_code(job_name, job_code_str, save=False) and
                    job_name.startswith('__')):
                    logger.debug('Error while setting %s. Dump it again.',
                                 job_name)
                    self.dump_default_job(job_name)
                    self.load_jobs(first_attempt=False)

    def after_workbook_load(self):
        logger.debug('Workbook %s: call after_workbook_load on all sheets',
                     self.label)
        # for sheet in self.sheets.values():
        #     sheet.plugin.check()

        for sheet in self.sheets.values():
            sheet.after_workbook_load()

    def get_common_plugin_code(self):
        plugin_fn = op.join(self.data_folder, 'plugin_common.py')
        tmp_fn = self.filesystem.copy_to_tmp(plugin_fn, decrypt=True)
        with open(tmp_fn, 'r') as fin:
            return fin.read()

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
        progress_callback = if_none(progress_callback, lambda s: None)

        # TODO. improve progress callback to avoid handling logic of increment
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

        sheets_folder = op.join(self.data_folder, WorkBook.SHEET_FOLDER)
        logger.info('WorkBook %s: Load sheets from %s',
                    self.label, sheets_folder)
        sheets = {}

        sheet_list = self.plugin.sheet_order()
        logger.info('WorkBook %s: sheets order from common plugin: %s',
                     self.label, sheet_list)

        sheet_folders = self.filesystem.listdir(sheets_folder,
                                                list_folders_only=True)

        unknown_sheets = set(sheet_list).difference(sheet_folders)
        if len(unknown_sheets) > 0:
            logger.warning('WorkBook %s: Unknown sheets specified in '\
                           'common plugin: %s' \
                           %(self.label, ', '.join(unknown_sheets)))

        last_sheets = []
        for sheet_label in sorted(sheet_folders):
           if sheet_label not in sheet_list:
                if not sheet_label.startswith('__'):
                    sheet_list.append(sheet_label)
                else:
                    last_sheets.append(sheet_label)

        for sheet_label in sorted(last_sheets):
            sheet_list.append(sheet_label)

        logger.debug('WorkBook %s: sheets to load from files: %s',
                     self.label, sheet_list)
        for sheet_label in sheet_list:
            if not self.filesystem.exists(op.join(sheets_folder,
                                                  sheet_label)):
                logger.warning('WorkBook %s: Skip loading sheet %s '\
                               '(no folder dfound)' %(self.label, sheet_label))
                continue
            if sheet_regexp.match(sheet_label) is not None:
                logger.info('WorkBook %s: Reload data sheet %s' % \
                            (self.label, sheet_label))
                sh_fs = self.filesystem.change_dir(op.join(sheets_folder,
                                                           sheet_label))

                sh = DataSheet.from_files(self.user, sh_fs,
                                          user_role=self.user_role,
                                          workbook=parent_workbook)
                sheets[sheet_label] = sh
                progress_callback('Loaded sheet %s' % sh.label)
            else:
                logger.debug('WorkBook %s: sheet %s not loaded (filtered)' % \
                             (self.label, sheet_label))
        return sheets

    def __eq__(self, other):
        return isinstance(other, WorkBook) and self.label==other.label and\
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

        sheet.change_filesystem(self.filesystem.change_dir(sheet_folder),
                                save_logic=True, save_live_data=True)
        sheet.set_workbook(self)

        if self.user is not None:
            sheet.set_user(self.user, self.user_role)

        self.sheets[sheet.label] = sheet

        self.after_workbook_load()

    def delete_sheet(self, sheet_label):
        sheet = self.sheets[sheet_label]

        blocking_users = sheet.users_with_pending_live_forms()
        if len(blocking_users):
            raise LiveFormsPendingError(blocking_users)

        if sheet.df is not None and sheet.df.shape[0] > 0:
            raise NonEmptyDataSheetError()

        blocking_users = sheet.users_with_master_form_lock()
        if len(blocking_users):
            raise MasterFormLockError(blocking_users)

        self.sheets.pop(sheet_label)
        self.filesystem.rmtree(op.join(self.sheet_folder, sheet_label))

        self.after_workbook_load() # TODO handle unwatching here: better to fully reload workbook from scratch in fact...

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


class InputTestJob(Job):
    def run(self, ask_input):
        self.workbook.hack_report = ask_input('Report')

class TestWorkBook(unittest.TestCase):

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp()
        logger.setLevel(logging.DEBUG)
        self.access_pwd = '1234'
        self.admin_pwd = '5425'

    def tearDown(self):
        shutil.rmtree(self.tmp_dir)

    def test_job(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        wb = WorkBook.create(wb_id, fs, access_password='HIOgb',
                             admin_password='6789341', admin_user='TV')

        wb.set_job_code('a_job', InputTestJob.get_code_str(), save=True)

        def fake_input(prompt):
            return 'Job done'
        wb.run_job('a_job', fake_input)

        self.assertEqual(wb.hack_report, 'Job done')

    def test_job_bad_name(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        wb = WorkBook(wb_id, data_folder, fs)
        self.assertRaises(InvalidJobName, wb.set_job_code, 'baaad name!', 'nvm')

    def test_job_bad_code(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        code = 'baaad code'
        wb.set_job_code('a_job', code, save=True)
        self.assertTrue('a_job' in wb.jobs_invalidity)
        self.assertRaises(JobDisabled, wb.run_job, 'a_job')
        self.assertEqual(wb.get_job_code('a_job'), code)

        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)

        self.assertRaises(JobDisabled, wb2.run_job, 'a_job')

        class NewJob(Job):
            def run(self, ask_input):
                self.workbook.hack_report = 'Job done'

        job_code = NewJob.get_code_str()
        wb2.set_job_code('a_job', job_code, save=True)
        self.assertEqual(wb2.get_job_code('a_job'), job_code)
        wb2.run_job('a_job')

    def test_delete_sheet(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        user = 'TV'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Simple_Sheet'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)

        wb.add_sheet(sh1)
        wb.delete_sheet(sh1.label)

        self.assertRaises(SheetNotFound, wb.__getitem__, 'Simple_Sheet')
        self.assertFalse(fs.exists(op.join(wb.sheet_folder, 'Simple_Sheet')))

        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)

        self.assertRaises(SheetNotFound, wb2.__getitem__, 'Simple_Sheet')
        self.assertFalse(fs.exists(op.join(wb2.sheet_folder, 'Simple_Sheet')))

    def test_cannot_delete_sheet_with_data(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        user = 'TV'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Simple_Sheet'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)
        wb.add_sheet(sh1)

        sh1.add_new_entry({'Participant_ID' : 'Bobbie'})
        sh1.add_new_entry({'Participant_ID' : 'Chouchou'})

        self.assertRaises(NonEmptyDataSheetError, wb.delete_sheet, 'Simple_Sheet')

        sh1.delete_all_entries()

        wb.delete_sheet(sh1.label)
        self.assertRaises(SheetNotFound, wb.__getitem__, 'Simple_Sheet')
        self.assertFalse(fs.exists(op.join(wb.sheet_folder, 'Simple_Sheet')))

    def test_cannot_delete_sheet_pending_live_forms(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        user = 'TV'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Simple_Sheet'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)
        wb.add_sheet(sh1)

        form = sh1.form_new_entry()
        self.assertRaises(LiveFormsPendingError, wb.delete_sheet, 'Simple_Sheet')

        form.submit()
        sh1.delete_all_entries()

        wb.delete_sheet(sh1.label)
        self.assertRaises(SheetNotFound, wb.__getitem__, 'Simple_Sheet')
        self.assertFalse(fs.exists(op.join(wb.sheet_folder, 'Simple_Sheet')))

    def test_cannot_delete_sheet_master_form_edition_lock(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        user = 'TV'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Simple_Sheet'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)
        wb.add_sheet(sh1)

        sh1.get_form_for_edition()
        self.assertRaises(MasterFormLockError, wb.delete_sheet, 'Simple_Sheet')

        sh1.close_form_edition()

        wb.delete_sheet(sh1.label)
        self.assertRaises(SheetNotFound, wb.__getitem__, 'Simple_Sheet')
        self.assertFalse(fs.exists(op.join(wb.sheet_folder, 'Simple_Sheet')))

    def test_delete_sheet_on_watchers(self):
        raise NotImplementedError() # TODO

    def test_export_all_logic(self):

        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        data_folder = 'workbook_files'
        user = 'TV'
        logger.debug('-----------------------')
        logger.debug('utest: create workbook')
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Sheet_With_Form'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)

        sheet_id = 'Sheet_With_No_Form'
        sh2 = DataSheet(sheet_id, None, user=user)

        sheet_id = 'Sheet_With_Plugin'
        sh3 = DataSheet(sheet_id, None, user=user)
        class Plugin1(SheetPlugin):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.df = pd.DataFrame(['init p1'], columns=['Field'])

            def update(self, sheet_source, changed_entry,
                       deletion=False, clear=False):
                self.df.iat[0,0] = 'plugin 1 was here'

            def views(self, views):
                return {'full' : lambda df: self.df}
        sh3.set_plugin_from_code(Plugin1.get_code_str())

        wb.add_sheet(sh1)
        wb.add_sheet(sh2)
        wb.add_sheet(sh3)

        class AJob(Job):
            def run(self, ask_input):
                self.workbook.hack_report = 'Job done'

        job_code = AJob.get_code_str()
        wb.set_job_code('a_job', job_code, save=True)

        export_folder = op.join(self.tmp_dir, 'wb_logic')
        os.makedirs(export_folder)
        wb.export_all_logic(export_folder, export_linked=False)
        expected_fns = [op.join(export_folder, 'plugin_common.py'),
                        op.join(export_folder, 'jobs', 'a_job.py'),
                        op.join(export_folder, 'sheets', 'Sheet_With_Form.form'),
                        op.join(export_folder, 'sheets', 'Sheet_With_Form.py'),
                        op.join(export_folder, 'sheets', 'Sheet_With_No_Form.py'),
                        op.join(export_folder, 'sheets', 'Sheet_With_Plugin.py')]
        for fn in expected_fns:
            self.assertTrue(op.exists(fn), '%s does not exist' % fn)
        not_expected_fns = [op.join(export_folder, '__users__.form'),
                            op.join(export_folder, '__users__.py'),
                            op.join(export_folder, 'sheets',
                                    'Sheet_With_No_Form.form'),
                            op.join(export_folder, 'sheets',
                                    'Sheet_With_Plugin.form')]
        for fn in not_expected_fns:
            self.assertFalse(op.exists(fn), '%s must not exist' % fn)

        # TODO check that no exported file starts with "__"

    def test_export_logic_job(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'A_Workbook'
        data_folder = 'workbook_files'
        user = 'TV'
        logger.debug('-----------------------')
        logger.debug('utest: create workbook')
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        sheet_id = 'Sheet_With_Form'
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'}),]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Evaluation'})
        sh1 = DataSheet(sheet_id, form, user=user)

        sheet_id = 'Sheet_With_No_Form'
        sh2 = DataSheet(sheet_id, None, user=user)

        sheet_id = 'Sheet_With_Plugin'
        sh3 = DataSheet(sheet_id, None, user=user)
        class Plugin1(SheetPlugin):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.df = pd.DataFrame(['init p1'], columns=['Field'])

            def update(self, sheet_source, changed_entry,
                       deletion=False, clear=False):
                self.df.iat[0,0] = 'plugin 1 was here'

            def views(self, views):
                return {'full' : lambda df: self.df}
        sh3.set_plugin_from_code(Plugin1.get_code_str())

        wb.add_sheet(sh1)
        wb.add_sheet(sh2)
        wb.add_sheet(sh3)

        class AJob(Job):
            def run(self, ask_input):
                self.workbook.hack_report = 'Job done'

        job_code = AJob.get_code_str()
        wb.set_job_code('a_job', job_code, save=True)

        export_folder = op.join(self.tmp_dir, 'wb_logic')
        os.makedirs(export_folder)
        wb.export_all_logic(export_folder, export_linked=False)
        expected_fns = [op.join(export_folder, 'plugin_common.py'),
                        op.join(export_folder, 'jobs', 'a_job.py'),
                        op.join(export_folder, 'sheets',
                                'Sheet_With_Form.form'),
                        op.join(export_folder, 'sheets',
                                'Sheet_With_Form.py'),
                        op.join(export_folder, 'sheets',
                                'Sheet_With_No_Form.py'),
                        op.join(export_folder, 'sheets',
                                'Sheet_With_Plugin.py')]
        for fn in expected_fns:
            self.assertTrue(op.exists(fn), '%s does not exist' % fn)
        not_expected_fns = [op.join(export_folder, '__users__.form'),
                            op.join(export_folder, '__users__.py'),
                            op.join(export_folder, 'jobs', '__export__.py'),
                            op.join(export_folder, 'sheets',
                                    'Sheet_With_No_Form.form'),
                            op.join(export_folder, 'sheets',
                                    'Sheet_With_Plugin.form')]
        for fn in not_expected_fns:
            self.assertFalse(op.exists(fn), '%s must not exist' % fn)

    def test_delete_good_job(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        class AJob(Job):
            def run(self, ask_input):
                self.workbook.hack_report = 'Job done'

        job_code = AJob.get_code_str()
        wb.set_job_code('a_job', job_code, save=True)

        wb.delete_job('a_job')

        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)

        self.assertRaises(JobNotFound, wb2.run_job, 'a_job')

    def test_delete_bad_job(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        wb.set_job_code('a_job', 'baaad code', save=True)
        wb.delete_job('a_job')
        self.assertFalse('a_job' in wb.jobs_code)
        self.assertFalse('a_job' in wb.jobs_invalidity)

        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)

        self.assertFalse('a_job' in wb2.jobs_code)
        self.assertFalse('a_job' in wb2.jobs_invalidity)

    def test_job_ask_password(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        wb = WorkBook.create(wb_id, fs, access_password='HIOgb',
                             admin_password='6789341', admin_user='TV')

        class AskJob(Job):
            def run(self, ask_input):
                self.workbook.hack_pwd = ask_input('Gimme',
                                                   input_type=InputType.PASSWORD)

        wb.set_job_code('a_job', AskJob.get_code_str(), save=True)

        def _ask_input(prompt, input_type):
            assert(input_type == InputType.PASSWORD)
            return 'pwd'

        wb.run_job('a_job', _ask_input)

        self.assertEqual(wb.hack_pwd, 'pwd')

    def test_job_persistence(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb_id = 'Participant_info'
        data_folder = 'pinfo_files'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

        class AJob(Job):
            def run(self, ask_input):
                self.workbook.hack_report = 'Job done'

        wb.set_job_code('a_job', AJob.get_code_str(), save=True)

        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
        wb2.decrypt(self.access_pwd)
        wb2.user_login(user, self.admin_pwd)

        wb2.run_job('a_job')
        self.assertEqual(wb2.hack_report, 'Job done')

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

        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

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

    def test_user_password_reset(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb = WorkBook.create('Participant_info', fs, access_password='12345',
                             admin_password='12T64', admin_user='admin')

        wb['__users__'].add_new_entry({'User_Name' : 'me',
                                       'Security_Word' : 'yata',
                                       'Role' : UserRole.EDITOR.name})
        self.assertRaises(PasswordReset, wb.user_login, 'me', 'hahaha')
        wb.set_user_password('me', 'pwd_me') # Password_Reset is set to False there
        wb.user_login('me', 'pwd_me')

        form_update_or_new('__users__', wb, {'User_Name' : 'me'},
                           {'Password_Reset' : True})[0].submit()

        self.assertRaises(PasswordReset, wb.user_login, 'me', 'pwd_me')

    def test_edit_users_role_check(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb = WorkBook.create('Participant_info', fs, access_password='12345',
                             admin_password='12T64', admin_user='admin')
        self.assertEqual(wb.get_users(), {'admin' : UserRole.ADMIN})

        sh_users = wb['__users__']
        sh_users.add_new_entry({'User_Name' : 'Bobbie',
                                'Security_Word' : 'yata',
                                'Role' : UserRole.MANAGER.name})
        wb.set_user_password('Bobbie', 'pwd_staff')
        wb.user_login('Bobbie', 'pwd_staff')

        sh_users = wb['__users__']
        users_df = sh_users.get_df_view()
        idx = sh_users.df_index_from_value({'User_Name' : 'admin'},
                                              view='latest')
        self.assertRaises(UnauthorizedRole, sh_users.action,
                          users_df.loc[idx], 'Eval_Staff')
        logger.debug('--- get form to enter new user as Bobbie ---')
        form = sh_users.form_new_entry()
        self.assertEqual(set(form.key_to_items['Role'][0].choices.keys()),
                         {'VIEWER', 'EDITOR', 'REVIEWER', 'MANAGER'})

    def test_edit_users(self):
        fs = LocalFileSystem(self.tmp_dir)
        wb = WorkBook.create('Participant_info', fs, access_password='12345',
                             admin_password='12T64', admin_user='admin')
        self.assertEqual(wb.get_users(), {'admin' : UserRole.ADMIN})
        wb['__users__'].add_new_entry({'User_Name' : 'me',
                                       'Security_Word' : 'yata',
                                       'Role' : UserRole.EDITOR.name})
        wb['__users__'].add_new_entry({'User_Name' : 'other',
                                       'Security_Word' : 'yata2',
                                       'Role' : UserRole.MANAGER.name})
        self.assertEqual(wb.get_users(),
                         {'admin' : UserRole.ADMIN,
                          'me' : UserRole.EDITOR,
                          'other' : UserRole.MANAGER})
        form_update_or_new('__users__', wb, {'User_Name' : 'other'},
                           {'Status' : 'non_active'})[0].submit()
        self.assertEqual(wb.get_users(),
                         {'admin' : UserRole.ADMIN,
                          'me' : UserRole.EDITOR})
        form_update_or_new('__users__', wb, {'User_Name' : 'other'},
                           {'Status' : 'active'})[0].submit()
        self.assertEqual(wb.get_users(),
                         {'admin' : UserRole.ADMIN,
                          'me' : UserRole.EDITOR,
                          'other' : UserRole.MANAGER})

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
        wb1 = WorkBook.create(wb_id, fs, data_folder=data_folder,
                              access_password=self.access_pwd,
                              admin_password=self.admin_pwd, admin_user='me')

        key_fn = op.join(self.tmp_dir, 'key')
        logger.debug('utest: dump key from workbook1')
        wb1.dump_access_key(key_fn)

        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')

        wb2 = WorkBook(wb_id, data_folder, fs)
        wb2.decrypt(None, key_afn=key_fn)
        wb2.user_login('me', self.admin_pwd)

        self.assertEqual(wb1, wb2)

    def test_data_persistence(self):

        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        logger.debug('-----------------------')
        logger.debug('utest: create workbook1')
        wb_id = 'Participant_info'
        user = 'me'
        wb1 = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                              admin_password=self.admin_pwd, admin_user=user)
        cfg_bfn = protect_fn(wb_id) + '.psh'

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
        wb2 = WorkBook.from_configuration_file(op.join(self.tmp_dir, cfg_bfn))
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
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd,
                             admin_user=user)

        # Create data sheet participant info (no form)
        sheet_id = 'Participants_Status'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE90001'],
                              'Secure_ID' : ['452164532', '5R32141'],
                              'Study_Status' : ['ongoing', 'ongoing']})
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Secure_ID':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          allow_empty=False),
                 FormItem({'Study_Status' :
                           {'French':'Statut du participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          choices={
                              'ongoing' : {'French' : 'Etude en cours'},
                              'drop_out' : {'French' : "Sorti.e de l'étude"},
                              'study_over' : {'French' : "Etude terminée"},
                              'inactive' : {'French' : "Entrée inactive"},
                          },
                          init_values={'Study_Status' : 'ongoing'},
                          allow_empty=False),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem({'Timestamp_Submission' : None},
                          vtype='datetime',
                          default_language='French',
                          supported_languages={'French'},
                          generator='timestamp_submission')
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=user)
        class ParticipantPlugin(SheetPlugin):
            def active_view(self, df):
                latest = self.sheet.latest_update_df(df)
                return latest[latest['Study_Status'] != 'inactive']
            def views(self, views):
                views.update({'latest_active' : self.active_view})
                return views
        sh_pp.set_plugin_from_code(ParticipantPlugin.get_code_str())

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
                 FormItem(keys={'Session_Action':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'do_session':{'French':'Réaliser la séance'},
                                   'revoke_session':
                                   {'French':'Annuler la séance'}},
                          allow_empty=False,
                          init_values={'Session_Action' : 'do_session'}),
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
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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
        sh_pnote = DataSheet('Progress_Notes', form, user=user)

        # Create dashboard sheet that gets list of participants from p_info
        # and compute evaluation status. Action is a string report.
        class DashboardEval(LescaDashboard):
            def sheets_to_watch(self):
                return super(DashboardEval, self).sheets_to_watch() + \
                    ['Evaluation']

            def after_workbook_load(self):
                super(DashboardEval, self).after_workbook_load()

            def init(self):
                self.eval = self.workbook['Evaluation']
                super().init()

            def refresh_entries(self, pids):
                pids, pids_dropped = super().refresh_entries(pids)
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
                super().action(entry_df, selected_column)

                logger.debug('action: entry_df=%s, selected_column=%s',
                             entry_df, selected_column)
                form, action_label = None, None
                if selected_column.startswith('Eval'):
                    participant_id = entry_df.index[0]
                    eval_df = self.eval.get_df_view('latest')
                    selection = eval_df[eval_df.Participant_ID==participant_id]
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
                    })
                return form, action_label

        logger.debug('utest: Create dashboard')
        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin_from_code(DashboardEval.get_code_str())

        wb.add_sheet(sh_dashboard)
        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_eval)
        wb.add_sheet(sh_pp)

        print('after add pp sheet')
        # from IPython import embed; embed()

        dashboard_df = sh_dashboard.get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Eval'] == 'eval_todo').all())

        logger.debug('utest: Add new participant CE90012 with study over')
        form = sh_pp.form_new_entry()
        form.set_values_from_entry({'Participant_ID' : 'CE90001',
                                    'Secure_ID' : '543678',
                                    'Study_Status' : 'study_over'})
        form.submit()

        dashboard_df = sh_dashboard.get_df_view()
        pid = 'CE90001'
        eval_CE90001 = dashboard_df.loc[pid, 'Eval']
        self.assertEqual(eval_CE90001, '')

        logger.debug('utest: Add new participant CE90002')
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
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
        self.assertEqual(dashboard_df.shape, (2,3))

    def test_dashboard_status_track_admin(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Study'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)

        # Create sheet for participant status
        sheet_id = 'Participants_Status'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002'],
                              'Study_Status' : ['ongoing', 'ongoing'],
                              'Timestamp_Submission' : [datetime(2021,9,9,10,10),
                                             datetime(2021,9,9,10,10)]})
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
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
                              'study_over' : {'French' : "Etude complétée"},
                              'inactive' : {'French' : "Entrée inactive"},
                          },
                          allow_empty=False),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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

        class ParticipantPlugin(SheetPlugin):
            def active_view(self, df):
                latest = self.sheet.latest_update_df(df)
                return latest[latest['Study_Status'] != 'inactive']
            def views(self, views):
                views.update({'latest_active' : self.active_view})
                return views
        sh_pp.set_plugin_from_code(ParticipantPlugin.get_code_str())

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
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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
        sh_pnote = DataSheet('Progress_Notes', form, user=user)

        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_pp)

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin_from_code(LescaDashboard.get_code_str())

        wb.add_sheet(sh_dashboard)
        wb.after_workbook_load()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Study_Status'] == 'ongoing').all())

        pid = 'CE0001'
        logger.debug('---- Test add progress note not related to drop-out ----')

        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'PNotes')
        form.set_values_from_entry({'Note_Type' : 'health'})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'ongoing')

        logger.debug('---- Test add exclusion progress note ----')
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'PNotes')
        form.set_values_from_entry({'Note_Type' : 'exclusion'})
        form.submit()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'confirm_drop')

        logger.debug('---- Test add new progress note not related to drop-out ----')

        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'PNotes')
        form.set_values_from_entry({'Note_Type' : 'health'})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'confirm_drop')

        logger.debug('---- Test ignore exclusion from progress note ----')
        # Update participant status, to make it more recent than any pnote
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        self.assertTrue(action_label.endswith('Update'), action_label)
        self.assertTrue(action_label.startswith('Participants'), action_label)
        form.set_values_from_entry({'Study_Status' : 'ongoing'})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'ongoing')

        logger.debug('---- Test add withdrawal progress note ----')
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'PNotes')
        form.set_values_from_entry({'Note_Type' : 'withdrawal'})
        form.submit()

        logger.debug('---- Test add exclusion progress note ----')
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'PNotes')
        form.set_values_from_entry({'Note_Type' : 'exclusion'})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'confirm_drop')

        logger.debug('---- Test accept withdrawal from progress note ----')
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        self.assertTrue(action_label.endswith('Update'), action_label)
        self.assertTrue(action_label.startswith('Participants'), action_label)

        form.set_values_from_entry({'Study_Status' : 'drop_out'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Study_Status'], 'drop_out')

    def test_dashboard_interview_track_editor(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd,
                             admin_user=user)

        # Create data sheet participant info (no form)
        sheet_id = 'Participants_Status'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002'],
                              'Study_Status' : ['ongoing', 'ongoing'],
                              'Timestamp_Submission' :
                              [datetime(2021,9,9,10,10),
                               datetime(2021,9,9,10,10)]})
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
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
                              'study_over' : {'French' : "Etude complétée"},
                              'inactive' : {'French' : "Entrée inactive"},
                          },
                          init_values={'Study_Status' : 'ongoing'},
                          allow_empty=False),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          allow_empty=False,
                          supported_languages={'French'},
                          default_language='French')
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=user)

        class ParticipantPlugin(SheetPlugin):
            def active_view(self, df):
                latest = self.sheet.latest_update_df(df)
                return latest[latest['Study_Status'] != 'inactive']
            def views(self, views):
                views.update({'latest_active' : self.active_view})
                return views
        sh_pp.set_plugin_from_code(ParticipantPlugin.get_code_str())

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
                          number_interval={'left':0, 'closed':'left'},
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
                                  'cancelled':None,
                                  'error':None},
                         init_values={'Email_Status' : 'to_send'},
                         allow_empty=True),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
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
        sh_plan = DataSheet(sheet_id, form, user=user)

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
                                   'revoke_session':
                                   {'French':'Annuler la séance'}},
                          allow_empty=False),
                 FormItem(keys={'Interview_Date':None},
                          vtype='datetime',
                          supported_languages={'French'},
                          default_language='French'),
                 FormItem(keys={'Session_Status':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'done':None,
                                   'redo':None,
                                   'revoke_session':None,},
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
        sh_eval = DataSheet(sheet_id, form, user=user)

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
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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
        sh_pnote = DataSheet('Progress_Notes', form, user=user)

        # Create dashboard sheet that gets list of participants from p_info
        # and compute evaluation status.
        class DashboardInterview(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(DashboardInterview, self).__init__(*args, **kwargs)
                self.date_now = None

            def after_workbook_load(self):
                super(DashboardInterview, self).after_workbook_load()

            def init(self):
                self.eval_tracker = InterviewTracker('Eval', self.workbook)
                super().init()

            def sheets_to_watch(self):
                return super(DashboardInterview, self).sheets_to_watch() + \
                    [DEFAULT_INTERVIEW_PLAN_SHEET_LABEL, 'Eval']

            def refresh_entries(self, pids):
                pids, pids_drop = super().refresh_entries(pids)
                logger.debug('DashboardInterview refresh (date_now=%s)...',
                             self.date_now)
                self.eval_tracker.track(self.df, pids, date_now=self.date_now,
                                        pids_drop=pids_drop)

            def action(self, entry_df, selected_column):
                result, result_label = super().action(entry_df, selected_column)
                if result is None:
                    result, result_label = \
                        self.eval_tracker.action(entry_df, selected_column)
                return result, result_label

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin_from_code(DashboardInterview.get_code_str())
        wb.add_sheet(sh_dashboard)

        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_plan)
        wb.add_sheet(sh_eval)
        wb.add_sheet(sh_pp)

        logger.debug('---- Create user Bobbie ----')
        wb['__users__'].add_new_entry({'User_Name' : 'Bobbie',
                                       'Security_Word' : 'yata',
                                       'Role' : UserRole.EDITOR.name})
        wb.set_user_password('Bobbie', 'pwd_staff')

        logger.debug('---- Login as Bobbie ----')
        wb.user_login('Bobbie', 'pwd_staff')

        df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(df.index.values), set(pp_df['Participant_ID']))
        self.assertTrue((df['Eval'] == 'eval_not_done').all())

        pid = 'CE0001'
        logger.debug('---- Test most recent entry in plan sheet ----')

        logger.debug('----- Assign staff for %s -----', pid)

        dashboard_df = wb['Dashboard'].get_df_view()
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                        'Eval_Staff')
        self.assertTrue(action_label.endswith('New'), action_label)
        plan_sheet_label = DEFAULT_INTERVIEW_PLAN_SHEET_LABEL
        self.assertTrue(action_label.startswith(plan_sheet_label),
                        action_label)

        ts = datetime(2021,9,10,10,10)
        form.set_values_from_entry({'Plan_Action' : 'assign_staff',
                                    'Staff' : 'Bobbie',
                                    'Timestamp_Submission' : ts})
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'eval_not_done')
        self.assertEqual(df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(df.loc[pid, 'Eval_Plan'], 'eval_plan')

        logger.debug('------- Pid %s: Plan interview date, no email --------',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
        self.assertEqual(df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATETIME_FMT))

        logger.debug('-- Pid %s: No planned date, availability, no callback --',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11,30)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Plan_Action' : 'plan',
                                    'Interview_Date' : None,
                                    'Availability' : 'parfois',
                                    'Date_Is_Set' : False,
                                    'Callback_Days' : 0,
                                    'Send_Email' : False,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_callback_now')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        logger.debug('-- Pid %s: No planned date, availability, '\
                     'callback in 7 days --', pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,11,35)
        wb['Dashboard'].plugin.date_now = ts
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        wb['Dashboard'].plugin.date_now = ts + timedelta(days=1)
        wb['Dashboard'].plugin.reset_data()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_callback_%dD' % (callback_nb_days-1))
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        wb['Dashboard'].plugin.date_now = (ts +
                                           timedelta(days=callback_nb_days+1))
        wb['Dashboard'].plugin.reset_data()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_callback_now' )
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'parfois')

        logger.debug('------- Pid %s: Plan interview date, with email --------',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,12)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATETIME_FMT))

        logger.debug('------- Interview email sent for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,13)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.set_values_from_entry({'Email_Status' : 'sent',
                                    'Timestamp_Submission' : ts})
        form.submit()

        date_now = idate - timedelta(days=2.1)
        logger.debug('------- Check dashboard 2 days before (date_now=%s) --------' %
                     date_now)
        wb['Dashboard'].plugin.date_now = date_now
        wb['Dashboard'].plugin.reset_data()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_2D')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATETIME_FMT))

        date_now = (datetime(idate.year,
                             idate.month,
                             idate.day) -
                    timedelta(minutes=5))
        logger.debug('------- Check dashboard the night before (date_now=%s) --------' %
                     date_now)
        wb['Dashboard'].plugin.date_now = date_now
        wb['Dashboard'].plugin.reset_data()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_1D')

        date_now = idate - timedelta(hours=1)
        logger.debug('------- Check dashboard one hour before (date_now=%s) --------' %
                     date_now)
        wb['Dashboard'].plugin.date_now = date_now
        wb['Dashboard'].plugin.reset_data()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_today')

        date_now = idate + timedelta(minutes=30)
        logger.debug('------- Check dashboard 30 mins after (date_now=%s) --------' %
                     date_now)
        wb['Dashboard'].plugin.date_now = date_now
        wb['Dashboard'].plugin.reset_data()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_overdue')

        logger.debug('------- Interview email error for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,14)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATETIME_FMT))

        logger.debug('------- Interview done for %s --------' % pid)
        idate = datetime(2021,10,10,10,33)
        ts = datetime(2021,11,10,10,16)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Eval'))

        form.set_values_from_entry({'Session_Action' : 'do_session',
                                    'Interview_Date' : idate,
                                    'Session_Status' : 'done',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_done')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         idate.strftime(DATETIME_FMT))

        logger.debug('------- Interview to redo for %s --------' % pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,9,10,10,17)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
                         'eval_plan')

        logger.debug('------- Interview revoked for %s --------' % pid)
        idate = datetime(2021,10,11,10,10)
        ts = datetime(2021,9,10,10,18)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Eval'))
        form.set_values_from_entry({'Session_Action' : 'revoke_session',
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'], 'eval_NA')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'], 'eval_plan')

        logger.debug('--- Pid %s: Plan interview date again, with email ----',
                     pid)
        idate = datetime(2021,10,15,10,10)
        ts = datetime(2021,9,10,10,29)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
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
                         idate.strftime(DATETIME_FMT))

        logger.debug('--- Pid %s: Revoke interview again, expect email cancel ----',
                     pid)

        ts = datetime(2021,9,10,10,50)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Eval'))
        form.set_values_from_entry({'Session_Action' : 'revoke_session',
                                    'Timestamp_Submission' : ts})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_NA')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         'confirm_cancel')

        logger.debug('--- Pid %s: email cancelled ----', pid)
        ts = datetime(2021,9,10,10,50)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith(plan_sheet_label))
        form.submit() # automatically filled for email cancellation
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_NA')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         'eval_plan')

        logger.debug('--- Pid %s: Plan interview date again, without email ----',
                     pid)
        idate = datetime(2021,10,15,10,10)
        ts = datetime(2021,9,10,10,51)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        form.set_values_from_entry({'Interview_Date' : idate,
                                    'Date_Is_Set' : True,
                                    'Staff' : 'Catherine-Alexandra Grégoire',
                                    'Send_Email' : False,
                                    'Email_Status' : None,
                                    'Timestamp_Submission' : ts})
        form.submit()

        logger.debug('--- Pid %s: Revoke interview again, expect no email cancel ---',
                     pid)

        ts = datetime(2021,9,10,10,55)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Eval'))
        form.set_values_from_entry({'Session_Action' : 'revoke_session',
                                    'Timestamp_Submission' : ts})
        form.submit()

        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Eval'],
                         'eval_NA')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Staff'],
                         'Bobbie')
        self.assertEqual(dashboard_df.loc[pid, 'Eval_Plan'],
                         'eval_plan')

    def test_dashboard_interview_review(self):
        # Must be reviewer role to access review field
        self.assertTrue(False)

    def test_dashboard_interview_on_drop(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Participant_info'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd,
                             admin_user=user)

        # Create data sheet participant info (no form)
        sheet_id = 'Participants_Status'
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002', 'CE0003'],
                              'Study_Status' : ['ongoing', 'ongoing', 'ongoing'],
                              'Timestamp_Submission' :
                              [datetime(2021,9,9,10,10),
                               datetime(2021,9,9,10,10),
                               datetime(2021,9,9,10,10)]})
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
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
                              'study_over' : {'French' : "Etude complétée"},
                              'inactive' : {'French' : "Entrée inactive"},
                          },
                          init_values={'Study_Status' : 'ongoing'},
                          allow_empty=False),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          allow_empty=False,
                          supported_languages={'French'},
                          default_language='French')
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Participant Information'})
        sh_pp = DataSheet(sheet_id, form_master=form, df=pp_df, user=user)

        class ParticipantPlugin(SheetPlugin):
            def active_view(self, df):
                latest = self.sheet.latest_update_df(df)
                return latest[latest['Study_Status'] != 'inactive']
            def views(self, views):
                views.update({'latest_active' : self.active_view})
                return views
        sh_pp.set_plugin_from_code(ParticipantPlugin.get_code_str())

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
                          number_interval={'left':0, 'closed':'left'},
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
                                  'cancelled':None,
                                  'error':None},
                         init_values={'Email_Status' : 'to_send'},
                         allow_empty=True),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
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
        sh_plan = DataSheet(sheet_id, form, user=user)

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
                                   'revoke_session':
                                   {'French':'Annuler la séance'}},
                          allow_empty=False),
                 FormItem(keys={'Interview_Date':None},
                          vtype='datetime',
                          supported_languages={'French'},
                          default_language='French'),
                 FormItem(keys={'Session_Status':None},
                          vtype='text', supported_languages={'French'},
                          default_language='French',
                          choices={'done':None,
                                   'redo':None,
                                   'revoke_session':None},
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
        sh_eval = DataSheet(sheet_id, form, user=user)

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
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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
        sh_pnote = DataSheet('Progress_Notes', form, user=user)

        # Create dashboard sheet that gets list of participants from p_info
        # and compute evaluation status.
        class DashboardInterview(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(DashboardInterview, self).__init__(*args, **kwargs)
                self.date_now = None

            def after_workbook_load(self):
                super(DashboardInterview, self).after_workbook_load()

            def init(self):
                self.eval_tracker = InterviewTracker('Eval', self.workbook)
                super().init()

            def sheets_to_watch(self):
                return super(DashboardInterview, self).sheets_to_watch() + \
                    [DEFAULT_INTERVIEW_PLAN_SHEET_LABEL, 'Eval']

            def refresh_entries(self, pids):
                pids, pids_drop = super().refresh_entries(pids)
                logger.debug('DashboardInterview refresh (date_now=%s)...',
                             self.date_now)
                self.eval_tracker.track(self.df, pids, date_now=self.date_now,
                                        pids_drop=pids_drop)

            def action(self, entry_df, selected_column):
                result, result_label = super().action(entry_df, selected_column)
                if result is None:
                    result, result_label = \
                        self.eval_tracker.action(entry_df, selected_column)
                return result, result_label

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin_from_code(DashboardInterview.get_code_str())
        wb.add_sheet(sh_dashboard)

        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_plan)
        wb.add_sheet(sh_eval)
        wb.add_sheet(sh_pp)

        logger.debug('---- Create user Bobbie ----')
        wb['__users__'].add_new_entry({'User_Name' : 'Bobbie',
                                       'Security_Word' : 'yata',
                                       'Role' : UserRole.MANAGER.name})
        wb.set_user_password('Bobbie', 'pwd_staff')

        logger.debug('---- Login as Bobbie ----')
        wb.user_login('Bobbie', 'pwd_staff')

        pid = 'CE0003'
        logger.debug('---- Pid %s: Drop without interview or prior planning ----',
                     pid)
        ts = datetime(2021,11,10,10,17)
        dashboard_df = wb['Dashboard'].get_df_view()
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        form.set_values_from_entry({'Study_Status' : 'drop_out',
                                    'Timestamp_Submission' : ts})
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertTrue(pd.isna(df.loc[pid, 'Eval']),
                         df.loc[pid, 'Eval'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Plan']),
                        df.loc[pid, 'Eval_Plan'])

        pid = 'CE0001'
        logger.debug('---- Pid %s: Do interview, without prior planning ----',
                     pid)
        idate = datetime(2021,10,10,10,33)
        ts = datetime(2021,11,10,10,16)
        dashboard_df = wb['Dashboard'].get_df_view()
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Eval'))

        form.set_values_from_entry({'Session_Action' : 'do_session',
                                    'Interview_Date' : idate,
                                    'Session_Status' : 'redo',
                                    'Timestamp_Submission' : ts})
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'eval_redo')
        self.assertTrue(df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertTrue(df.loc[pid, 'Eval_Plan'], idate.strftime(DATETIME_FMT))

        # Drop participant
        ts = datetime(2021,11,10,10,17)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        form.set_values_from_entry({'Study_Status' : 'drop_out',
                                    'Timestamp_Submission' : ts})
        form.submit()

        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'confirm_revoke')
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Plan']),
                        df.loc[pid, 'Eval_Plan'])

        # Put them back in study
        ts = datetime(2021,11,10,10,18)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        form.set_values_from_entry({'Study_Status' : 'ongoing',
                                    'Timestamp_Submission' : ts})
        form.submit()

        logger.debug('------- Pid %s: Plan interview date, with sent email --------',
                     pid)
        idate = datetime(2021,10,10,10,10)
        ts = datetime(2021,11,10,10,19)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        form.set_values_from_entry({'Plan_Action' : 'plan',
                                    'Interview_Date' : idate,
                                    'Staff' : 'dunno',
                                    'Availability' : 'ignored',
                                    'Date_Is_Set' : True,
                                    'Send_Email' : True,
                                    'Email_Status' : 'sent',
                                    'Timestamp_Submission' : ts})
        form.submit()

        # Drop participant
        ts = datetime(2021,11,10,10,20)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        form.set_values_from_entry({'Study_Status' : 'drop_out',
                                    'Timestamp_Submission' : ts})
        form.submit()

        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'confirm_revoke')
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertEqual(df.loc[pid, 'Eval_Plan'], 'confirm_cancel')

        # Confirm planning cancellation
        ts = datetime(2021,11,10,10,21)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval_Plan')
        form.set_values_from_entry({'Timestamp_Submission' : ts})
        logger.debug('---- Cancel date for drop out ----')
        form.submit()

        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'confirm_revoke')
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Plan']),
                        df.loc[pid, 'Eval_Plan'])

        # Confirm session revokation
        ts = datetime(2021,11,10,10,22)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        form.set_values_from_entry({'Timestamp_Submission' : ts})
        logger.debug('---- confirm revokation ----')
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertTrue(pd.isna(df.loc[pid, 'Eval']), df.loc[pid, 'Eval'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Plan']),
                        df.loc[pid, 'Eval_Plan'])


        pid = 'CE0002'
        logger.debug('---- Pid %s: Do interview, without prior planning ----',
                     pid)
        idate = datetime(2021,10,10,10,33)
        ts = datetime(2021,11,10,10,16)
        dashboard_df = wb['Dashboard'].get_df_view()
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Eval')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Eval'))

        form.set_values_from_entry({'Session_Action' : 'do_session',
                                    'Interview_Date' : idate,
                                    'Session_Status' : 'done',
                                    'Timestamp_Submission' : ts})
        form.submit()
        df = wb['Dashboard'].get_df_view()
        self.assertEqual(df.loc[pid, 'Eval'], 'eval_done')
        self.assertTrue(df.loc[pid, 'Eval_Staff'], 'Bobbie')
        self.assertTrue(df.loc[pid, 'Eval_Plan'], idate.strftime(DATETIME_FMT))

        # Drop participant
        ts = datetime(2021,11,10,10,17)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Study_Status')
        form.set_values_from_entry({'Study_Status' : 'drop_out',
                                    'Timestamp_Submission' : ts})
        form.submit()

        df = wb['Dashboard'].get_df_view()
        self.assertTrue(pd.isna(df.loc[pid, 'Eval']),
                         df.loc[pid, 'Eval'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Staff']),
                        df.loc[pid, 'Eval_Staff'])
        self.assertTrue(pd.isna(df.loc[pid, 'Eval_Plan']),
                        df.loc[pid, 'Eval_Plan'])

    def test_dashboard_emailled_poll_track(self):
        # Create empty workbook
        fs = LocalFileSystem(self.tmp_dir)

        # Create new workbook from scratch
        wb_id = 'Project_Evaluation'
        user = 'me'
        wb = WorkBook.create(wb_id, fs, access_password=self.access_pwd,
                             admin_password=self.admin_pwd, admin_user=user)

        # Create data sheet participant status)
        pp_df = pd.DataFrame({'Participant_ID' : ['CE0001', 'CE0002'],
                              'Study_Status' : ['ongoing', 'ongoing'],
                              'Timestamp_Submission' :
                              [datetime(2021,9,9,10,10),
                               datetime(2021,9,9,10,10)]})
        items = [FormItem({'Participant_ID' :
                   {'French':'Code Participant'}},
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
                              'study_over' : {'French' : "Etude complétée"},
                              'inactive' : {'French' : "Entrée inactive"},
                          },
                          init_values={'Study_Status' : 'ongoing'},
                          allow_empty=False),
                 FormItem(keys={'User' : None},
                          vtype='user_name',
                          allow_empty=False,
                          supported_languages={'French', 'English'},
                          default_language='French'),
                 FormItem(keys={'Timestamp_Submission':None},
                          vtype='datetime',
                          allow_empty=True,
                          supported_languages={'French'},
                          default_language='French')
        ]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Statut Participant'})
        sheet_label = 'Participants_Status'
        sh_pp = DataSheet(sheet_label, form_master=form, df=pp_df, user=user)
        class ParticipantPlugin(SheetPlugin):
            def active_view(self, df):
                latest = self.sheet.latest_update_df(df)
                return latest[latest['Study_Status'] != 'inactive']
            def views(self, views):
                views.update({'latest_active' : self.active_view})
                return views
        sh_pp.set_plugin_from_code(ParticipantPlugin.get_code_str())

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
                                   'revoke':
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
                                   'cancelled':None,
                                   'error':None},
                          init_values={'Email_Status' : 'to_send'},
                          allow_empty=True),
                 FormItem(keys={'Email_Scheduled_Send_Date':None},
                          vtype='datetime', supported_languages={'French'},
                          default_language='French',
                          allow_empty=False),
                 FormItem(keys={'User' : None},
                          vtype='user_name',
                          allow_empty=False,
                          supported_languages={'French', 'English'},
                          default_language='French'),
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

        # Create Progress note sheet
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          freeze_on_update=True,
                          supported_languages={'French'}),
                 FormItem(keys={'Note_Type' : None},
                          vtype='text', supported_languages={'French'},
                          choices={'health' : {'French' : 'Etat de santé'},
                                   'withdrawal' : {'French' : "Abandon"},
                                   'exclusion' : {'French' : "Exclusion"}
                                   },
                          default_language='French',
                          allow_empty=False),
                 FormItem({'User' : None},
                          vtype='user_name',
                          default_language='French',
                          supported_languages={'French'},
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
        sh_pnote = DataSheet('Progress_Notes', form, user=user)

        wb.add_sheet(sh_pnote)
        wb.add_sheet(sh_email)
        wb.add_sheet(sh_poll)
        wb.add_sheet(sh_pp)

        class DashboardPoll(LescaDashboard):
            def __init__(self, *args, **kwargs):
                super(DashboardPoll, self).__init__(*args, **kwargs)
                self.date_now = None

            def after_workbook_load(self):
                logger.debug('Dashboard after_workbook_load')
                logger.debug('Dashboard create poll_tracker')
                self.poll_tracker = EmailledPollTracker('Poll', 'Email',
                                                        self.workbook)
                logger.debug('Dashboard after_workbook_load call super()')
                super().after_workbook_load()

            def sheets_to_watch(self):
                return super().sheets_to_watch() + ['Poll', 'Email']

            def refresh_entries(self, pids):
                pids, pids_dropped = super().refresh_entries(pids)
                logger.debug('Dashboard refresh for: %s', pids)
                self.poll_tracker.track(self.df, pids, date_now=self.date_now)

            def action(self, entry_df, selected_column):
                super().action(entry_df, selected_column)
                return self.poll_tracker.action(entry_df, selected_column)

        sh_dashboard = DataSheet('Dashboard')
        sh_dashboard.set_plugin_from_code(DashboardPoll.get_code_str())
        wb.add_sheet(sh_dashboard)

        wb.after_workbook_load()

        pid = 'CE0001'
        logger.debug('--- Pid %s: Email not planned ----', pid)
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(set(dashboard_df.index.values),
                         set(pp_df['Participant_ID']))
        self.assertTrue((dashboard_df['Poll'] == 'poll_to_send').all())

        logger.debug('--- Pid %s: Plan email ----', pid)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Poll')
        self.assertTrue(action_label.endswith('New'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Staff' : 'Catherine-Alexandra Grégoire',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_pending')

        logger.debug('--- Pid %s: Cancel email ----', pid)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Email_Action' : 'cancel',
                                    'Staff' : 'Catherine-Alexandra Grégoire'})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_to_send')

        logger.debug('--- Pid %s: Plan email again ----', pid)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Staff' : 'Thomas Vincent',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_pending')

        logger.debug('--- Pid %s: Email error ----', pid)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        form.set_values_from_entry({'Staff' : 'Script',
                                    'Email_Status' : 'error',
                                    'Email_Scheduled_Send_Date' : \
                                    datetime.now()})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_error')

        logger.debug('--- Pid %s: Email sent, not answered ----', pid)
        form, action_label = sh_dashboard.action(dashboard_df.loc[[pid]],
                                                 'Poll')
        self.assertTrue(action_label.endswith('Update'))
        self.assertTrue(action_label.startswith('Email'))
        ts = datetime(2021,9,10,10,29)
        wb['Dashboard'].plugin.date_now = ts
        overdue_nb_days = 2
        form.set_values_from_entry({'Staff' : 'Script',
                                    'Email_Status' : 'sent',
                                    'Overdue_Days' : overdue_nb_days,
                                    'Timestamp_Submission' : ts})
        form.submit()
        dashboard_df = wb['Dashboard'].get_df_view()
        self.assertEqual(dashboard_df.loc[pid, 'Poll'], 'poll_email_sent')

        logger.debug('--- Pid %s: Email sent, overdue ----', pid)
        wb['Dashboard'].plugin.date_now = ts + timedelta(days=overdue_nb_days+1)
        wb['Dashboard'].plugin.reset_data()
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


    def test_auto_salt(self):
        password = "password"
        crypter = Encrypter(password)

        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

        def give_pwd():
            return password

        crypter2 = Encrypter(password, get_password=give_pwd)
        self.assertEqual(crypter2.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

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
        self.sheet.notifier.add_watcher('appended_entry', self.update_after_append)
        self.sheet.notifier.add_watcher('entry_set', self.update_after_set)
        self.sheet.notifier.add_watcher('pre_delete_entry',
                                        self.update_before_delete)
        self.sheet.notifier.add_watcher('deleted_entry', self.update_after_delete)
        self.sheet.notifier.add_watcher('pre_clear_data', self.update_before_clear)
        self.sheet.notifier.add_watcher('cleared_data', self.update_after_clear)
        self.sheet.notifier.add_watcher('pre_header_change',
                                        self.update_before_clear)
        self.sheet.notifier.add_watcher('header_changed', self.update_after_clear)

    def on_header_changed(self):
        self.headerDataChanged.emit(QtCore.Qt.Horizontal, O, 1)

    def refresh_view(self, view_label=None):
        self.beginResetModel()
        self.view_df = self.sheet.get_df_view(view_label)
        # assert(self.view_df.index.is_lexsorted())

        self.nb_rows = 0
        self.nb_cols = 0
        self.view = []
        self.colums = []
        self.view_validity = []
        self.sort_idx = []
        if self.view_df is not None:
            view_validity_df = self.sheet.view_validity(view_label)
            if self.sheet.show_index_in_ui():
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

        logger.debug('Refreshed view %s of sheet %s in Qt model for UI',
                     view_label, self.sheet.label)
        logger.debug('View_df shape: %s, view_array shape: (%d, %d)',
                     self.view_df.shape,
                     len(self.view[0]) if len(self.view) > 0 else 0,
                     len(self.view),)
        logger.debug('validify_df shape: %s, valididy_array shape: (%d, %d)',
                     view_validity_df.shape,
                     (len(self.view_validity[0])
                      if len(self.view_validity) > 0 else 0),
                     len(self.view_validity))
        self.endResetModel()
        self.layoutChanged.emit()

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

                hint = self.sheet.hint(self.columns[icol], value)
                #logger.debug2('Hint is %s for %s, value=%s', hint,
                #              self.columns[icol], value)
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
        if self.view_df is None:
            return

        try:
            irow = self.view_df.index.get_loc(entry_df.index[0])
        except KeyError:
            # Added an entry that is not in current view... nothing to do
            return False

        tree_view_irow = np.where(self.sort_idx==irow)[0][0]
        self.beginInsertRows(QtCore.QModelIndex(), tree_view_irow,
                             tree_view_irow)
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
        return True

    @QtCore.pyqtSlot()
    def update_after_delete(self, entry_df):
        # TODO: proper callback to actual data change here
        self.endRemoveRows()
        self.layoutChanged.emit()
        return True

    @QtCore.pyqtSlot()
    def update_before_clear(self):
        self.layoutAboutToBeChanged.emit()
        self.beginResetModel()
        return True

    @QtCore.pyqtSlot()
    def update_after_clear(self):
        logger.debug('ItemModel of %s: Update_after_full_clear',
                     self.sheet.label)
        self.endResetModel()
        self.layoutChanged.emit()
        return True

    @QtCore.pyqtSlot()
    def update_after_set(self, entry_idx):
        logger.debug('update_after_set for sheet %s', self.sheet.label)
        if self.view_df is None:
            return
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

from .core import text_connect, get_set_connect

class SheetViewChanger:

    def __init__(self, combobox, sheet_model):
        self.sheet_model = sheet_model
        self.combobox = combobox

    def __call__(self, combox_index):
        self.sheet_model.refresh_view(self.combobox.currentText())


#!/usr/bin/python3
import sys
from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtCore import Qt

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



class NewPasswordDialog(QtWidgets.QDialog,
                        ui.main_single_centered_dialog_ui.Ui_Dialog):
    def __init__(self, user, security_word, forbidden=None,
                 min_length=4, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)
        self.setupUi(self)

        self.secure_word = security_word
        self.forbidden = if_none(forbidden, set())
        self.min_length = min_length

        self.setWindowTitle('Enter new password for user "%s"' % user)

        self.main_widget = QtWidgets.QWidget()
        self.vlayout = QtWidgets.QVBoxLayout(self.main_widget)

        self.pwd_frame = QtWidgets.QFrame(self.main_widget)
        self.formLayout = QtWidgets.QFormLayout(self.pwd_frame)
        self.formLayout.setContentsMargins(4, 4, 9, 4)
        self.formLayout.setObjectName("formLayout")

        self.label_secure_word = QtWidgets.QLabel(self.pwd_frame)
        self.label_secure_word.setObjectName("label_security_word")
        self.label_secure_word.setText('Security word:')
        self.formLayout.setWidget(1, QtWidgets.QFormLayout.LabelRole,
                                  self.label_secure_word)
        self.secure_word_field = PasswordEdit(self.pwd_frame)
        self.secure_word_field.setFrame(True)
        self.secure_word_field.setObjectName("security_word_field")
        self.formLayout.setWidget(1, QtWidgets.QFormLayout.FieldRole,
                                  self.secure_word_field)

        self.label = QtWidgets.QLabel(self.pwd_frame)
        self.label.setObjectName("label")
        self.label.setText('New password:')
        self.formLayout.setWidget(2, QtWidgets.QFormLayout.LabelRole, self.label)
        self.pwd_field = PasswordEdit(self.pwd_frame)
        self.pwd_field.setFrame(True)
        self.pwd_field.setObjectName("pwd_field")
        self.formLayout.setWidget(2, QtWidgets.QFormLayout.FieldRole,
                                  self.pwd_field)

        self.label_confirm = QtWidgets.QLabel(self.pwd_frame)
        self.label_confirm.setObjectName("label_confirm")
        self.label_confirm.setText('Confirm password:')
        self.formLayout.setWidget(3, QtWidgets.QFormLayout.LabelRole,
                                  self.label_confirm)
        self.pwd_field_confirm = PasswordEdit(self.pwd_frame)
        self.pwd_field_confirm.setFrame(True)
        self.pwd_field_confirm.setObjectName("pwd_field_confirm")
        self.formLayout.setWidget(3, QtWidgets.QFormLayout.FieldRole,
                                  self.pwd_field_confirm)

        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        self.label_invalid = QtWidgets.QLabel(self.pwd_frame)
        self.label_invalid.setObjectName("label_invalid")
        self.label_invalid.setText('')
        self.label_invalid.setProperty("invalidity_message", True)

        self.pwd_entered_once = False
        self.pwd_field.textChanged.connect(self.on_pwd_change)
        self.pwd_field.editingFinished.connect(self.on_pwd_finished)

        self.pwd_confirm_entered_once = False
        self.pwd_field_confirm.textChanged.connect(self.on_pwd_confirm_change)
        (self.pwd_field_confirm.editingFinished
         .connect(self.on_pwd_confirm_finished))

        self.secure_word_entered_once = False
        self.secure_word_field.textChanged.connect(self.on_secure_word_change)
        (self.secure_word_field.editingFinished
         .connect(self.on_secure_word_finished))

        self.vlayout.addWidget(self.pwd_frame)
        self.vlayout.addWidget(self.label_invalid)
        self.vlayout.addWidget(self.buttonBox)

        self.vlayout_main.addWidget(self.main_widget)

        self.invalid_color = '#FEA82F' # yellow orange
        self.valid_color = '#c4df9b' # green

    def password(self):
        return self.pwd_field.text()

    @staticmethod
    def ask(user, security_word, forbidden=None, parent=None):
        dialog = NewPasswordDialog(user, security_word, forbidden=forbidden,
                                   parent=parent)
        result = dialog.exec_()
        if result == QtWidgets.QDialog.Accepted:
            return dialog.password()
        else:
            return None

    def on_pwd_change(self):
        if self.pwd_entered_once:
            self.check_pwd()

    def on_pwd_confirm_change(self):
        if self.pwd_confirm_entered_once:
            self.check_pwd_confirm()

    def on_secure_word_change(self):
        if self.secure_word_entered_once:
            self.check_secure_word()

    def on_secure_word_finished(self):
        self.secure_word_entered_once = True
        self.check_secure_word()

    def on_pwd_finished(self):
        self.pwd_entered_once = True
        self.check_pwd()

    def on_pwd_confirm_finished(self):
        self.pwd_confirm_entered_once = True
        self.check_pwd_confirm()

    def check_secure_word(self):
        if self.secure_word_field.text() != self.secure_word:
            self.label_invalid.setText('Invalid security word')
            css = 'QLineEdit { background-color: %s }' % self.invalid_color
            self.secure_word_field.setStyleSheet(css)
            return False
        else:
            self.label_invalid.setText('')
            css = 'QLineEdit { background-color: %s }' % self.valid_color
            self.secure_word_field.setStyleSheet(css)
        return True

    def check_pwd(self):
        """
        - Length of password must not be less than min length
        - Password must not be in given list of forbidden password
          (eg access password)
        """

        pwd = self.pwd_field.text()
        error = None
        if len(pwd) < self.min_length:
            error = 'Password too short'
        elif pwd in self.forbidden:
            error = 'Password not allowed'

        if error is not None:
            self.label_invalid.setText(error)
            self.pwd_field.setStyleSheet('QLineEdit { background-color: %s }' %\
                                         self.invalid_color)
            return False
        else:
            self.label_invalid.setText('')
            self.pwd_field.setStyleSheet('QLineEdit { background-color: %s }' %\
                                         self.valid_color)
        if self.pwd_confirm_entered_once:
            self.check_pwd_confirm(change_validity_message=False)
        return True

    def check_pwd_confirm(self, change_validity_message=True):
        """
        - Confirmation must match
        """
        if self.pwd_field.text() != self.pwd_field_confirm.text():
            if change_validity_message:
                self.label_invalid.setText('Confirmation password '\
                                           'does not match')
            self.label_invalid.show()
            (self.pwd_field_confirm
             .setStyleSheet('QLineEdit { background-color: %s }' %\
                            self.invalid_color))
            return False
        else:
            if change_validity_message:
                self.label_invalid.setText('')
            (self.pwd_field_confirm
             .setStyleSheet('QLineEdit { background-color: %s }' %\
                            self.valid_color))
        return True

    def accept(self):
        self.buttonBox.setFocus()
        if self.check_pwd() and self.check_pwd_confirm() and \
           self.check_secure_word():
            return super().accept()

class CreateWorkBookDialog(QtWidgets.QDialog):
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

        self.colors = ['#eddcd2', '#fff1e6', '#fde2e4', '#fad2e1', '#c5dedd',
                       '#dbe7e4', '#f0efeb', '#d6e2e9', '#bcd4e6', '#99c1de']
        self.form_ui.colorComboBox.addItems([''] * len(self.colors))
        color_cb_model = self.form_ui.colorComboBox.model()
        for irow, color in enumerate(self.colors):
            idx = color_cb_model.index(irow, 0)
            color_cb_model.setData(idx, QtGui.QColor(color),
                                   Qt.BackgroundColorRole);
        def f_show_selected_color(combo_idx):
            (self.form_ui.color_label
             .setStyleSheet("QLabel { background-color : %s ; }" % \
                            self.colors[combo_idx]))
        (self.form_ui.colorComboBox.currentIndexChanged
         .connect(f_show_selected_color))

        self.required_fields = {
            'Access password' : self.form_ui.access_pwd_field,
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
    def create(parent=None):
        dialog = CreateWorkBookDialog(parent=parent)
        result = dialog.exec_()
        if result == QtWidgets.QDialog.Accepted:
            return (dialog.workbook_cfg_fn, dialog.access_pwd,
                    dialog.admin_name, dialog.admin_pwd)
        else:
            return None, None, None, None

    def accept(self):
        if self.check() and self._make_workbook():
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
        self.access_pwd = self.form_ui.access_pwd_field.text()
        self.admin_pwd = self.form_ui.admin_pwd_field.text()
        self.admin_name = self.form_ui.adminNameLineEdit.text()
        color = self.colors[self.form_ui.colorComboBox.currentIndex()]

        try:
            wb = WorkBook.create(wb_label, fs,
                                 access_password=self.access_pwd,
                                 admin_password=self.admin_pwd,
                                 admin_user=self.admin_name,
                                 color_hex_str=color)
        except Exception as e:
            msg = 'Error while creating workbook:\n%s' % repr(e)
            show_critical_message_box(msg)
            return False

        self.workbook_cfg_fn = fs.full_path(protect_fn(wb_label) + '.psh')
        return True

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

# Helper function: single_section_form()
# When sheet data change -> send

class SheetNameValidator(QtGui.QValidator):
    def __init__(self, black_list, parent=None):
        super(SheetNameValidator, self).__init__(parent=parent)
        self.black_list = set(black_list)

    def validate(self, sheet_label, pos):
        try:
            DataSheet.validate_sheet_label(sheet_label)
        except InvalidSheetLabel:
            return QtGui.QValidator.Intermediate, sheet_label, pos

        if sheet_label in self.black_list:
            return QtGui.QValidator.Intermediate, sheet_label, pos

        return QtGui.QValidator.Acceptable, sheet_label, pos

class FileFieldValidator(QtGui.QValidator):
    def __init__(self, allow_empty=False, parent=None):
        super(FileFieldValidator, self).__init__(parent=parent)
        self.allow_empty = allow_empty

    def validate(self, file_fn, pos):
        if file_fn == '':
            if self.allow_empty:
                return QtGui.QValidator.Acceptable, file_fn, pos
            else:
                return QtGui.QValidator.Intermediate, file_fn, pos
        else:
            if op.exists(file_fn):
                return QtGui.QValidator.Acceptable, file_fn, pos
            else:
                return QtGui.QValidator.Intermediate, file_fn, pos

class SheetCreationDialog(QtWidgets.QDialog):
    def __init__(self, existing_sheet_labels=None, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)

        existing_sheet_labels = (existing_sheet_labels
                                 if existing_sheet_labels is not None
                                 else [])

        input_widget = QtWidgets.QWidget()
        self.input_widget_ui = ui.sheet_creation_ui.Ui_Form()
        self.input_widget_ui.setupUi(input_widget)

        self.name_validator = \
            SheetNameValidator(existing_sheet_labels, parent=self)
        self.input_widget_ui.sheet_name_edit.setValidator(self.name_validator)
        (self.input_widget_ui.sheet_name_edit.textChanged
         .connect(partial(self.line_edit_validity_feedback,
                          self.input_widget_ui.sheet_name_edit)))

        self.fn_validator = FileFieldValidator(allow_empty=True)
        # TODO add a status bar to the dialog window to display error feedback
        # TODO also validate if file is openable and content is valid
        # Add arg validate_content to FileFieldValidator
        self.input_widget_ui.form_file_edit.setValidator(self.fn_validator)

        (self.input_widget_ui.form_file_edit.textChanged
         .connect(partial(self.line_edit_validity_feedback,
                          self.input_widget_ui.form_file_edit)))

        self.input_widget_ui.plugin_file_edit.setValidator(self.fn_validator)
        (self.input_widget_ui.plugin_file_edit.textChanged
         .connect(partial(self.line_edit_validity_feedback,
                          self.input_widget_ui.plugin_file_edit)))

        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        button_icon = QtGui.QIcon(':/icons/file_open_icon')
        self.input_widget_ui.form_file_open_button.setIcon(button_icon)

        form_file_format = "Piccel form file (*.form)"
        on_click = partial(self.ask_open_fn, form_file_format,
                           self.input_widget_ui.form_file_edit)
        self.input_widget_ui.form_file_open_button.clicked.connect(on_click)

        plugin_file_format = "Piccel sheet plugin file (*.py)"
        on_click = partial(self.ask_open_fn, plugin_file_format,
                           self.input_widget_ui.plugin_file_edit)
        self.input_widget_ui.plugin_file_open_button.setIcon(button_icon)
        self.input_widget_ui.plugin_file_open_button.clicked.connect(on_click)

        self.layout = QtWidgets.QVBoxLayout()
        self.layout.addWidget(input_widget)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

    def line_edit_validity_feedback(self, line_edit):
        input_text = line_edit.text()
        state = line_edit.validator().validate(input_text, 0)[0]
        if state == QtGui.QValidator.Acceptable:
            color = '#c4df9b' # green
        elif state == QtGui.QValidator.Intermediate:
            color = '#FEA82F' # yellow orange
        else:
            color = '#f6989d' # red
        line_edit.setStyleSheet('QLineEdit { background-color: %s }' % color)

    def accept(self):
        try:
            self.get_sheet()
        except Exception as e:
            show_critical_message_box('Error while creating sheet:\n%s' %\
                                      repr(e))
            return
        super().accept()

    # def is_valid(self):
    #     try:
    #         self.get_sheet()
    #     except Exception:
    #         return False
    #     return True

    def get_sheet(self):

        def empty_or_fn_exists(fn):
            return fn=='' or op.exists(fn)

        form_fn = self.input_widget_ui.form_file_edit.text()
        plugin_fn = self.input_widget_ui.plugin_file_edit.text()

        if not self.input_widget_ui.sheet_name_edit.hasAcceptableInput():
            raise Exception('Invalid sheet name')

        label = self.input_widget_ui.sheet_name_edit.text()
        return DataSheet(label, form_master=self._get_form(),
                         plugin_code_str=self._get_plugin_str())

    def ask_open_fn(self, fn_format, dest_line_edit):
        fn, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Open file',
                                                   '', fn_format)
        if fn is not None and fn != '':
            dest_line_edit.setText(fn)

    @staticmethod
    def new_sheet(existing_sheet_labels=None, parent=None):
        dialog = SheetCreationDialog(existing_sheet_labels=existing_sheet_labels,
                                     parent=parent)
        result = dialog.exec_()
        if result == QtWidgets.QDialog.Accepted:
            return dialog.get_sheet()
        return None

    def _get_form(self):
        form_fn = self.input_widget_ui.form_file_edit.text()
        if form_fn == '':
            form = None
        elif not op.exists(form_fn):
            raise IOError('Form file does not exists: %s' % form_fn)
        else:
            form = Form.from_json_file(form_fn)

        return form

    def _get_plugin_str(self):
        plugin_fn = self.input_widget_ui.plugin_file_edit.text()
        if plugin_fn == '':
            plugin_str = None
        elif not op.exists(plugin_fn):
            raise IOError('Plugin file does not exists: %s' % plugin_fn)
        else:
            with open(plugin_fn, 'r') as fin:
                plugin_str = fin.read()
        return plugin_str

class TabSorter:
    def __init__(self, tab_widget):

        self.sheet_widgets = {}
        self.live_form_widgets = {}
        self.form_editors_widgets = {}
        self.plugin_editors_widgets = {}

        self.tab_widget = tab_widget

        self.editor_icon = QtGui.QIcon(':/icons/editor_icon')
        self.warning_icon = QtGui.QIcon(':/icons/alert_icon')
        self.null_icon = QtGui.QIcon()

        self.clear()

    def clear(self):

        for widgets in (self.sheet_widgets, self.live_form_widgets,
                        self.form_editors_widgets, self.plugin_editors_widgets):
            widgets.clear()

        for tab_idx in reversed(range(self.tab_widget.count())):
            w = self.tab_widget.widget(tab_idx)
            self.tab_widget.removeTab(tab_idx)
            del w

    def to_first(self):
        self.tab_widget.setCurrentIndex(0)

    def to_sheet(self, sheet_label):
        tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet_label])
        self.tab_widget.setCurrentIndex(tab_idx)

    def show_tab_sheet(self, sheet, user_role):
        if sheet.label in self.sheet_widgets:
            logger.debug('Tab already exists for sheet %s', sheet.label)
            tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet.label])
        else:
            logger.debug('Create tab for sheet %s', sheet.label)
            sheet_widget = SheetWidget(sheet, user_role, self,
                                       parent=self.tab_widget)
            self.sheet_widgets[sheet.label] = sheet_widget

            nb_tabs = self.tab_widget.count()
            if not sheet.label.startswith('__'):
                tab_idx = next((i for i in range(nb_tabs)
                                if self.tab_widget.tabText(i).startswith('__')),
                               nb_tabs)
            else:
                tab_idx = nb_tabs
            tab_idx = self.tab_widget.insertTab(tab_idx, sheet_widget, sheet.label)
        if not sheet.plugin_is_valid():
            self.show_tab_sheet_warning(sheet.label, sheet.plugin_error_reporting)
        self.tab_widget.setCurrentIndex(tab_idx)

    def close_tab_sheet(self, sheet_label):
        """
        Remove tab showing given sheet and set focus on previous tab or
        on next one if removed sheet was the first.
        """
        tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet_label])
        self.tab_widget.removeTab(tab_idx)
        self.sheet_widgets.pop(sheet_label)

    def show_tab_sheet_warning(self, sheet_name, reporting=None):
        tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet_name])
        self.tab_widget.setTabIcon(tab_idx, self.warning_icon)
        if reporting is not None:
            show_critical_message_box('Error in %s:\n%s' % \
                                      (sheet_name, reporting))

    def hide_tab_sheet_warning(self, sheet_name):
        tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet_name])
        self.tab_widget.setTabIcon(tab_idx, self.null_icon)

    def add_tab_report(self, report, tab_name):
        report_widget = ReportWidget(report.content, report.header, report.footer)
        tab_idx = self.tab_widget.insertTab(0, report_widget, tab_name)
        tab_icon = QtGui.QIcon(':/icons/text_icon')
        self.tab_widget.setTabIcon(tab_idx, tab_icon)
        self.tab_widget.setCurrentIndex(tab_idx)

    def add_tab_live_form(self, live_form, tab_name, origin_sheet_label,
                          user_role=UserRole.EDITOR):
        """
        Add tab before given origin_sheet or after if origin_sheet is first
        """
        # TODO: add parameter insert after, to be used when form originates
        #       from Dashboard
        form_widget = FormWidget(live_form, origin_sheet_label,
                                 close_callback=self.close_tab_live_form,
                                 user_role=user_role,
                                 parent=self.tab_widget)
        sheet_widget = self.sheet_widgets[origin_sheet_label]
        origin_tab_idx = self.tab_widget.indexOf(sheet_widget)

        tab_idx = self.tab_widget.insertTab(origin_tab_idx, form_widget, tab_name)
        tab_icon = QtGui.QIcon(':/icons/form_input_icon')
        self.tab_widget.setTabIcon(tab_idx, tab_icon)
        self.tab_widget.setCurrentIndex(tab_idx)

        self.live_form_widgets[id(form_widget)] = form_widget

    def close_tab_live_form(self, form_widget):
        """ Remove tab showing given form and set focus on origin sheet """
        self.live_form_widgets.pop(id(form_widget))
        self.tab_widget.removeTab(self.tab_widget.indexOf(form_widget))
        sheet_widget = self.sheet_widgets[form_widget.origin_sheet_label]
        self.tab_widget.setCurrentIndex(self.tab_widget.indexOf(sheet_widget))

    def show_tab_form_editor(self, sheet):
        if sheet.label in self.form_editors_widgets:
            editor_widget = self.form_editors_widgets[sheet.label]
            tab_idx = self.tab_widget.indexOf(editor_widget)
            self.tab_widget.setCurrentIndex(tab_idx)
        else:
            on_close = partial(self.close_tab_form_editor, sheet.label)
            try:
                editor_widget = FormSheetEditor(sheet, on_close,
                                                parent=self.tab_widget)
            except FormEditionCancelled:
                return
            tab_label = '%s | Form edit' % sheet.label
            self.form_editors_widgets[sheet.label] = editor_widget
            tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet.label])+1
            self.tab_widget.insertTab(tab_idx, editor_widget, self.editor_icon,
                                      tab_label)
            self.tab_widget.setCurrentIndex(tab_idx)

    def _close_tab_editor(self, sheet_name, widgets):
        editor_widget = widgets.pop(sheet_name)
        self.tab_widget.removeTab(self.tab_widget.indexOf(editor_widget))

        sheet_widget = self.sheet_widgets[sheet_name]
        self.tab_widget.setCurrentIndex(self.tab_widget.indexOf(sheet_widget))

    def close_tab_form_editor(self, sheet_name):
        self._close_tab_editor(sheet_name, self.form_editors_widgets)

    def show_tab_plugin_editor(self, sheet):
        if sheet.label in self.plugin_editors_widgets:
            editor_widget = self.plugin_editors_widgets[sheet.label]
            tab_idx = self.tab_widget.indexOf(editor_widget)
            self.tab_widget.setCurrentIndex(tab_idx)
        else:
            def _set_plugin(text):
                try:
                    sheet.set_plugin_from_code(text)
                    sheet.save_plugin_code(overwrite=True)
                    sheet.reload_all_data()
                    # TODO: live forms are not loaded and not displayed in UI
                except Exception as e:
                    msg = 'Error while setting plugin:\n%s' % repr(e)
                    show_critical_message_box(msg)
                    return False
                return True

            _on_close = partial(self.close_tab_plugin_editor, sheet.label)
            text_editor = TextEditorWidget(sheet.get_plugin_code(),
                                           submit=_set_plugin,
                                           close_callback=_on_close)
            self.plugin_editors_widgets[sheet.label] = text_editor

            tab_idx = self.tab_widget.indexOf(self.sheet_widgets[sheet.label])+1
            tab_idx = self.tab_widget.insertTab(tab_idx, text_editor,
                                                self.editor_icon, sheet.label)
            self.tab_widget.setCurrentIndex(tab_idx)

    def close_tab_plugin_editor(self, sheet_name):
        self._close_tab_editor(sheet_name, self.plugin_editors_widgets)

from .plugin_tools import Report

class ReportWidget(QtWidgets.QWidget, ui.report_ui.Ui_Form):
    def __init__(self, content_html, header_text=None, footer_text=None,
                 title=None, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        if header_text is None:
            self.report_header_label.hide()
        else:
            self.report_header_label.setText(header_text)

        if footer_text is None:
            self.report_footer_label.hide()
        else:
            self.report_footer_label.setText(footer_text)

        self.report_content.setHtml(content_html)

        if title is not None:
            self.setWindowTitle(title)

class TextEditorWidget(QtWidgets.QWidget, ui.text_editor_ui.Ui_Form):
    def __init__(self, text, submit, close_callback=None, title='Text editor',
                 parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.title_label.setText(title)

        self.close_callback = if_none(close_callback, self.close)
        self.submit = submit
        self.textBrowser.setText(text)

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

        self.button_cancel.clicked.connect(self.on_cancel)
        self.button_apply.clicked.connect(self.on_apply)
        self.button_ok.clicked.connect(self.on_ok)

    def on_apply(self):
        self.submit(self.textBrowser.toPlainText())

    def on_cancel(self):
        # TODO process pending changes
        self.close_callback()

    def on_ok(self):
        if self.submit(self.textBrowser.toPlainText()):
            self.close_callback()


class SheetWidget(QtWidgets.QWidget, ui.data_sheet_ui.Ui_Form):
    def __init__(self, sheet, user_role, tab_sorter, parent=None):
        # TODO: user_role should be determined by given sheet...
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.tab_sorter = tab_sorter

        #self.cell_value_frame.hide()

        # button_icon = QtGui.QIcon(':/icons/refresh_icon')
        # self.button_refresh.setIcon(button_icon)
        # self.button_refresh.clicked.connect(sh.refresh_data)

        model = DataSheetModel(sheet)

        self.tableView.setModel(model)
        hHeader = self.tableView.horizontalHeader()
        hHeader.setMaximumSectionSize(400) # TODO expose param
        #hHeader.setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)

        vHeader = self.tableView.verticalHeader()
        #vHeader.setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)

        def resize_table_view(*args, **kwargs):
            self.tableView.resizeRowsToContents()
            self.tableView.resizeColumnsToContents()

        for notification in ['appended_entry', 'entry_set',
                             'deleted_entry', 'clear_data']:
            sheet.notifier.add_watcher(notification, resize_table_view)

        resize_table_view()

        def f_cell_action(idx):

            row_df = model.entry_df(idx)
            if idx.column()==0 and row_df.index.name is not None:
                column = row_df.index.name
            else:
                column = row_df.columns[idx.column()-(row_df.index.name is not None)]
            logger.debug('f_cell_action, idx.row=%d, idx.col=%d, column=%s',
                         idx.row(), idx.column(), column)
            try:
                action_result, action_label = sheet.action(row_df, column)
            except Exception as e:
                error_message = ('Error calling action for sheet %s' %
                                 sheet.label)
                details = format_exc()
                logger.error('%s\n%s', error_message, details)
                show_critical_message_box(repr(e))
                action_result = None

            if action_result is None:
                return

            if isinstance(action_result, Form):
                self.tab_sorter.add_tab_live_form(action_result, action_label,
                                                  sheet.label,
                                                  user_role=sheet.user_role)
                # self.make_form_tab(action_label, model, self,
                #                    self._workbook_ui.tabWidget,
                #                    tab_idx=max(1,self.tab_indexes[sh_name]-1),
                #                    form=action_result)
            if isinstance(action_result, Report):
                report = action_result
                self.report_widget = ReportWidget(report.content, report.header,
                                                  report.footer,
                                                  title=action_label)
                self.report_widget.show()

                # self.tab_sorter.add_tab_report(action_result, action_label)
            else:
                logger.debug('action result: %s', action_result)

        self.tableView.doubleClicked.connect(f_cell_action)
        self.tableView.frozenTableView.doubleClicked.connect(f_cell_action)

        def show_details(idx):
            self.cell_value.setText(model.data(idx))
            self.cell_value_frame.show()

        self.tableView.clicked.connect(show_details)

        def f_edit_entry():
            idx = self.tableView.currentIndex()
            entry_id = model.entry_id(idx)
            logger.debug('set_entry: idx.row=%s, entry_id=%s',
                         idx.row(), entry_id)
            self.tab_sorter.add_tab_live_form(sheet.form_set_entry(entry_id),
                                              sheet.label,
                                              origin_sheet_label=sheet.label,
                                              user_role=sheet.user_role)

        def f_delete_entry():
            idx = self.tableView.currentIndex()
            entry_id = model.entry_id(idx)
            logger.debug('delete_entry: idx.row=%s, entry_id=%s',
                         idx.row(), entry_id)
            sheet.delete_entry(entry_id)

        if sheet.form_master is not None: #TODO: and user is admin
            self.button_edit_entry.clicked.connect(f_edit_entry)
        else:
            self.button_edit_entry.hide()

        def f_new_entry():
            self.tab_sorter.add_tab_live_form(sheet.form_new_entry(),
                                              tab_name=sheet.label,
                                              origin_sheet_label=sheet.label,
                                              user_role=sheet.user_role)

        if sheet.form_master is not None and \
           sheet.has_write_access: #TODO: and user is admin
            self.button_new_entry.clicked.connect(f_new_entry)
            (self.button_delete_entry
             .clicked.connect(f_delete_entry))
            # new_entry_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("N"),
            #                                      sheet_widget)
            # new_entry_shortcut.activated.connect(f_new_entry)
        else:
            self.button_new_entry.hide()

        self.comboBox_view.addItems(list(sheet.views.keys()))
        self.comboBox_view.setCurrentText(sheet.default_view)
        f = SheetViewChanger(self.comboBox_view, model)
        self.comboBox_view.currentIndexChanged.connect(f)

        # if sh_name.startswith('__'):
        #     tab_idx = (self._workbook_ui.tabWidget
        #                .addTab(sheet_widget, sh_name))
        # else:
        #     #TODO: better handle sheet order. This only works if
        #     # there is only one sheet starting with "__"
        #     insert_idx = max(1, self._workbook_ui.tabWidget.count()-1)
        #     tab_idx = (self._workbook_ui.tabWidget
        #                .insertTab(insert_idx, sheet_widget, sh_name))
        # self.tab_indexes[sh_name] = tab_idx


        sheet.notifier.add_watcher('plugin_invalid',
                                   partial(self.tab_sorter.show_tab_sheet_warning,
                                           sheet.label))

        sheet.notifier.add_watcher('plugin_valid',
                                   partial(self.tab_sorter.hide_tab_sheet_warning,
                                           sheet.label))

        f_form_editor = partial(self.tab_sorter.show_tab_form_editor, sheet)
        self.button_edit_form.clicked.connect(f_form_editor)

        # f_plugin_editor = partial(self.tab_sorter.show_tab_plugin_editor,
        #                           sheet)
        # self.button_edit_plugin.clicked.connect(f_plugin_editor)

        if user_role < UserRole.MANAGER:
            self.button_edit_form.hide()
            # self.button_edit_plugin.hide()

        if user_role < UserRole.ADMIN or sheet.form_master is None:
            self.button_delete_entry.hide()
            self.button_edit_entry.hide()

        # for form_id, form in sheet.live_forms.items():
        #     logger.info('Load pending form "%s" (%s)',
        #                 form.tr['title'], form_id)
        #     self.tab_sorter.add_tab_live_form(form, sheet.label,
        #                                       origin_sheet_label=sheet.label)

            # self.make_form_tab(sh_name, model, self,
            #                    self._workbook_ui.tabWidget,
            #                    self.tab_indexes[sh_name]+1, form)

class SelectorWindow(QtWidgets.QMainWindow,
                     ui.main_single_centered_widget_ui.Ui_MainWindow):
    def __init__(self, recent_files, open_file, on_create, parent=None):
        super(QtWidgets.QMainWindow, self).__init__(parent)
        self.setupUi(self)

        self.open_file = open_file
        self.on_create = on_create

        self.selector = QtWidgets.QWidget()
        _selector_ui = ui.selector_widget_ui.Ui_Form()
        _selector_ui.setupUi(self.selector)
        self.vlayout_main.addWidget(self.selector)

        button_icon = QtGui.QIcon(':/icons/file_open_icon')
        _selector_ui.button_open_file.setIcon(button_icon)
        _selector_ui.button_open_file.clicked.connect(self.select_file)

        button_icon = QtGui.QIcon(':/icons/file_create_icon')
        _selector_ui.button_create.setIcon(button_icon)
        _selector_ui.button_create.clicked.connect(self.on_create)

        self.recent_files = recent_files

        def load_workbook_info(wb_fn):
            try:
                with open(wb_fn, 'r') as fin:
                    wb_cfg = json.load(fin)
            except Exception as e:
                msg = ('Error loading workbook file %s:\n %s' % \
                       (wb_fn, repr(e)))
                logger.error(msg)
                show_critical_message_box(msg)
            return wb_cfg['workbook_label'], wb_cfg.get('color_hex_str', None)

        self.wbs_info = []
        for wb_cfg_fn in sorted(self.recent_files):
            wb_title, wb_color = load_workbook_info(wb_cfg_fn)
            self.wbs_info.append((wb_title, wb_color, wb_cfg_fn))

        self.wbs_info.sort(key=lambda e: e[0])
        for wb_title, wb_color, wb_cfg_fn in self.wbs_info:
            if wb_title is not None:
                list_item = QtWidgets.QListWidgetItem(wb_title)
                if wb_color is not None:
                    list_item.setBackground(QtGui.QColor(wb_color))
                _selector_ui.recent_list.addItem(list_item)

        def _cfg_fn():
            return self.wbs_info[_selector_ui.recent_list.currentRow()][2]
        on_double_click = lambda i: self.open_file(_cfg_fn())
        _selector_ui.recent_list.itemDoubleClicked.connect(on_double_click)

        on_click = lambda i: self.statusBar().showMessage(_cfg_fn())
        _selector_ui.recent_list.itemClicked.connect(on_click)

        self.statusBar().showMessage("Ready")

    def select_file(self):
        fn_format = "Piccel file (*.psh *.form)"
        fn, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Open file',
                                                      '', fn_format)
        logger.debug('Open file %s', fn)
        self.open_file(fn)

class AccessWindow(QtWidgets.QMainWindow,
                   ui.main_single_centered_widget_ui.Ui_MainWindow):
    def __init__(self, access_process, access_cancel, parent=None):
        super(QtWidgets.QMainWindow, self).__init__(parent)
        self.setupUi(self)

        self.wb_label, self.wb_color, self.access_pwd = None, None, None

        self.access_process = access_process
        self.access_cancel = access_cancel

        self.access_widget = QtWidgets.QWidget()
        self._access_ui = ui.access_widget_ui.Ui_Form()
        self._access_ui.setupUi(self.access_widget)
        self._access_ui.button_cancel.clicked.connect(self.access_cancel)
        self._access_ui.button_ok.clicked.connect(self.access_process)
        access_ok_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Return"),
                                                 self.access_widget)
        access_ok_shortcut.activated.connect(self.access_process)
        access_cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                                     self.access_widget)
        access_cancel_shortcut.activated.connect(self.access_cancel)

        self.vlayout_main.addWidget(self.access_widget)

    def on_ok(self):
        pwd_text = self._access_ui.access_password_field.text()
        self.access_password = pwd_text if pwd_text != '' else None

    def disable_inputs(self):
        self._access_ui.button_ok.setEnabled(False)
        self._access_ui.button_cancel.setEnabled(False)

    def enable_inputs(self):
        self._access_ui.button_ok.setEnabled(True)
        self._access_ui.button_cancel.setEnabled(True)

    def access_password(self):
        pwd_text = self._access_ui.access_password_field.text()
        return pwd_text if pwd_text != '' else None

    def set_wb_info(self, wb_label, wb_color, access_pwd):
        self.wb_label = wb_label
        self.wb_color = wb_color
        self.access_pwd = access_pwd

    def show(self):
        super(QtWidgets.QMainWindow, self).show()

        self._access_ui.button_ok.setEnabled(True)
        self._access_ui.button_cancel.setEnabled(True)

        self._access_ui.workbook_label.setText(self.wb_label)
        if self.wb_color is not None:
            ss = "QFrame { background-color : %s; }" % self.wb_color
            self._access_ui.title_frame.setStyleSheet(ss)

        self._access_ui.access_password_field.clear()
        if self.access_pwd is not None:
            self._access_ui.access_password_field.setText(self.access_pwd)


class LoginWindow(QtWidgets.QMainWindow,
                   ui.main_single_centered_widget_ui.Ui_MainWindow):
    def __init__(self, login_preload_user, login_process, login_cancel,
                 parent=None):
        super(QtWidgets.QMainWindow, self).__init__(parent)
        self.setupUi(self)

        self.login_widget = QtWidgets.QWidget()
        self._login_ui = ui.login_widget_ui.Ui_Form()
        self._login_ui.setupUi(self.login_widget)

        self._login_ui.other_password_label.setText('User password:')

        self.login_preload_user = login_preload_user
        self._login_ui.user_list.currentTextChanged.connect(self.on_user_change)
        self._login_ui.button_cancel.clicked.connect(login_cancel)
        self._login_ui.button_ok.clicked.connect(login_process)
        login_ok_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Return"),
                                                self)
        login_ok_shortcut.activated.connect(login_process)
        login_cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                                    self)
        login_cancel_shortcut.activated.connect(login_cancel)

        self.vlayout_main.addWidget(self.login_widget)

    def on_user_change(self, user):
        self._login_ui.roleComboBox.clear()
        self._login_ui.other_password_field.clear()
        if user == '':
            return
        new_pwd, user_role = self.login_preload_user(user)
        if new_pwd is not None:
            self._login_ui.other_password_field.setText(new_pwd)
            logger.debug('LoginWindow: login_preload_user returned new password')
        else:
            logger.debug('LoginWindow: login_preload_user returned no new pwd')
        for role in reversed(UserRole):
            if role <= user_role:
                self._login_ui.roleComboBox.addItem(role.name)
        self._login_ui.roleComboBox.setCurrentText(user_role.name)

    def ___login_preload_user(self, user):
        self._login_ui.other_password_label.show()
        self._login_ui.other_password_field.hide()

        if user is not None and user != '':
            role = self.get_user_role(user)

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

    def disable_inputs(self):
        self._login_ui.button_ok.setEnabled(False)
        self._login_ui.button_cancel.setEnabled(False)

    def enable_inputs(self):
        self._login_ui.button_ok.setEnabled(True)
        self._login_ui.button_cancel.setEnabled(True)

    def set_users(self, user_names):
        self._login_ui.user_list.clear()
        self._login_ui.user_list.addItems(user_names)

    def set_workbook_info(self, wb_label, wb_color):
        self._login_ui.workbook_label.setText(wb_label)
        if wb_color is not None:
            ss = "QFrame { background-color : %s; }" % wb_color
            self._login_ui.title_frame.setStyleSheet(ss)

    def reset_role_pwd(self, role_pwd):
        self._login_ui.other_password_field.clear()
        if role_pwd is not None:
            self._login_ui.other_password_field.setText(role_pwd)

    def login_info(self):
        user = self._login_ui.user_list.currentText()
        role_pwd_input = self._login_ui.other_password_field.text()
        role_pwd = role_pwd_input if role_pwd_input != '' else None
        return user, role_pwd, UserRole[self._login_ui.roleComboBox.currentText()]

class PiccelApp(QtWidgets.QApplication):

    USER_FILE = 'piccel.json'

    def __init__(self, argv, fn=None, user=None, access_pwd=None,
                 role_pwd=None, cfg_fns=None, refresh_rate_ms=0):
        super(PiccelApp, self).__init__(argv)

        self.setStyle('Fusion')
        self.setStyleSheet(ui.main_qss.main_style)
        Hints.preload(self)

        self.sheet_icon = QtGui.QIcon(':/icons/sheet_icon')
        self.sheet_add_icon = QtGui.QIcon(':/icons/add_icon')
        self.job_add_icon = QtGui.QIcon(':/icons/add_icon')
        self.editor_icon = QtGui.QIcon(':/icons/editor_icon')

        self.delete_icon = QtGui.QIcon(':/icons/form_delete_icon')
        self.plugin_icon = QtGui.QIcon(':/icons/plugin_icon')
        self.warning_icon = QtGui.QIcon(':/icons/alert_icon')

        self.refresh_rate_ms = refresh_rate_ms

        # icon_style = QtWidgets.QStyle.SP_ComputerIcon
        # self.setWindowIcon(self.style().standardIcon(icon_style))
        self.setWindowIcon(QtGui.QIcon(':/icons/main_icon'))
        self.logic = PiccelLogic(UserData(PiccelApp.USER_FILE))

        if cfg_fns is None:
            recent_files = self.logic.get_recent_files()
        else:
            logger.debug('Available cfg fn: %s', cfg_fns)
            recent_files = cfg_fns

        self.selector_screen = SelectorWindow(recent_files, self.open_file,
                                              self.on_create)
        # self.selector_screen = QtWidgets.QWidget()
        # _selector_ui = ui.selector_ui.Ui_Form()
        # _selector_ui.setupUi(self.selector_screen)

        self.access_screen = AccessWindow(self.access_process,
                                          self.access_cancel)

        self.login_screen = LoginWindow(self.login_preload_user,
                                        self.login_process,
                                        self.login_cancel)

        self.workbook_screen = WorkBookWindow()
        self._workbook_ui = self.workbook_screen.workbook_ui

        menu_icon = QtGui.QIcon(':/icons/workbook_tab_menu_icon')
        self._workbook_ui.button_menu.setIcon(menu_icon)

        def _make_menu():
            menu = QtWidgets.QMenu(self._workbook_ui.tabWidget)
            actions = []

            for sheet_label in self.logic.workbook.sheets:
                go_to_action = QtWidgets.QAction(self.sheet_icon,
                                                 sheet_label,
                                                 self._workbook_ui.tabWidget)
                go_to_action.triggered.connect(partial(self.tab_sorter.to_sheet,
                                                       sheet_label))
                actions.append(go_to_action)

            if self.logic.workbook.user_role >= UserRole.MANAGER:
                separator = QtWidgets.QAction('', self._workbook_ui.tabWidget)
                separator.setSeparator(True)
                actions.append(separator)

                add_sheet_action = QtWidgets.QAction(self.sheet_add_icon,
                                                     'Create sheet',
                                                     self._workbook_ui.tabWidget)
                add_sheet_action.triggered.connect(self.on_add_sheet)
                actions.append(add_sheet_action)

                add_sheets_act = QtWidgets.QAction(self.sheet_add_icon,
                                                   'Import sheets',
                                                   self._workbook_ui.tabWidget)
                add_sheets_act.triggered.connect(self.on_add_sheets)
                actions.append(add_sheets_act)

            for action in actions:
                menu.addAction(action)

            if self.logic.workbook.user_role >= UserRole.ADMIN:
                sheet_del_menu = menu.addMenu(self.delete_icon,
                                              'Delete sheet')
                for sheet_label in self.logic.workbook.sheets:
                    if not sheet_label.startswith('__'):
                        del_act = QtWidgets.QAction(self.sheet_icon,
                                                    sheet_label,
                                                    self._workbook_ui.tabWidget)
                        del_act.triggered.connect(partial(self.on_del_sheet,
                                                          sheet_label))
                        sheet_del_menu.addAction(del_act)

                separator = QtWidgets.QAction('', self._workbook_ui.tabWidget)
                separator.setSeparator(True)
                menu.addAction(separator)

                code_menu = menu.addMenu(self.plugin_icon, 'Code')
                sheet_plugin_menu = code_menu.addMenu(self.sheet_icon,
                                                      'Edit sheet plugin')
                for sheet_label, sheet in self.logic.workbook.sheets.items():
                    edit_act = QtWidgets.QAction(self.sheet_icon,
                                                 sheet_label,
                                                 self._workbook_ui.tabWidget)
                    f_edit = partial(self.tab_sorter.show_tab_plugin_editor,
                                     sheet)
                    edit_act.triggered.connect(f_edit)
                    sheet_plugin_menu.addAction(edit_act)

                separator = QtWidgets.QAction('', self._workbook_ui.tabWidget)
                separator.setSeparator(True)
                code_menu.addAction(separator)

                job_defs = [(job_name, job.icon())
                            for job_name, job
                            in self.logic.workbook.jobs.items()]
                job_defs.extend((job_name, self.warning_icon)
                                for job_name in self.logic.workbook.jobs_invalidity)
                logger.debug('job_defs to show in menu: %s', job_defs)
                for job_name, job_icon in job_defs:
                    if (job_name.startswith('__') and
                        self.logic.workbook.user_role < UserRole.ADMIN):
                        continue
                    job_menu = code_menu.addMenu(job_icon, job_name)

                    del_act = QtWidgets.QAction(self.delete_icon,
                                                'Delete',
                                                self._workbook_ui.tabWidget)
                    del_act.triggered.connect(partial(self.on_del_job,
                                                      job_name))
                    job_menu.addAction(del_act)

                    edit_act = QtWidgets.QAction(self.editor_icon,
                                                 'Edit',
                                                 self._workbook_ui.tabWidget)
                    edit_act.triggered.connect(partial(self.on_edit_job,
                                                       job_name))
                    job_menu.addAction(edit_act)

                    edit_act = QtWidgets.QAction(self.editor_icon,
                                                 'Rename',
                                                 self._workbook_ui.tabWidget)
                    edit_act.triggered.connect(partial(self.on_rename_job,
                                                       job_name))
                    job_menu.addAction(edit_act)

                import_act = QtWidgets.QAction(self.job_add_icon,
                                             'Import job',
                                             self._workbook_ui.tabWidget)
                import_act.triggered.connect(self.on_import_job)
                code_menu.addAction(import_act)

                separator = QtWidgets.QAction('', self._workbook_ui.tabWidget)
                separator.setSeparator(True)
                code_menu.addAction(separator)

                wb_plugin_act = QtWidgets.QAction(self.plugin_icon,
                                                  'Edit workbook plugin',
                                                  self._workbook_ui.tabWidget)
                wb_plugin_act.triggered.connect(self.on_wb_plugin_edit)
                code_menu.addAction(wb_plugin_act)

            menu.exec_(QtGui.QCursor.pos(), actions[-1])

        self._workbook_ui.button_menu.clicked.connect(_make_menu)

        self._workbook_ui.button_close.setIcon(QtGui.QIcon(':/icons/close_icon'))
        self._workbook_ui.button_close.clicked.connect(self.close_workbook)

        self._workbook_ui.job_list.itemClicked.connect(self.on_job_item_click)

        self.tab_sorter = TabSorter(self._workbook_ui.tabWidget)

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

        self.form_editor = None

        self.open_file(fn)
        if self.logic.workbook is not None and \
           self.access_pwd is not None:
            self.access_process()
            if self.default_user is not None and \
               self.role_pwd is not None:
                self.login_process()

    def on_wb_plugin_edit(self):
        logger.debug('Edit workbook plugin')

        def _set_plugin(content):
            logger.debug('Set workbook plugin from editor')
            self.logic.workbook.dump_common_plugin(content)
            show_info_message_box('Close and reopen workbook to apply changes')
            return True

        plugin_code = self.logic.workbook.get_common_plugin_code()
        self.wb_plugin_editor = TextEditorWidget(plugin_code,
                                                 submit=_set_plugin)
        self.wb_plugin_editor.show()

    def on_del_job(self, job_name):
        logger.info('Delete job %s', job_name)
        ask = QtWidgets.QMessageBox(self.workbook_screen)
        ask.setWindowTitle("Confirm deletion")
        ask.setText("Confirm deletion of job %s" % job_name)
        ask.setStandardButtons(QtWidgets.QMessageBox.Yes |
                               QtWidgets.QMessageBox.No)
        ask.setIcon(QtWidgets.QMessageBox.Question)
        answer = ask.exec()
        if answer == QtWidgets.QMessageBox.Yes:
            self.logic.workbook.delete_job(job_name)
            self.refresh_job_buttons()

    def on_rename_job(self, job_name):
        logger.info('TODO rename job %s (maybe?)', job_name)

    def on_edit_job(self, job_name):
        logger.info('Edit job %s', job_name)

        def _set_job(content):
            logger.debug('Set workbook job from editor')
            self.logic.workbook.set_job_code(job_name, content, save=True)
            self.refresh_job_buttons()
            return True

        job_code = self.logic.workbook.jobs_code[job_name]
        self.job_editor = TextEditorWidget(job_code,
                                           submit=_set_job)
        self.job_editor.show()

    def on_job_item_click(self, item):
        job_name = item.data(QtCore.Qt.UserRole)[len('Job_'):]
        try:
            self.logic.workbook.run_job(job_name, self.ask_input)
        except:
            msg = 'Error while running job %s:' % job_name
            details = format_exc()
            logger.error('%s\n%s', msg, details)
            show_critical_message_box(msg, detailed_text=details)

    def ask_input(self, label, input_type=InputType.TEXT, parent_widget=None):
        ask_box = QtWidgets.QDialog(parent=parent_widget)
        input_ui = ui.single_input_dialog_ui.Ui_Dialog()
        input_ui.setupUi(ask_box)
        input_ui.input_label.setText(label)
        input_ui.select_button.hide()
        if input_type==InputType.PASSWORD:
            input_ui.input_field.setEchoMode(QtWidgets.QLineEdit.Password)
        elif input_type in [InputType.FOLDER, InputType.FILE_OUT,
                            InputType.FILE_IN]:
            input_ui.select_button.show()
            f_select = partial(self.ask_file, input_type, input_ui.input_field)
            input_ui.select_button.clicked.connect(f_select)
        result = ask_box.exec_()
        if result == QtWidgets.QDialog.Accepted:
            ask_box.close()
            return input_ui.input_field.text()
        return None

    def ask_file(self, file_type, dest_field):
        path = None
        if file_type==InputType.FOLDER:
            path = (QtWidgets.QFileDialog
                    .getExistingDirectory(None, 'Select directory', '',
                                          QtWidgets.QFileDialog.ShowDirsOnly))
        elif file_type==InputType.FILE_OUT:
            path, _ = (QtWidgets.QFileDialog
                       .getSaveFileName(None, 'Select file', '',
                                        QtWidgets.QFileDialog.ShowDirsOnly))
        elif file_type==InputType.FILE_IN:
            path, _ = (QtWidgets.QFileDialog
                       .getOpenFileName(None, 'Select file', '',
                                        QtWidgets.QFileDialog.ShowDirsOnly))

        if path is not None and path != '':
            dest_field.setText(path)

    def refresh_job_buttons(self):
        self._workbook_ui.job_list.clear()

        logger.info('Adding job buttons for %s',
                    ', '.join(self.logic.workbook.jobs))
        for job_name, job in self.logic.workbook.jobs.items():
            job_user = job.who_can_run()
            if ((job_user is None or
                 job_user == self.logic.workbook.user) and
                self.logic.workbook.user_role >= job.min_access_level()):
                icon = job.icon()
                item = QtWidgets.QListWidgetItem(icon, '')
                item.setData(QtCore.Qt.UserRole, 'Job_%s' % job_name)
                description = job.description()
                if description is not None and len(description) > 0:
                    item.setData(QtCore.Qt.ToolTipRole, description)
                else:
                    item.setData(QtCore.Qt.ToolTipRole, job_name)
                self._workbook_ui.job_list.addItem(item)

    def on_import_job(self):
        logger.info('Import job')
        fn_format = "Piccel job file (*.py)"
        fn, _ = QtWidgets.QFileDialog.getOpenFileName(self._workbook_ui,
                                                      'Open file',
                                                      '', fn_format)
        if fn is not None and len(fn) > 0:
            with open(fn, 'r') as fin:
                job_code = fin.read()
            try:
                (self.logic.workbook
                 .set_job_code(op.splitext(op.basename(fn))[0], job_code,
                               save=True))
                self.refresh_job_buttons()
            except InvalidJobCode as e:
                show_critical_message_box('Error in job code',
                                          detailed_text=e.error_message)
            except InvalidJobName as e:
                show_critical_message_box('Invalid job name. It must be a ' \
                                          'valid identifier  (only '\
                                          'alpha-numeric characters and '\
                                          'underscores, 1st character is a '\
                                          'letter or an underscore)',
                                          detailed_text=e.error_message)

    def on_del_sheet(self, sheet_label):
        logger.info('Delete sheet %s', sheet_label)
        ask = QtWidgets.QMessageBox(self.workbook_screen)
        ask.setWindowTitle("Confirm deletion")
        ask.setText("Confirm deletion of %s" % sheet_label)
        ask.setStandardButtons(QtWidgets.QMessageBox.Yes |
                               QtWidgets.QMessageBox.No)
        ask.setIcon(QtWidgets.QMessageBox.Question)
        answer = ask.exec()
        if answer == QtWidgets.QMessageBox.Yes:
            try:
                self.logic.workbook.delete_sheet(sheet_label)
                self.tab_sorter.close_tab_sheet(sheet_label)
            except NonEmptyDataSheetError:
                show_critical_message_box('Cannot delete sheet with data. '\
                                          'It must be cleared first.')
            except MasterFormLockError as e:
                show_critical_message_box('Cannot delete sheet because '\
                                          'form master is being edited by '\
                                          '<b>%s</b>.' % ', '.join(e.args[0]))
            except LiveFormsPendingError as e:
                show_critical_message_box('Cannot delete sheet because '\
                                          'of pending live forms of '\
                                          '<b>%s</b>.' % ', '.join(e.args[0]))

    def login_preload_user(self, user):
        """ Return new password if reset has happened, or None if no reset """
        new_pwd = None
        if self.logic.password_reset_needed(user):
            logger.debug('Password reset needed for user %s', user)
            new_pwd = NewPasswordDialog.ask(user,
                                            self.logic.get_security_word(user),
                                            forbidden=[self.access_password])
            if new_pwd is not None:
                self.logic.set_user_password(user, new_pwd)
        #
        #         return new_pwd
        #     else:
        #         show_critical_message_box('Password reset not done')
        #         return False

        return new_pwd, self.logic.get_user_role(user)

    def on_add_sheets(self):
        fn_format = "Piccel sheet files (*.form *.py)"
        fns, _ = QtWidgets.QFileDialog.getOpenFileNames(self.workbook_screen,
                                                        'Open file',
                                                        '', fn_format)
        if fns is not None and len(fns) > 0:
            form_fns = {op.splitext(op.basename(fn))[0] : fn
                        for fn in fns if fn.endswith('.form')}
            plugin_fns = {op.splitext(op.basename(fn))[0] : fn
                          for fn in fns if fn.endswith('.py')}
            errors = []
            for sheet_label, form_fn in form_fns.items():
                form = Form.from_json_file(form_fn)

                plugin_str = None
                plugin_fn = plugin_fns.pop(sheet_label, None)
                if plugin_fn is not None:
                    with open(plugin_fn, 'r') as fin:
                        plugin_str = fin.read()
                sheet = DataSheet(sheet_label, form, plugin_code_str=plugin_str)
                error = self.add_sheet(sheet)
                if error is not None:
                    errors.append(error)

            # Add sheet with only plugin, no form
            for sheet_label, plugin_fn in plugin_fns.items():
                with open(plugin_fn, 'r') as fin:
                    plugin_str = fin.read()
                sheet = DataSheet(sheet_label, form_master=None,
                                  plugin_code_str=plugin_str)
                error = self.add_sheet(sheet)
                if error is not None:
                    errors.append(error)

            if len(errors) > 0:
                message = ('Error while adding sheet(s):\n%s' %
                           ('\n'.join([' - %s' % e for e in errors])))
                logger.error(message)
                show_critical_message_box(message)

    def add_sheet(self, sheet):
        error = None

        sheet_label = sheet.label
        isheet = 1
        while sheet_label in self.logic.workbook.sheets:
            logger.warning('Sheet %s already exists', sheet_label)
            sheet_label = '%s_%d' % (sheet.label, isheet)
            isheet += 1
        sheet.label = sheet_label

        try:
            self.logic.workbook.add_sheet(sheet)
            self.tab_sorter.show_tab_sheet(sheet,
                                           self.logic.workbook.user_role)
        except SheetDataOverwriteError:
            error = 'Sheet data folder already exists for %s' % sheet.label

        return error


    def on_add_sheet(self):
        existing_sheet_labels = list(self.logic.workbook.sheets.keys())

        new_sheet = (SheetCreationDialog
                     .new_sheet(existing_sheet_labels=existing_sheet_labels,
                                parent=self._workbook_ui.tabWidget))
        if new_sheet is not None:
            error = self.add_sheet(new_sheet)
            if error is not None:
                message = ('Error while adding sheet:\n%s\nError:\n%s' %
                           (sheet.label, error))
                logger.error(message)
                show_critical_message_box(message)

    def on_create(self):
        cfg_fn, self.access_pwd, self.default_user, self.role_pwd = \
            CreateWorkBookDialog.create()
        if cfg_fn is not None:
            self.selector_screen.hide()
            self.open_configuration_file(cfg_fn)
            if self.logic.workbook is not None:
                self.access_process()
                self.login_process()
            else:
                logger.error('Workbook not properly loaded')

    def open_file(self, fn):
        if fn is not None:
            if fn.endswith('.psh'):
                self.open_configuration_file(fn)
            elif fn.endswith('.form'):
                self.form_editor = FormFileEditor(fn)
                self.refresh()
            else:
                show_critical_message_box('Cannot open %s' % fn)

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
                msg = 'Cannot write to %s. This could be an ' \
                    'unauthorized access in the cloud storage ' \
                    'client (ex Dropbox).' % \
                    self.logic.workbook.filesystem.root_folder
                show_critical_message_box(msg)
            self.refresh()

    def show_screen(self, screen):
        def _show():
            screen.show()
            return screen
        return _show

    def access_cancel(self):
        self.logic.cancel_access()
        self.refresh()

    def access_process(self):
        logger.debug('Start access process')
        self.access_screen.statusBar().showMessage('Preparing workbook login...')
        self.access_screen.disable_inputs()
        self.processEvents()

        self.access_password = self.access_screen.access_password()

        error_message = None
        try:
            self.logic.decrypt(self.access_password)
        except InvalidPassword:
            error_message = 'Invalid access password'
        except Exception as e:
            error_message = 'Error: %s' % repr(e)

        if error_message is not None:
            message_box = QtWidgets.QErrorMessage()
            message_box.showMessage(error_message)
            message_box.exec_()

        logger.debug('End login process')
        self.refresh()

    def login_cancel(self):
        self.logic.cancel_login()
        self.refresh()

    def login_process(self, button_checked=False, user=None, pwd=None,
                      user_role=None):
        logger.debug('Start login process')
        self.login_screen.disable_inputs()

        self.login_screen.statusBar().showMessage("Loading workbook data...")
        self.processEvents() # TODO: make it less ugly? (using signals/QThread)

        def progress(msg):
            self.login_screen.statusBar().showMessage(msg)
            self.processEvents()

        entered_user, entered_pwd, entered_role = self.login_screen.login_info()
        user = if_none(user, entered_user)
        pwd = if_none(pwd, entered_pwd)
        user_role = if_none(user_role, entered_role)

        if pwd is None:
            error_message = 'Password required'
        else:
            error_message = None
            try:
                self.logic.login(user, pwd, user_role=user_role,
                                 progression_callback=progress)
                if self.refresh_rate_ms > 0:
                    self.timer = QtCore.QTimer(self)
                    logger.debug('Start data refresh timer with an interval '\
                                 'of %d ms', self.refresh_rate_ms)
                    self.timer.setInterval(self.refresh_rate_ms)
                    self.timer.timeout.connect(self.logic.workbook
                                               .refresh_all_data)
                    self.timer.start()
            except UnknownUser:
                error_message = 'Unknown user: %s' % user
            except InvalidPassword:
                error_message = 'Invalid user password'
            except PasswordReset:
                secure_word = self.logic.get_security_word(user)
                new_pwd = NewPasswordDialog.ask(user, secure_word,
                                                forbidden=[self.access_password])
                if new_pwd is not None:
                    self.logic.set_user_password(user, new_pwd)
                    self.login_process(user=user, pwd=new_pwd)
                else:
                    error_message = 'Password reset not done'

        if error_message is not None:
            message_box = QtWidgets.QErrorMessage()
            message_box.showMessage(error_message)
            message_box.exec_()

        if len(self.logic.workbook.jobs_invalidity) > 0:
            jobs_invalidity = self.logic.workbook.jobs_invalidity
            msg = ('Failed to load job(s): %s' %
                             ', '.join(jobs_invalidity))
            details = '\n'.join('## %s ##\n%s\n' % (jn,e)
                                for jn,e in jobs_invalidity.items())
            show_critical_message_box(msg, detailed_text=details)

        logger.debug('End login process')
        self.refresh()

    def show_access_screen(self):
        self.access_screen.set_wb_info(self.logic.workbook.label,
                                       self.logic.workbook.color_hex_str,
                                       self.access_pwd)
        self.access_screen.enable_inputs()
        self.access_screen.statusBar().clearMessage()
        self.access_screen.show()
        return self.access_screen
    #     self._access_ui.button_ok.setEnabled(True)
    #     self._access_ui.button_cancel.setEnabled(True)

    #     self._access_ui.workbook_label.setText(self.logic.workbook.label)
    #     self._access_ui.access_password_field.clear()
    #     if self.access_pwd is not None:
    #         self._access_ui.access_password_field.setText(self.access_pwd)
    #     self.access_screen.show()
    #     return self.access_screen

    def show_login_screen(self):
        # TODO: Add option to save debug log output in workbook
        logger.debug('Show login screen')
        user_names = self.logic.get_user_names()
        if self.default_user in user_names:
            user_names = [self.default_user] + \
                [u for u in user_names if u != self.default_user]

        self.login_screen.set_users(user_names)
        self.login_screen.set_workbook_info(self.logic.workbook.label,
                                            self.logic.workbook.color_hex_str)
        self.login_screen.reset_role_pwd(self.role_pwd)
        self.login_screen.enable_inputs()
        self.login_screen.statusBar().clearMessage()
        self.login_screen.show()

        return self.login_screen

    def make_text_editor(self, tab_widget, tab_label, text,
                         language, submit):
        text_editor_widget = QtWidgets.QWidget()
        _text_editor_ui = ui.text_editor_ui.Ui_Form()
        _text_editor_ui.setupUi(text_editor_widget)


    def close_workbook(self):
        self.logic.close_workbook()
        self.timer.stop()
        self.refresh()

    def show_workbook_screen(self):

        self.refresh_job_buttons()
        self.tab_sorter.clear()

        if len(self.logic.workbook.sheets) > 0:
            for isheet, (sheet_name, sheet) \
                in enumerate(self.logic.workbook.sheets.items()):
                access_level = if_none(sheet.access_level(), UserRole.ADMIN)
                if self.logic.workbook.user_role >= access_level:
                    logger.info('Load sheet %s in UI (access_level=%s, '
                                'user_role=%s)', sheet_name,
                                sheet.access_level(),
                                self.logic.workbook.user_role)
                    self.tab_sorter.show_tab_sheet(sheet,
                                                   self.logic.workbook.user_role)
                    for form_id, form in sheet.live_forms.items():
                        logger.info('Load pending form "%s" (%s)',
                                    form.tr['title'], form_id)
                        (self.tab_sorter
                         .add_tab_live_form(form, sheet.label,
                                            origin_sheet_label=sheet.label,
                                            user_role=self.logic.workbook.user_role))
                else:
                    logger.info('Sheet %s not loaded in UI because '\
                                'user role %s < %s',
                                sheet_name, self.logic.workbook.user_role,
                                sheet.access_level())
            self.tab_sorter.to_first()

        # def on_tab_idx_change(tab_idx):
        #     if tab_idx == tab_menu_idx:
        #         self._workbook_ui.tabWidget.setCurrentIndex(self.previous_tab_idx)

        # self._workbook_ui.tabWidget.currentChanged.connect(on_tab_idx_change)

        self.workbook_screen.setWindowTitle(self.logic.workbook.label)
        self.workbook_screen.show()

        return self.workbook_screen

    def show(self):
        self.refresh()
        # self.current_widget.show()
        # if self.form_editor is not None:
        #     self.form_editor.show()

    def refresh(self):
        self.current_widget.hide()
        logger.debug('Current logic state: %s',
                     PiccelLogic.STATES[self.logic.state])
        self.current_widget = self.screen_show[self.logic.state]()
        if self.form_editor is not None:
            self.form_editor.hide()
            self.form_editor.show()

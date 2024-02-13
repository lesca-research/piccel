from collections import defaultdict
from traceback import format_exc

import numpy as np
import pandas as pd

from .logging import logger

from PyQt5 import QtCore, QtGui, QtWidgets

class on_str(object):
    def __init__(self, func):
        self.func = func

    def __str__(self):
        return self.func()

def if_none(value, default_value):
    return value if value is not None else default_value

def if_none_or_empty(value, default_value):
    return value if (value is not None and len(value) > 0) else default_value

def nexts(l):
    """
    ASSUME: l has unique elements
    """
    it1 = iter(l)
    it2 = iter(l)
    next(it2)
    n = {e:ne for e,ne in zip(it1,it2)}
    for e in l:
        pass
    n[e] = None
    return n

class LazyFunc:
    def __init__(self, func, *args, **kwargs):
        self.func = func
        self.args = args
        self.kwargs = kwargs
    def __call__(self, **kwargs):
        return self.func(*self.args, **{**self.kwargs, **kwargs})

def df_index_from_value(df, value_dict):
    if len(value_dict) == 0:
        return []
    # iter_vd = iter(value_dict.items())
    # first_key, first_value = next(iter_vd)
    # m = df[first_key] == first_value
    # for key, value in iter_vd:
    #     m &= (df[key] == value)
    return df_filter_from_dict(df, value_dict).index.to_list()


def df_filter_from_dict(df, value_dict):

    if df.shape[0] == 0:
        return df

    single_vals = {}
    multi_vals = {}
    for k, v in value_dict.items():
        if isinstance(v, list):
            multi_vals[k] = v
        else:
            single_vals[k] = v

    if len(single_vals) > 0:
        df = df.loc[(df[list(single_vals)] == pd.Series(single_vals)).all(axis=1)]

    if len(multi_vals) > 0:
        multi_mask = pd.Series(np.ones(df.shape[0], dtype=bool),
                               index=df.index)
        for col, values in multi_vals.items():
            multi_mask &= df[col].isin(values)
        df = df[multi_mask]
    return df

def language_abbrev(language):
    # https://www.loc.gov/standards/iso639-2/php/code_list.php
    return {'French' : 'Fre',
            'English' : 'Eng'}[language]

class get_set_connect:
    def __init__(self, f_get, f_set):
        self.get = f_get
        self.set = f_set
    def __call__(self):
        self.set(self.get())

class text_connect:
    def __init__(self, text_get, text_set, ignore_empty=False):
        self.text_get = text_get
        self.text_set = text_set
        self.ignore_empty = ignore_empty
    def __call__(self):
        txt = self.text_get()
        if txt != '' or not self.ignore_empty:
            self.text_set(txt)

class refresh_text:
    def __init__(self, item, item_tr_label, ui_label,
                 hide_on_empty=False):
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

class Notifier:
    # TODO add recursion detection
    def __init__(self, notifications=None):
        self.on_events = defaultdict(list)
        if notifications is not None:
            self.add_callbacks(notifications)

    def add_callbacks(self, callbacks):
        """ callbacks : dict(event : callable]) """
        for event, callback in callbacks.items():
                self.add_callback(event, callback)

    def add_callback(self, event, callback):
        self.on_events[event].append(callback)

    def notify(self, event, *args, **kwargs):
        for on_event in self.on_events[event]:
            try:
                on_event(*args, **kwargs)
            except Exception as e:
                logger.error('Error during notification of event %s, ' \
                             'while calling %s', event, on_event)
                logger.error(format_exc())
                raise e

def strip_indent(code):
    indent_size = 0
    while code[indent_size] == ' ':
        indent_size += 1
    if indent_size == 0:
        return code
    return '\n'.join(line[indent_size:] for line in code.split('\n'))

from enum import IntEnum, Enum

class UserRole(IntEnum):
    VIEWER = 0
    EDITOR = 1
    REVIEWER = 2
    MANAGER = 3
    ADMIN = 4

InputType = Enum('InputType', 'TEXT PASSWORD FOLDER FILE_OUT FILE_IN')

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
    IGNORED = Hint(background_color_hex_str='#999999',
                   foreground_color_hex_str='#FFFFFF')
    COMPLETED = Hint(background_color_hex_str='#B6D7A8',
                     foreground_color_hex_str='#FFFFFF')

    ALL_HINTS = [WARNING, DONE, NOT_DONE, ERROR, QUESTION,
                 TEST, IGNORED, COMPLETED]

    @staticmethod
    def preload(qobj):
        for hint in Hints.ALL_HINTS:
            hint.preload(qobj)

class SheetNotFound(Exception): pass

class UnauthorizedRole(Exception): pass

class FormEditionBlockedByPendingLiveForm(Exception): pass
class FormEditionLocked(Exception): pass
class FormEditionNotOpen(Exception): pass
class FormEditionLockedType(Exception): pass
class FormEditionOrphanError(Exception): pass
class FormEditionCancelled(Exception): pass

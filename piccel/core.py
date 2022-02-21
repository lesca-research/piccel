from collections import defaultdict
from traceback import format_exc

import pandas as pd

from .logging import logger

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
    return df.loc[(df[list(value_dict)] == pd.Series(value_dict)).all(axis=1)]

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

    def __init__(self, watchers=None):
        self.watchers = defaultdict(list)
        if watchers is not None:
            self.add_watchers(watchers)

    def add_watchers(self, watchers):
        """ watchers : dict(event : [callables]) """
        for signal, watcher_list in watchers.items():
            for watcher in watcher_list:
                self.add_watcher(signal, watcher)

    def add_watcher(self, event, watcher):
        self.watchers[event].append(watcher)

    def notify(self, event, *args, **kwargs):
        for watcher in self.watchers[event]:
            try:
                watcher(*args, **kwargs)
            except Exception as e:
                logger.error('Error during notification of event %s, ' \
                             'while calling %s', event, watcher)
                logger.error(format_exc())
                raise e

def strip_indent(code):
    indent_size = 0
    while code[indent_size] == ' ':
        indent_size += 1
    if indent_size == 0:
        return code
    return '\n'.join(line[indent_size:] for line in code.split('\n'))

from enum import IntEnum

class UserRole(IntEnum):
    VIEWER = 0
    EDITOR = 1
    MANAGER = 2
    ADMIN = 3

class SheetNotFound(Exception): pass

class FormEditionBlockedByPendingLiveForm(Exception): pass
class FormEditionLocked(Exception): pass
class FormEditionNotOpen(Exception): pass
class FormEditionLockedType(Exception): pass
class FormEditionOrphanError(Exception): pass
class FormEditionCancelled(Exception): pass

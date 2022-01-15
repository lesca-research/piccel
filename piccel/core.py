from collections import defaultdict

import pandas as pd

from .logging import logger

def if_none(value, default_value):
    return value if value is not None else default_value

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
                raise e

from enum import IntEnum

class UserRole(IntEnum):
    ADMIN = 3
    MANAGER = 2
    EDITOR = 1
    VIEWER = 0

class SheetNotFound(Exception): pass

class FormEditionBlockedByPendingLiveForm(Exception): pass
class FormEditionLocked(Exception): pass
class FormEditionNotOpen(Exception): pass
class FormEditionLockedType(Exception): pass
class FormEditionOrphanError(Exception): pass
class FormEditionNotAvailable(Exception): pass

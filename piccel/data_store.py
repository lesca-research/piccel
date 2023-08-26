# -*- coding: utf-8 -*-

from itertools import product
from datetime import datetime, date, timezone
from copy import deepcopy
from pathlib import PurePath

import numpy as np
import pandas as pd
from pandas.testing import assert_frame_equal, assert_series_equal

from .core import if_none, Notifier
import logging
from .logging import logger, debug2, debug3

import tempfile
from pyfakefs.fake_filesystem_unittest import TestCase
#from unittest import TestCase
from .io.filesystem import LocalFileSystem

DATE_FORMAT = '%Y-%m-%d'
QDATE_FORMAT = 'yyyy-MM-dd'
DATETIME_FORMAT = '%Y-%m-%d %H:%M:%S.%f'

def unformat_boolean(s):
    if s == 'True':
        return True
    elif s == 'False' or s == '':
        return False
    else:
        raise ValueError('Boolean string must be "True", "False", '\
                         'empty (%s given)' % s)

FLAGS_SYMBOLS = {
    'cross_red',
    'square_blue',
    'triangle_orange',
    'circle_green',
    'tick_mark_green',
    'question_mark',
    'exclamation_point',
    'phone',
    'clock',
    'trash',
    'arobase',
    'idea',
    'calendar',
    'cycle',
    'unlocked',
    'locked'
}

VTYPES = {
    'string' : {
        'dtype_pd' : 'string',
        'check_dtype_pd' : lambda dt: dt == 'string',
        'unformat' : lambda s : s,
        'format' : lambda v : v,
        'validate_dtype_pd' : lambda v : isinstance(v, str),
        'null_value' : '',
        'na_value' : pd.NA,
        'corner_cases' : {'':'', 'a´*€$éà ':'a´*€$éà ', '12':'12',
                          'False':'False', '2020-01-02':'2020-01-02'},
        'bad_format_cases' : [],
    },
    'int' : {
        'dtype_pd' : 'Int64',
        'unformat' : lambda s : np.int64(s),
        'format' : lambda i : '%d' % i,
        'validate_dtype_pd' : pd.api.types.is_int64_dtype,
        'null_value' : np.int64(0),
        'na_value' : pd.NA,
        'corner_cases' : {'0':np.int64(0), '-1':np.int64(-1),
                          '12345':np.int64(12345)},
        'bad_format_cases' : ['1.1', '', 'text', '1+2'],
    },
    'boolean' : {
        'dtype_pd' : 'boolean',
        'unformat' : unformat_boolean,
        'format' : lambda b : str(b),
        'validate_dtype_pd' : lambda v : isinstance(v, bool),
        'null_value' : False,
        'na_value' : pd.NA,
        'corner_cases' : {'False':False, 'True':True, '':False},
        'bad_format_cases' : ['false', 'true', '0', '1', 'text'],
    },
    'number' : {
        'dtype_pd' : 'float',
        'unformat' : lambda s : float(s),
        'format' : lambda n : '%f' % n,
        'validate_dtype_pd' : pd.api.types.is_float_dtype,
        'null_value' : 0.0,
        'na_value' : np.nan,
        'corner_cases' : {'0':0, '0.0':0, '-1.4':-1.4, '3.141592653589793':np.pi},
        'bad_format_cases' : ['False', 'true', 'text', 'np.pi'],
    },
    'date' : {
        'dtype_pd' : 'datetime64[ns]',
        'unformat' : lambda s : date.fromisoformat(s),
        'format' : lambda d : d.isoformat(),
        'validate_dtype_pd' : pd.api.types.is_datetime64_dtype,
        'null_value' : datetime.now().date(),
        'na_value' : pd.NaT,
        'corner_cases' : {'2020-01-02' : date(2020, 1, 2)},
        'bad_format_cases' : ['01-02-2020', 'true', 'text', 'np.pi'],
    },
    'datetime' : {
        'dtype_pd' : 'datetime64[ns]',
        'unformat' : lambda s : datetime.fromisoformat(s),
        'format' : lambda d : d.isoformat(),
        'validate_dtype_pd' : pd.api.types.is_datetime64_dtype,
        'null_value' : datetime.now().astimezone(),
        'na_value' : pd.NaT,
        'corner_cases' : {'2011-11-04 00:05:23.283+00:00':
                          datetime(2011, 11, 4, 0, 5, 23, 283000,
                                   tzinfo=timezone.utc)},
        'bad_format_cases' : ['01-02-2020', '2011-11-04 00h05',
                              'true', 'text', 'np.pi'],
    }
}

VTYPES['variable_type'] = deepcopy(VTYPES['string'])
VTYPES['variable_type']['validate_value'] = lambda v: v in VTYPES

VTYPES['symbol'] = deepcopy(VTYPES['string'])
VTYPES['symbol']['validate_value'] = lambda v: v in FLAGS_SYMBOLS

VTYPES['flag_index'] = deepcopy(VTYPES['int'])
VTYPES['flag_index']['validate_value'] = lambda v: (v >= 0) and (v < 64)


VTYPES['ds_code_entry'] = deepcopy(VTYPES['string'])
# TODO: add validation & conversion to compiled code object

ALLOWED_VARIABLE_TYPE_CHANGE = {
    ('int', 'number'),
    ('boolean', 'int'),
    ('date', 'datetime')
}

class InvalidDataStoreLabel(Exception): pass
class DuplicateValueError(Exception): pass
class InvalidValueError(Exception): pass
class BadVariableType(Exception): pass
class InvalidFlagFormat(Exception): pass
class DuplicateFlag(Exception): pass
class DuplicateChoice(Exception): pass
class UnsetFlagError(Exception): pass
class InvalidFlagIndex(Exception): pass
class LockedVariables(Exception): pass
class InvalidIndex(Exception): pass
class VariableChangeError(Exception): pass

class Var:
    def __init__(self, var_label, var_type, index_position=None, is_unique=False,
                 is_used=True, nullable=True, column_position=None):

        self.var_label = var_label

        if var_type not in VTYPES:
            raise BadVariableType(var_type)
        self.var_type = var_type

        self.index_position = index_position

        self.is_unique = is_unique
        self.is_used = is_used
        self.nullable = nullable

        self.column_position = column_position

    def asdict(self):
        return {
            'var_label' : self.var_label,
            'var_type' : self.var_type,
            'index_position' : self.index_position,
            'column_position' : self.column_position,
            'is_unique' : self.is_unique,
            'nullable' : self.nullable,
            'is_used' : self.is_used,
        }

class FixedVariables:
    def __init__(self, variables):
        self.variables = {v.var_label:v for v in variables}

    def __iter__(self):
        return (v.asdict() for v in self.variables.values())

    def validate_dtypes(self):
        return False # stub

class PersistentVariables:
    META_VARS = [
        Var('var_label', 'string', index_position=0),
        Var('var_type', 'variable_type'),
        Var('nullable', 'boolean'),
        Var('index_position', 'int'),
        Var('is_unique', 'boolean'),
        Var('is_used', 'boolean'),
        Var('column_position', 'int'),
    ]
    def __init__(self, parent_store):
        self.store = DataStore(parent_store.filesystem,
                               label=parent_store.label + '_vars', 
                               variables=PersistentVariables.META_VARS,
                               use_annotations=False,
                               validate_entry=parent_store.validate_var_entry,
                               watchers={'pushed_entry' :
                                         parent_store.on_pushed_variable})

    def __iter__(self):
        return (Var(idx, **row) for idx, row in self.store.head_df().iterrows())

def df_like(df, fill_value=pd.NA, dtype=None):
    new_df = pd.DataFrame().reindex_like(df).fillna(fill_value)
    if dtype is not None:
        new_df = new_df.astype(dtype)

class PersistentLogic:
    STORE_VARS = [
        Var('code_entry', 'ds_code_entry', index_position=0),
        Var('code', 'string')
    ]

    def __init__(self, parent_store):

        # TODO pass code validation function
        self.store = DataStore(parent_store.filesystem,
                               label=parent_store.label + '_code', 
                               variables=PersistentLogic.STORE_VARS,
                               use_annotations=False,
                               watchers={'pushed_entry' :
                                         self.on_pushed_entry})

    def on_pushed_entry(self, new_entry):
        for idx, row in new_entry.iterrows():
            if row['code_entry'] == '':
                pass

class TestVariable(TestCase):

    def test_fixed_variables(self):
        v1 = Var('v1', 'string')
        v2 = Var('v2_idx', 'int', index_position=0)
        v3 = Var('v3', 'boolean')
        vs = FixedVariables([v1, v2, v3])
        self.assertSequenceEqual(list(vs),
                                 [v1.asdict(), v2.asdict(), v3.asdict()])

    def test_fixed_variables_duplicate(self):
        self.assertRaises(DuplicateValueError, FixedVariables,
                          [Var('v1', 'string'),
                           Var('v2', 'int'),
                           Var('v2', 'string')])

    def test_persistent_variables_persistence(self):
        raise NotImplementedError()

def null_df_if_none(df, df_orig, fill=lambda df: df):
    if df is None:
        return fill(pd.DataFrame().reindex_like(df_orig))
    else:
        return df

def false_df_if_none(df, df_orig):
    null_df_if_none(df, df_orig, lambda df: df.fillna(False).astype(bool))

def bitmask(positions):
    n = 0
    for position in positions:
        n |= (1<<position)
    return n

import math
def bitunmask(bits):
    if bits == 0:
        return []
    max_pos = int(math.log(bits, 2)) + 1
    return [n for n in range(max_pos) if bits & (1 << n)]

class TestBitMasking(TestCase):

    def test(self):
        for pos in ( [],
                     [0],
                     [1],
                     [2, 7, 10, 14, 16],
                     [0, 1, 2, 4, 120] ):
            mask = bitmask(pos)
            self.assertEqual(bitunmask(mask), pos)


class TestHash(TestCase):

    def test_hash_stable(self):
        mi = pd.MultiIndex.from_tuples([('CE1', 'psy'), ('CE3', 'npk')],
                                       names=['pid', 'interview'])
        hashes = pd.util.hash_pandas_object(mi)
        assert_series_equal(hashes, pd.Series([5595273432021433277,
                                               6997378824351957369],
                                              dtype='uint64'))
        
class DataStoreLogger(logging.LoggerAdapter):
    def process(self, msg, kwargs):
        return '[%s] %s' % (self.extra['store_label'], msg), kwargs

class DataStore:

    # nofitications:
    # 'pushed_entry', 'deleted_entry', 'variables_changed', 'flags_changed'
    # 'pushed_annotation'

    TRACKING_INDEX_LEVELS = ['__entry_id__',
                             '__update_idx__',
                             '__conflict_idx__']
    PRIVATE_COLS = TRACKING_INDEX_LEVELS + ['__fn__']

    FLAG_DEF_VARS = [
        Var('flag_index', 'flag_index', index_position=0, nullable=False),
        Var('flag_label', 'string', is_unique=True),
        Var('flag_symbol', 'symbol'),
    ]

    FLAG_VARIABLES = [
        Var('index_hash', 'int', index_position=0),
        Var('index_repr', 'string'),
        Var('variable', 'string'),
        Var('flag', 'int'),
    ]

    NOTES_VARIABLES = [
        Var('index_hash', 'int', index_position=0),
        Var('timestamp', 'datetime', index_position=1),
        Var('index_repr', 'string'),
        Var('variable', 'string'),
        Var('note', 'int'),
        Var('archived', 'boolean'),
    ]

    DATA_FILE_EXT = '.csv'

    def __init__(self, filesystem, label=None, variables=None,
                 use_annotations=True, logic=None, watchers=None):
        """
        For variables and logic, use persistent versions with history if they
        are None.
        """

        expected_label = DataStore.label_from_filesystem(filesystem)
        if label is None:
            # ASSUME filesystem points to store directory
            if not DataStore.is_valid_datastore_label(expected_label):
                raise InvalidDataStoreLabel(expected_label)
            self.label = expected_label
            self.filesystem = filesystem.clone()
        elif label != expected_label:
            # label is given but not consistent with filesystem
            # -> move to subdirectory
            if not DataStore.is_valid_datastore_label(label):
                raise InvalidDataStoreLabel(label)
            if not filesystem.exists(label):
                filesystem.makedirs(label)
            self.filesystem = filesystem.change_dir(label)
            self.label = label
        else:
            # label is given and consistent with filesystem
            if not DataStore.is_valid_datastore_label(label):
                raise InvalidDataStoreLabel(label)
            self.filesystem = filesystem.clone()
            self.label = label

        self.log = DataStoreLogger(logger, {'store_label' : label})

        self.notifier = Notifier(watchers if watchers is not None else {})

        self.df = pd.DataFrame(columns=DataStore.PRIVATE_COLS)
        for col in DataStore.TRACKING_INDEX_LEVELS:
            self.df[col] = self.df[col].astype(np.int64)
        self.df['__fn__'] = self.df['__fn__'].astype('string')
        self.df = self.df.set_index(DataStore.TRACKING_INDEX_LEVELS)

        if variables is not None:
            self.variables = FixedVariables(variables)
        else:
            self.variables = PersistentVariables(self)

        self.flag_ds = None
        self.note_ds = None
        if use_annotations:
            self.flag_defs_ds = DataStore(self.filesystem,
                                          label=self.label + '_flag_defs',
                                          variables=DataStore.FLAG_DEFS_VARS,
                                          use_annotations=False,
                                          watchers={'pushed_entry':
                                                    self.on_pushed_flag_def})

            self.flag_ds = DataStore(self.filesystem,
                                     label=self.label + '_flags',
                                     variables=DataStore.FLAGS_VARIABLES,
                                     use_annotations=False,
                                     watchers={'pushed_entry':
                                               self.on_pushed_flag_def})

            self.note_ds = DataStore(self.filesystem,
                                     label=self.label + '_notes',
                                     variables=DataStore.NOTES_VARIABLES,
                                     use_annotations=False,
                                     watchers={'pushed_entry':
                                               self.on_pushed_note})

        if logic is not None:
            self.logic = logic # expect DataStoreLogic
        else:
            self.logic = PersistentLogic(self)

        self.user = None

        self.filesystem.makedirs('data')
        self.filesystem.enable_track_changes()

        self._refresh_data()

    def _refresh_data(self):
        modified_files, new_files, deleted_files = \
            self.filesystem.external_changes()
        self.logger.debug2('Files externally added: %s', new_files)
        self.logger.debug2('Files externally modified: %s', modified_files)
        self.logger.debug2('Files externally deleted: %s', deleted_files)

        def _is_data_file(fn):
            return (fn.startswith('data') and
                    fn.endswith(DataStore.DATA_FILE_EXT))

        new_data_files = [fn for fn in new_files if _is_data_file(fn)]
        modified_data_files = [fn for fn in modified_files if _is_data_file(fn)]
        deleted_data_files = [fn for fn in deleted_files if _is_data_file(fn)]

        def _load_entry(data_fn):
            df_content = self.filesystem.load(data_fn)
            entry_df = self.df_from_str(df_content)
            entry_df['__fn__'] = data_fn
            self.merge(entry_df) # will notify added_entries

        for del_fn in deleted_data_files:
            to_delete = self.df.index[self.df['__fn__'] == del_fn]
            self.df = self.df.drop(index=to_delete)
            self.notifier.notify('deleted_entries', to_delete)

        for mod_fn in modified_data_files:
            to_reload = self.df.index[self.df['__fn__'] == mod_fn]
            self.df = self.df.drop(index=to_reload)
            self.notifier.notify('deleted_entries', to_reload)
            _load_entry(mod_fn)

        for new_fn in new_data_files:
            _load_entry(new_fn)

        self.filesystem.accept_all_changes('data')

    def merge(self, other_df):
        if other_df.index.names != DataStore.TRACKING_INDEX_LEVELS:
            raise Exception()

    def push_record(self, record, comment=None, timestamp=None):
        value_df = pd.DataFrame.from_records([record])
        if comment is None:
            comment_df = df_like(value_df, fill_value=pd.NA, dtype='string')
        else:
            comment_df = pd.DataFrame.from_records([comment])

        timestamp_df = df_like(value_df,
                               fill_value=if_none(timestamp,
                                                  datetime.now().astimezone()),
                               dtype='datetime64[ns]')

        user_df = df_like(value_df, fill_value=if_none(self.user, pd.NA),
                          dtype='string')

        self.push_df(value_df, comment_df, timestamp=timestamp)

        # put in push_df:

    def push_df(self, value_df, comment_df, user_df, timestamp_df):
        dfs = {'value_df' : value_df,
               'comment_df' : comment_df,
               'user_df' : user_df,
               'timestamp_df' : timestamp_df}
        if not set(DataStore.TRACKING_INDEX_LEVELS).issubset(value_df.columns):
            index_variables = self.variables.index_variables()
            if len(index_variables) > 0:
                index_to_update = ...
                index_new = ...
            else:
                index_new = pd.MultiIndex.from_tuples(
                    [(self.new_entry_id(), 0, 0) for _ in value_df.index],
                    names=DataStore.TRACKING_INDEX_LEVELS)
            
            # apply index change to comment, user, ts
        else:
            for k, df in dfs.items():
                dfs[k] = df.set_index(DataStore.TRACKING_INDEX_LEVELS)

        idx = self.merge_df(dfs)
        data_fn = self.save_entry(dfs)
        self.df.loc[idx, '__fn__'] = data_fn

    def reload_all_data(self):
        """ Data is cleared before loading """
        self.logger.debug('Reload all data')
        data_folder = 'data'

        data_bfns = [fn for fn in self.filesystem.listdir(data_folder) \
                     if fn.endswith(DataStore.DATA_FILE_EXT)]

        if logger.level >= logging.DEBUG:
            self.logger.debug('Available data files:\n%s',
                              self.label, '\n'.join(data_bfns))
        if len(data_bfns) > 0:
            if self.df.shape[0] > 0:
                self.delete_all_entries()
            # Associated views will be cleared
            # Expect watchers to react
            for data_bfn in data_bfns:
                data_fn = op.join(data_folder, data_bfn)
                self.logger.debug('Load data in %s', data_fn)
                df_content = self.filesystem.load(data_fn)
                entry_df = self.df_from_str(df_content)
                if not data_fn.endswith('main.csv'):
                    entry_df['__fn__'] = data_fn
                self._merge_df(entry_df) # previously _append_df
            self.fix_conflicting_entries()
            self.invalidate_cached_views()
        else:
            logger.debug('No sheet data to load in %s', data_folder)
        self.filesystem.accept_all_changes(data_folder)

    def delete_all_entries(self):
        self.notifier.notify('pre_clear_data')
        self.df = self.df.drop(self.df.index)
        self.notifier.notify('cleared_data')

    def refresh(self):
        self.variables.refresh()
        self.logic.refresh()
        if self.flag_ds is not None:
            self.flag_ds.refresh()
        if self.note_ds is not None:
            self.note_ds.refresh()
        self._refresh_data()

    def on_pushed_variable(self, changes):
        # ASSUME validation has been done before push
        for var_old, var_new in changes:
            if var_old is not None:
                label_old = var_old['var_label']
                if var_new is not None: # modified variable
                    label_new = var_new['var_label']

                    if label_old != label_new:
                        self.df = self.df.rename({label_old : label_new})
                        self.notifier.notify('column_renamed', label_old,
                                             label_new)

                    if var_old['var_type'] != var_new['var_type']:
                        dtype_new = VTYPES[var_new['var_new']]['dtype_pd']
                        self.df[label_new] = (self.df[label_new]
                                              .astype(dtype_new))
                        self.notifier.notify('column_values_changed', label_new)

                    if var_old['nullable'] and not var_new['nullable']:
                        nans = pd.isna(self.df[label_new])
                        if nans.any():
                            na_fill = VTYPES[var_new['var_new']]['null_value']
                            self.log.warning(('%s becomes nullable but has '
                                              '%d NA values. They will be filled '
                                              'with %s'), label_new, na_fill)
                            self.df[label_new] = (self.df[label_new]
                                                  .fillna(na_fill))
                            self.notifier.notify('values_changed',
                                                 self.df[[label_new]][nans])

                    if var_old['index_position'] != var_new['index_position']:
                        if pd.isna(var_new['index_position']):
                            self.notifier.notify('head_index_removed',
                                                 label_new)
                        else:
                            self.notifier.notify('head_index_added', label_new)

                    if var_old['is_used'] != var_new['is_used']:
                        if var_new['is_used']:
                            self.notifier.notify('head_column_removed',
                                                 label_new)
                        else:
                            self.notifier.notify('head_column_added',
                                                 label_new)

                    if var_old['column_position'] != var_new['column_position']:
                        self.notifier.notify('head_column_position_changed',
                                             label_new,
                                             var_old['column_position'],
                                             var_new['column_position'])
                else: # deleted variable
                    self.df = self.df.drop(column=[var_old['var_label']])
                    self.notifier.notify('column_removed', var_old['var_label'])
            else: # new variable
                vlabel = var_new['var_label'] 
                tdef = VTYPES[var_new['var_type']]
                if var_new['nullable']:
                    fill_value = pd.na
                else:
                    fill_value = tdef['null_value']
                self.df[vlabel] = fill_value
                self.df[vlabel] = self.df[vlabel].astype(tdef['dtype_pd'])
                self.notifier.notify('column_added', vlabel)

            self.invalidate_cached_views()

    def invalidate_cached_views(self):
        raise NotImplementedError()

    def on_pushed_flag_def(self, flag_entry):
        # TODO actually check if change is worth notifying
        # if associated with tracking index, then full view UI should
        # update accordingly 
        # else (associated with head index), then head view UI should update
        self.notifier.notify('flag_definition_changed', flag_entry)

    def on_pushed_note(self, note_entry):
        # TODO actually check if change is worth notifying
        self.notifier.notify('pushed_note', note_entry)

    @classmethod
    def label_from_filesystem(self, fs):
        return PurePath(fs.root_folder).parts[-1]

    def validate_var_entry(self, new_entry):

        current_vars_df = self.variables.store.head_df()
        # Check only modified variables
        new_entry = new_entry.set_index('var_label')
        modified_vars = new_entry.index.intersection(current_vars_df)
        new_entry = new_entry.loc[modified_vars]
        previous = current_vars_df.loc[modified_vars]

        def index_vars(var_df):
            m_index = ~pd.isna(var_df['index_position'])
            return var_df.index[m_index].sort()

        if self.variables_are_locked():
            # allow only change in index or column order
            pos_cols = ['index_position', 'column_position']            
            if ( (index_vars(previous) != index_vars(new_entry)).any() or
                 (previous.drop(columns=pos_cols) !=
                  new_entry.drop(columns=pos_cols)).any(axis=None) ):
                raise LockedVariables()
            else:
                if (previous[[pos_cols]] !=
                    new_entry[[pos_cols]]).any(axis=None):
                    self.invalidate_cached_views()
                # else no change in new entry, nothing to do
        else:
            if self.df.empty: # no data yet, allow any change
                return true_df_like(new_entry)
            else:
                full_df = self.full_df()
                for var_label, mod_var in new_entry.iterrows():
                    current_var = current_vars_df.loc[var_label]
                    # check type change
                    if ( (current_var['var_type'], mod_var['var_type']) not in
                         ALLOWED_VARIABLE_TYPE_CHANGE ):
                        raise VariableChangeError(var_label)
                    # check uniqueness / index
                    if ( (not current_var['is_unique'] and
                          mod_var['is_unique']) or
                         (pd.isna(current_var['index_position']) and
                          not pd.isna(mod_var['index_position'])) ):
                        raise VariableChangeError(var_label)
                    # check nullable
                    if ((current_var['nullable'] and
                        not  mod_var['nullable']) and
                        pd.isna(full_df[var_label]).any()):
                        raise VariableChangeError(var_label)
        
    @classmethod
    def is_valid_variable_label(cls, label):
        return (label.isidentifier() and
                not (label.startswith('__') and label.endswith('__')))

    @classmethod
    def is_valid_datastore_label(cls, label):
        return (label.isidentifier() and
                not (label.startswith('__') and label.endswith('__')))

    @classmethod
    def is_valid_flag_label(cls, label):
        return label.isidentifier()

    def set_user(self, user):
        self.user = user

    def push_records(self, records):
        return [(0, 0, 0)] # stub

    def push_record(self, record, tracking_index=None):
        return (0, 0, 0) # stub

    def push_variable(self, var_label, var_type, nullable=True,
                      index_position=None, is_unique=False, is_used=True,
                      column_position=None):
        return self.variables.store.push_record({}) # stub

    def invalid_entries(self):
        return []

    def validate_dtypes(self):
        logger.debug('Validate dtypes of %s', self.label)

        is_valid = True

        # Validate index in full df
        validate_int = VTYPES['int']['validate_dtype_pd']
        for index_level in DataStore.TRACKING_INDEX_LEVELS:
            dtype = self.df.index.dtypes[index_level]
            validity = validate_int(dtype)
            if not validity:
                logger.error('Index level %s has invalid dtype: %s',
                             index_level, dtype)
            is_valid &= validity

        dtype = self.df['__fn__'].dtype
        validity = VTYPES['string']['validate_dtype_pd'](dtype)
        if not validity:
            logger.error('Column __fn__ has invalid dtype: %s', dtype)
        is_valid &= validity

        # Validate columns in full & head df
        for df in (self.head_df(), self.df):
            for variable in self.variables:
                type_def = VTYPES[variable.vtype]
                dtype = df[variable.var_label].dtype
                validity = type_def['validate_dtype_pd'](dtype)
                if not validity:
                    logger.error('Column of %s (%s) has invalid dtype: %s',
                                 variable, variable.vtype, dtype)
                is_valid &= validity

        is_valid &= self.variables.validate_dtypes()

        if self.flag_ds is not None:
            is_valid &= self.flag_ds.validate_dtypes()

        if self.annotation_ds is not None:
            is_valid &= self.annotation_ds.validate_dtypes()

        return is_valid

    def push(self, value_df, comment_df=None, flags_df=None):
        self._push(value_df,
                   null_df_if_none(comment_df, value_df),
                   null_df_if_none(flags_df, value_df))

    def _push(self, value_df, comment_df, flags_dfs):
        """
        ASSUME: all dfs have same index & columns
        ASSUME: flags_dfs has all flags
        """
        # TODO: make df with user + timestamp
        # Arrange tracking index
        pass

    def full_df(self, view):
        return pd.DataFrame() # stub

    def head_df(self, view):
        return pd.DataFrame() # stub

class TestDataStore(TestCase):

    def setUp(self):
        self.setUpPyfakefs()
        self.tmp_dir = tempfile.mkdtemp()
        self.filesystem = LocalFileSystem(self.tmp_dir)        
        
    def test_valid_variable_label(self):
        self.assertFalse(DataStore.is_valid_variable_label('__test__'))
        self.assertTrue(DataStore.is_valid_variable_label('__test_'))

        self.assertFalse(DataStore.is_valid_variable_label('1var'))
        self.assertFalse(DataStore.is_valid_variable_label('A variable'))
        self.assertTrue(DataStore.is_valid_variable_label('var_1'))

    def test_valid_flag_label(self):
        self.assertFalse(DataStore.is_valid_flag_label('1flag'))
        self.assertFalse(DataStore.is_valid_flag_label('A flag'))
        self.assertTrue(DataStore.is_valid_flag_label('flag_1'))

    # TEST BASIC DATA INPUT FOR DTYPE CONSISTENCY, UNIQUENESS, UNUSED
    def _check_store(self, ds, nullables, uniques, indexes, unused):
        self.assertTrue(ds.validate_dtypes())

        self.assertTrue(ds.full_df('validity').all(axis=None))
        self.assertTrue(ds.head_df('validity').all(axis=None))
        
        full_df = ds.full_df()
        head_df = ds.head_df()

        for tl in uniques:
            self.assertTrue(head_df[tl].is_unique(), tl)

        self.assertTrue(head_df.index.is_unique())
        if len(indexes) > 0:
            self.assertEqual(head_df.index.names, indexes)

        not_unused_head = (set(unused)
                           .intersection(head_df.reset_index().columns))

        self.assertEqual(len(not_unused_head), 0, ', '.join(not_unused_head))

        self.assertTrue(set(unused).issubset(full_df.columns))

        _check_store(DataStore.from_files(ds.filesystem))

    def _test_push_data(self, nullables=None, uniques=None, indexes=None,
                        unused=None):
        nullables = if_none(nullables, [])
        uniques = if_none(uniques, [])
        indexes = if_none(indexes, [])
        unused = if_none(unused, [])

        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        for t, tdef in VTYPES.items():
            ds.push_variable(t, t, nullable=t in nullables,
                             index_position=(indexes.find(t)
                                             if t in indexes else None),
                             is_unique=t in uniques,
                             is_used=t not in unused)

        combinations = [[(tl, v)
                         for v in (td["corner_values"] +
                                   ([None] if tl in nullables
                                    else []))]
                        for tl, td in VTYPES.items()]
        entries = list(product(*combinations))
        # import pdb; pdb.set_trace()
        ds.push_records([dict(e) for e in entries])

        self._check_store(ds, nullables, uniques, indexes, unused)

        for tlabel in uniques:
            tdef = VTYPES[tlabel]
            self.assertRaises(DuplicateValueError,
                              ds.push_record,
                              {tlabel:tdef['corner_values'][0]})

        # Check store reloading
        ds2 = DataStore(self.filesystem)
        self._check_store(ds2, nullables, uniques, indexes, unused)
        assert_frame_equal(ds.full_df(), ds2.full_df())

    def test_data_entry(self):
        self._test_push_data()

    def test_datafile_multi_entry_deletion(self):
        # TODO do not check actual files, only check refresh & reload
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(self.filesystem)
        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx = ds1.push_records({'v1' : ['test', 'other test']})

        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()
        assert_frame_equal(full_df1, full_df2)

        ds1.delete_single_entry(tidx[0])
        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()

        self.assertTrue(tidx[0] not in full_df1.index)
        assert_frame_equal(full_df1, full_df2)
        
    def test_datafile_single_entry_deletion(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(self.filesystem)

        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx1 = ds1.push_record({'v1' : 'test'})
        tidx2 = ds1.push_record({'v1' : 'other test'})

        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()

        fn1 = full_df1.loc[tidx1, '__fn__']
        self.assertTrue(self.filesystem.exists(fn1))
        assert_frame_equal(full_df1, full_df2)

        ds1.delete_single_entry(tidx1)
        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()

        self.assertFalse(tixd1 in full_df1.index)
        self.assertFalse(self.filesystem.exists(fn1))
        assert_frame_equal(full_df1, full_df2)

    def test_main_datafile_modification(self):

        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(self.filesystem)

        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx1 = ds1.push_records({'v1' : 'test'})
        tidx2 = ds1.push_record({'v1' : 'other test'})
        ds2.refresh()

        full_df1 = ds1.full_df()
        fn1 = full_df1.loc[tidx1, '__fn__']
        fn2 = full_df1.loc[tidx2, '__fn__']

        ds1.pack_data_files()
        self.assertFalse(self.filesystem.exists(fn1))
        self.assertFalse(self.filesystem.exists(fn2))

        full_df1 = ds1.full_df()
        main_fn = op.join('test_ds', 'data', 'data_main.csv')
        self.assertEqual(full_df1.loc[tidx1, '__fn__'], main_fn)
        self.assertEqual(full_df1.loc[tidx2, '__fn__'], main_fn)

        ds2.refresh()
        full_df2 = ds2.full_df()
        self.assertEqual(full_df2.loc[tidx1, '__fn__'], main_fn)
        self.assertEqual(full_df2.loc[tidx2, '__fn__'], main_fn)

        ds1.delete_single_entry(tidx1) # data_main.csv will be modified
        self.assertFalse(tixd1 in ds1.full_df().index)
        self.assertTrue(self.filesystem.exists(main_fn))

        tidx3 = ds1.push_record({'v1' : 'another test'})
        ds1.pack_data_files()

        ds2.refresh()
        full_df2 = ds2.full_df()
        self.assertFalse(tixd1 in full_df2.index)
        self.assertTrue(tixd3 in full_df2.index)

        self.assertEqual(full_df2.loc[tidx2, '__fn__'], main_fn)
        self.assertEqual(full_df2.loc[tidx3, '__fn__'], main_fn)

    def test_data_entry_nullable(self):
        self._test_push_data(nullables=VTYPES.keys())

    def test_data_entry_unique(self):
        self._test_push_data(uniques=VTYPES.keys())

    def test_data_entry_index(self):
        for type_label in VTYPES:
            self._test_push_data(indexes=[type_label])

        vtypes = list(VTYPES.keys())
        self._test_push_data(indexes=vtypes[:2])

    def test_data_entry_unused(self):
        for type_label in VTYPES:
            self._test_push_data(unused=[type_label])

    def test_data_push_non_indexed_entry(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_records({'v1' : 'test'})
        tidx = ds.push_record({'v1' : 'other test'})

        assert_frame_equal(ds.head_df().reset_index(drop=True),
                           pd.DataFrame({'v1' : ['test', 'other test']}))

        ds.push_record({'v1' : 'other test update'}, tracking_index=tidx)
        assert_frame_equal(ds.head_df().reset_index(drop=True),
                           pd.DataFrame({'v1' : ['test', 'other test update']}))

    def test_data_push_indexed_entry(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('my_index', 'int', index_position=0)
        ds.push_record({'v1' : 'test',
                        'my_index' : 10})

        ds.push_record({'v1' : 'other',
                        'my_index' : 34})

        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'v1' : ['test', 'other'],
                                          'my_index' : [10, 34]})
                            .set_index('my_index')))

        ds.push_record({'v1' : 'updated',
                        'my_index' : 10})

        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'v1' : ['test', 'updated'],
                                         'entry_id' : [10, 34]})
                            .set_index('my_index')))

    def test_multi_index(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        # TODO check uniqueness of index_position
        ds.push_variable('interview', 'string', index_position=1)
        ds.push_variable('pid', 'string', index_position=0)
        ds.push_variable('age', 'int')

        ds.push_record({'pid' : 'CE01',
                        'interview' : 'preliminary',
                        'age' : 54})
        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'pid' : ['CE01'],
                                          'interview' : ['preliminary'],
                                          'age' : [54]})
                            .set_index(['pid', 'interview'])))

    def test_fordidden_variable_type_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('v1', 'int')
        ds.push_record({'v1' : 1})
        self.assertRaises(VariableChangeError, ds.push_variable, 'v1', 'string')

    def test_variable_index_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')

        ds.push_variable('pid', 'string', index_position=0)
        ds.push_variable('age', 'int')
        
        ds.push_record({'pid' : 'CE01', 'age' : 54})
        ds.push_record({'pid' : 'CE01', 'age' : 55})
        ds.push_record({'pid' : 'CE02', 'age' : 33})

        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'pid' : ['CE01', 'CE02'],
                                          'age' : [55, 33]})
                            .set_index(['pid'])))

        ds.push_variable('pid', 'string', index_position=None)

        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'pid' : ['CE01', 'CE02'],
                                          'age' : [55, 33]})))

        ds.push_record({'pid' : 'CE02', 'age' : 42})
        assert_frame_equal(ds.head_df(),
                           (pd.DataFrame({'pid' : ['CE01', 'CE02', 'CE02'],
                                          'age' : [55, 33, 42]})))

        self.assertRaises(VariableChangeError,
                          ds.push_variable('pid', 'string', index_position=0))

    def test_variable_unique_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_record({'v1' : 'test'})
        ds.push_variable('v1', 'string', unique=True)
        
        self.assertRaise(InvalidValueError, ds.push_record, {'v1' : 'test'})

        ds.push_variable('v1', 'string', unique=False)
        ds.push_record({'v1' : 'test'})
        self.assertRaises(VariableChangeError, ds.push_variable, 'v1', 'string',
                          unique=True)

    def test_variable_nullable_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string', nullable=False)
        self.assertRaise(InvalidValueError, ds.push_record, {'v1' : None})

        ds.push_variable('v1', 'string', nullable=True)
        ds.push_record({'v1' : None})
        self.assertTrue(ds.head_df('validity').all(axis=None))

        self.assertRaise(VariableChangeError, ds.push_variable, 'v1', 'string',
                         nullable=False)

    def test_variable_lock(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('v2', 'int')
        ds.push_variable('v3', 'string')

        ds.push_record({'v1' : 'test',
                        'v2' : 10,
                        'v3' : 'other'})
        ds.push_record({'v1' : 'test2',
                        'v2' : 23,
                        'v3' : 'other2'})
        ds.remove_variable('v1')
        expected_head_df = pd.DataFrame({'v2' : [10, 23],
                                         'v3' : ['other', 'other2']})
        assert_frame_equal(ds.head_df(), expected_head_df)

        ds2 = DataStore.from_files(self.filesystem)
        assert_frame_equal(ds2.head_df(), expected_head_df)

        ds.lock_variables()
        self.assertRaises(LockedVariables, ds.remove_variable, 'v2')

        ds2.refresh()
        self.assertRaises(LockedVariables, ds2.remove_variable, 'v2')

    def test_variable_order(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('v2', 'int')
        ds.push_variable('v3', 'string')
        self.assertSequenceEqual(ds.head_df().columns,
                                 ['v1', 'v2', 'v3'])

        ds2 = DataStore.from_files(self.filesystem)

        ds.push_variable('v1', 'string', column_position=3)
        ds.push_variable('v2', 'int', column_position=1)
        ds.push_variable('v3', 'string', column_position=2)
        ds.push_variable('v4', 'string')

        self.assertSequenceEqual(ds.head_df().columns,
                                 ['v2', 'v3', 'v1', 'v4'])
        
        ds.push_variable('v1', 'string', column_position=1)
        self.assertSequenceEqual(ds.head_df().columns,
                                 ['v2', 'v1', 'v3'])
        
        ds.push_variables({'var_label': ['v4'],
                           'position' : [10]})
        self.assertSequenceEqual(ds.head_df().columns,
                                 ['v2', 'v1', 'v3', 'v4'])
        ds2.refresh()
        self.assertSequenceEqual(ds2.head_df().columns,
                                 ['v2', 'v1', 'v3', 'v4'])
        
        ds.push_variables({'var_label': ['va'],
                           'position' : [1.5]})
        self.assertSequenceEqual(ds.head_df().columns,
                                 ['v2', 'va', 'v1', 'v3', 'v4'])
        ds2.refresh()
        self.assertSequenceEqual(ds2.head_df().columns,
                                 ['v2', 'va', 'v1', 'v3', 'v4'])

    def test_flag_indexed_head_df(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('vid', 'string', index=0)
        ds.push_variable('age', 'int')

        ds.push_flag(0, 'to_check', 'triangle_orange')
        ds.push_flag(1, 'double_checked', 'tick_mark_green')

        tidx = ds.push_record({'vid' : 'ID1', 'age' : 111})
        ds.flag(tidx, 'age', 1) # flag using tracking index
        ds.flag('ID1', 'age', 1<<2) # flag using head index

        symbols_full_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(symbols_full_df.loc[tidx, 'age'],
                                 ['double_checked'])

        symbols_head_df = ds.head_df('single_flag_symbols')
        self.assertSequenceEqual(symbols_head_df.loc['ID1', 'age'],
                                 ['tick_mark_green'])

    def test_flag_definition(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')

        ds.push_flag(0, 'to_check', 'triangle_orange')
        ds.push_flag(1, 'dummy', 'question_mark')
        ds.push_flag(2, 'double_checked', 'tick_mark_green')

        self.assertEqual(ds.flag_index_as_symbol(0), 'triangle_orange')
        self.assertEqual(ds.flag_index_as_label(0), 'to_check')
        self.assertEqual(ds.flag_index_as_symbol(1), 'dummy')
        self.assertEqual(ds.flag_index_as_label(1), 'question_mark')

        self.assertRaises(InvalidFlagIndex, ds.flag_index_as_symbols, 3)
        self.assertRaises(InvalidFlagIndex, ds.push_flag_definition,
                          flag_index=65, flag_label='f',
                          flag_symbol='triangle_orange')

        tidx1 = ds.push_record({'v1' : 'has flags'}),
        ds.flag(tidx1, 'v1', 1<<1)
        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(single_flag_symbols_df.loc[tidx1, 'v1'],
                                 ['dummy'])

        ds.push_flag_definition(1, 'error', 'cross_red')

        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assert_equal(single_flag_symbols_df.loc[tidx1, 'v1'],
                          ['cross_red'])

    def test_many_flags(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')

        ds.push_flag_definition(0, 'to_check', 'triangle_orange')
        ds.push_flag_definition(1, 'dummy', 'question_mark')
        ds.push_flag_definition(2, 'double_checked', 'tick_mark_green')
    
        tidx = ds.push_records([{'v1' : 'has flags'},
                                {'v1' : 'one flag'},
                                {'v1' : 'no flag'}]),

        ds.flag(tidx[0], 'v1', 1|(1<<2))
        ds.flag(tidx[1], 'v1', (1<<1))
        ds.flag(tidx[2], 'v1', 0)

        self.assertSequenceEqual(ds.flags_of(tidx[0], 'v1'),
                                 [0, 2])
        self.assertSequenceEqual(ds.flags_of(tidx[1], 'v1'),
                                 [1])
        self.assertSequenceEqual(ds.flags_of(tidx[2], 'v1'),
                                 [])

        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(single_flag_symbols_df.loc[tidx, 'v1'],
                                 ['many', 'question_mark', pd.NA])

        tidx2 = ds.push_record(values={'v1' : 'one flag bis'},
                               tracking_index=tidx[1])
        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(single_flag_symbols_df.loc[tidx2, 'v1'],
                                 ['many', pd.NA, pd.NA])

        ds.flag(tidx[1], 'v1', 1|(1<<1))
        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(single_flag_symbols_df.loc[tidx[1], 'v1'],
                                 ['many', 'many', pd.NA])

    def test_flag_update(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')

        ds.push_flag_definition(0, 'to_check', 'triangle_orange')
        ds.push_flag_definition(1, 'dummy', 'question_mark')
        ds.push_flag_definition(2, 'double_checked', 'tick_mark_green')

        ds.flag('id1', 'v1', 1<<1)
        self.assertSequenceEqual(ds.flags_of('id1', 'v1'),
                                 [1])

        ds.flag('id1', 'v1', 1 | (1<<1))
        self.assertSequenceEqual(ds.flags_of('id1', 'v1'),
                                 [0, 1])
        
    def test_refresh(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds1.set_user('me')

        ds2 = DataStore.from_files(self.filesystem)

        v_def = {'var_label' : 'v1', 'var_type' : 'string'}
        ds1.push_variable(**v_def)
        ds2.refresh()
        self.assertSequenceEqual(list(ds2.variables), [v_def])

        ds1.push_record({'v1' : 'first_val'})
        ds2.refresh()
        assert_frame_equal(ds2.head_df(), pd.DataFrame({'v1' : ['first_val']}))

        ds1.push_flag_definition(0, 'to_check', 'triangle_orange')

        idx = ds1.push_record({'v1' : 'has flag'})
        ds.flag(idx, 'v1', 0)

        ds2.refresh()
        self.assert_equal(ds2.flags_of(idx, 'v1'), [0])

    def test_user(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        tidx0 = ds.push_variable('v1', 'string')
        vars_full_df = ds.variables.store.full_df()
        self.assertEqual(vars_full_df.loc[tidx0,
                                          ('var_label', 'user')], 'me')

        tidx1 = ds.push_record({'v1' : 'test'})
        tidx2 = ds.push_record({'v1' : 'test2'},
                               tracking_index=tidx1)

        full_user_df = ds.full_df('user')
        self.assertEqual(full_user_df.loc[tidx1, 'v1'], 'me')
        self.assertEqual(full_user_df.loc[tidx2, 'v1'], 'me')

        self.assertEqual(ds.head_df('user').loc[0, 'v1'], 'me')

        # change user
        ds.set_user('me2')

        # Add some data
        tidx3 = ds.push_record({'v1' : 'test3'}, tracking_index=tidx2)

        self.assertEqual(ds.full_df('user').loc[tidx3, 'v1'], 'me2')
        self.assertEqual(ds.head_df('user').loc[0, 'v1'], 'me2')

        # Add a new variable
        tidx4 = ds.push_variable('v2', 'int')
        vars_full_df = ds.variables.full_df('user')
        self.assertEqual(vars_full_df.loc[tidx4, 'v2'], 'me2')

        self.assertTrue(pd.isna(ds.full_df('user').loc[tidx3, 'v2']))
        self.assertTrue(pd.isna(ds.head_df('user').loc[0, 'v2']))
        
    def test_head_df_no_index_sorted_by_time(self):
        raise NotImplementedError()

    def test_timestamp(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('v2', 'string')
        ts1 = datetime(2020,1,2,10,12)
        tidx1 = ds.push_record({'v1' : 'test', 'v2' : 'other'},
                               timestamp=ts1)
        ts_df = ds.head_df('timestamp')
        self.assertEqual(ts_df.loc[0, 'v1'], ts1)
        self.assertEqual(ts_df.loc[0, 'v2'], ts1)

        ts2 = datetime(2020,1,2,10,12)
        ds.push_record({'v1' : 'test2'},
                       tracking_index=tidx1,
                       timestamp=ts2)
        ts_df = ds.head_df('timestamp')
        self.assertEqual(ts_df.loc[0, 'v1'], ts2)
        self.assertEqual(ts_df.loc[0, 'v2'], ts1)

    def test_comment(self):
        # Input comments are bound to input values
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('v2', 'string')
        tidx1 = ds.push_record({'v1' : 'test', 'v2' : 'other'},
                               comment={'v1': None,
                                        'v2': 'orig comment'})
        comment_df = ds.head_df('comment')
        self.assertTrue(pd.isna(comment_df.loc[0, 'v1']))
        self.assertEqual(comment_df.loc[0, 'v2'], 'orig comment')

        ds.push_record({'v1' : 'test2'},
                       comment={'v1':'new comment'},
                       tracking_index=tidx1)
        self.assertEqual(comment_df.loc[0, 'v1'], 'new comment')
        self.assertEqual(comment_df.loc[0, 'v2'], 'orig comment')

    def test_annotation(self):
        # Annotations are comment threads associated with an index
        # and a variable
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        tidx1 = ds.push_record({'v1' : 'test'})

        ds.annotate(tidx1, 'v1', 'this was a test', timestamp=ts1)
        
        ts1 = datetime(2020,1,2,10,12)
        a_idx1 = ds.annotate(tidx1, 'v1', 'this was a test', timestamp=ts1)
        ts2 = datetime(2020,1,2,10,13)
        a_idx2 = ds.annotate(tidx1, 'v2', 'this really was a test',
                             timestamp=ts2)

        expected_annotations = {
            'annotation' : ['this was a test',
                            'this really was a test'],
            'user' : ['me', 'me'],
            'timestamp' : [ts1, ts2],
            'archived' : [False, False],
        }
        assert_frame_equal(ds.annotations(tidx1, 'v1'),
                           pd.DataFrame(expected_annotations))
        ds.archive_annotation(a_idx1, 'v1')

        expected_annotations = {
            'annotation' : ['this really was test',
                             'this really was a test'],
            'user' : ['me', 'me'],
            'timestamp' : [ts1, ts2],
            'archived' : [True, False]
        }
        assert_frame_equal(ds.annotations(tidx1, 'v1'),
                           pd.DataFrame(expected_annotations))

    def test_conflict_update(self):
        
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        idx1 = ds1.push_record({'v1', 'orig'})
        
        ds2 = DataStore.from_files(self.filesystem)

        idx2 = ds1.push_record({'v1', 'update from ds1'}, index=idx1)
        idx3 = ds2.push_record({'v1', 'conflicting update from ds2'},
                               index=idx1)

        ds1.refresh()
        ds2.refresh()

        self.assertIn('conflict', ds1.head_df('validity').loc[idx2, 'v1'])
        self.assertIn('conflict', ds2.head_df('validity').loc[idx3, 'v1'])

    def test_conflict_unique(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds1.set_user('me')
        ds1.push_variable('v1', 'string', unique=True)
        
        ds2 = DataStore.from_files(self.filesystem)

        idx1 = ds1.push_record({'v1', 'unique value'})
        idx2 = ds2.push_record({'v1', 'unique value'})

        ds1.refresh()
        ds2.refresh()

        self.assertIn('non-unique', ds1.head_df('validity').loc[idx1, 'v1'])
        self.assertIn('non-unique', ds2.head_df('validity').loc[idx2, 'v1'])

    def test_user_view(self):
        # Any cell of head where user name is in value
        pass

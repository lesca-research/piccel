# -*- coding: utf-8 -*-
import os.path as op
import io
from itertools import product, chain
from datetime import datetime, date, timezone
from copy import deepcopy
from collections import defaultdict
from functools import partial
from pathlib import PurePath
import tempfile
import logging
import csv
import json

# UUID1: MAC addr + current timestamp with nanosec precision
# UUID4: 122 bytes random number
from uuid import uuid1, uuid4

import numpy as np
import pandas as pd
from pandas.testing import assert_frame_equal, assert_series_equal

from .core import if_none, Notifier
from .io.filesystem import LocalFileSystem
from .logging import logger, debug2, debug3

from pyfakefs.fake_filesystem_unittest import TestCase
#from unittest import TestCase

DATE_FORMAT = '%Y-%m-%d'
QDATE_FORMAT = 'yyyy-MM-dd'
DATETIME_FORMAT = '%Y-%m-%d %H:%M:%S.%f' # TODO handle timezone?

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
        'unformat' : lambda s : s,
        'format' : lambda v : v,
        'validate_dtype_pd' : pd.api.types.is_string_dtype,
        'null_value' : '',
        'na_value' : pd.NA,
        'corner_cases' : {'':'', 'a´*€$éà ':'a´*€$éà ', '12':'12',
                          'False':'False', '2020-01-02':'2020-01-02'},
        'bad_format_cases' : [],
    },
    'int' : {
        'dtype_pd' : 'Int64', # TODO for non-NA values,
                              # int64 may be more efficient
        'unformat' : lambda s : np.int64(s),
        'format' : lambda i : '%d' % i,
        'validate_dtype_pd' : pd.api.types.is_int64_dtype,
        'null_value' : np.int64(0),
        'na_value' : pd.NA,
        'corner_cases' : {'0':np.int64(0), '-1':np.int64(-1),
                          '12345':np.int64(12345)},
        'bad_format_cases' : ['1.1', '', 'text', '1+2'],
    },
    'singleton' : { # used to force data_store to have one single entry
        'dtype_pd' : 'string',
        'unformat' : lambda s : s,
        'format' : lambda v : v,
        'validate_dtype_pd' : pd.api.types.is_string_dtype,
        'validate_value' : lambda v: v == '1',
        'null_value' : '1',
        'na_value' : '1',
        'corner_cases' : {'1' : '1'},
        'bad_format_cases' : ['0', '', 'False'],
    },
    'boolean' : {
        'dtype_pd' : 'boolean',
        'unformat' : unformat_boolean,
        'format' : lambda b : str(b),
        'validate_dtype_pd' : pd.api.types.is_bool_dtype,
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
        'corner_cases' : {'0':0, '0.0':0, '-1.4':-1.4,
                          '3.141592653589793':np.pi},
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
        'null_value' : datetime.now(),
        'na_value' : pd.NaT,
        'corner_cases' : {'2011-11-04 00:05:23.283+00:00':
                          datetime(2011, 11, 4, 0, 5, 23, 283000)},
        'bad_format_cases' : ['01-02-2020', '2011-11-04 00h05',
                              'true', 'text', 'np.pi'],
    }
}
def unformat(s, var_type):
    if s == '':
        return VTYPES[var_type]['na_value']
    else:
        return VTYPES[var_type]['unformat'](s)

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
class IndexNotFound(Exception): pass
class InvalidImport(Exception): pass

class Var:
    def __init__(self, var_label, var_type, index_position=None, is_unique=False,
                 is_used=True, nullable=True, column_position=None):

        self.var_label = var_label

        if var_type not in VTYPES:
            raise BadVariableType(var_type)
        self.var_type = var_type

        if pd.isna(index_position):
            index_position = None
        self.index_position = index_position

        if index_position is not None:
            if nullable:
                logger.warning('Index variable %s cannot be NA', var_label)
            nullable = False

        self.is_unique = is_unique
        self.is_used = is_used
        self.nullable = nullable

        if pd.isna(column_position):
            column_position = None
        self.column_position = column_position

    def is_index(self):
        return self.index_position is not None

    def __eq__(self, other):
        return self.asdict() == other.asdict()

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
        return iter(self.variables.values())

    def indexes(self):
        return list(sorted((v for v in self.variables.values()
                            if v.is_index()),
                           key=lambda e: e.index_position))

    def validate_dtypes(self):
        return False # stub

    def refresh(self):
        pass

class PersistentVariables:
    
    META_VARS = [
        Var('var_label', 'string', index_position=0, nullable=False),
        Var('var_type', 'variable_type', nullable=False),
        Var('nullable', 'boolean', nullable=False),
        Var('index_position', 'number', is_unique=True, nullable=True),
        Var('is_unique', 'boolean', nullable=False),
        Var('is_used', 'boolean', nullable=False),
        Var('column_position', 'number'),
    ]

    def __init__(self, parent_store):
        self.parent_store = parent_store
        self.store = DataStore(parent_store.filesystem,
                               label=parent_store.label + '_vars', 
                               variables=PersistentVariables.META_VARS,
                               use_annotations=False,
                               use_properties=False,
                               validate_entry=self.validate_entry,
                               notifications={'pushed_entry' :
                                              parent_store.on_variable_entry},
                               log_label=parent_store.log_label + '_vars')
        self.logger = DataStoreLogger(logger,
                                      {'store_label' : self.store.label+'_PV'})

    def __iter__(self):
        hdf = self.store.head_df().drop(columns=DataStore.TRACKING_INDEX_LEVELS)
        return (Var(idx, **row) for idx, row in hdf.iterrows())

    def indexes(self):
        return list(sorted((v for v in self if v.is_index()),
                           key=lambda e: e.index_position))
    def refresh(self):
        self.store.refresh()
    
    def validate_entry(self, store, new_entry):
        current_vars_df = store.head_df()
        # Check only modified variables
        new_entry = new_entry.set_index('var_label')
        modified_vars = new_entry.index.intersection(current_vars_df.index)
        new_entry = new_entry.loc[modified_vars]
        previous = current_vars_df.loc[modified_vars]

        def index_vars(var_df):
            m_index = ~pd.isna(var_df['index_position'])
            return var_df.index[m_index].sort()

        if self.parent_store.variables_are_locked():
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
            if self.parent_store.data_is_empty(): # no data yet, allow any change
                return df_like(new_entry, fill_value=True, dtype='boolean')
            else:
                full_df = self.parent_store.full_df()
                head_df = self.parent_store.head_df()
                for var_label, mod_var in new_entry.iterrows():
                    # TODO handle change of var_label?
                    current_var = current_vars_df.loc[var_label]
                    # check type change
                    if ( current_var['var_type'] != mod_var['var_type'] and
                         (current_var['var_type'], mod_var['var_type']) not in
                         ALLOWED_VARIABLE_TYPE_CHANGE ):
                        self.logger.error('Variable %s cannot change type '
                                          '%s to %s', var_label,
                                          current_var['var_type'],
                                          mod_var['var_type'])
                        raise VariableChangeError(var_label)
                    # check uniqueness / index
                    if (not current_var['is_unique'] and
                        mod_var['is_unique'] and
                        not head_df[var_label].is_unique):
                        # TODO actually check that values are not unique
                        self.logger.error('Variable %s cannot become unique',
                                          var_label)
                        raise VariableChangeError(var_label)
                    if (pd.isna(current_var['index_position']) and
                          not pd.isna(mod_var['index_position'])):
                        self.logger.error('Variable %s cannot become an index',
                                          var_label)
                        raise VariableChangeError(var_label)
                    # check nullable
                    if ((current_var['nullable'] and
                        not  mod_var['nullable']) and
                        pd.isna(full_df[var_label]).any()):
                        self.logger.error('Variable %s cannot become nullable',
                                          var_label)
                        raise VariableChangeError(var_label)

def df_like(df, fill_value=pd.NA, dtype=None):
    new_df = pd.DataFrame().reindex_like(df).fillna(fill_value)
    if dtype is not None:
        new_df = new_df.astype(dtype)
    return new_df

class PersistentLogic:
    STORE_VARS = [
        Var('code_entry', 'ds_code_entry', index_position=0, nullable=False),
        Var('code', 'string')
    ]

    def __init__(self, parent_store):

        # TODO pass code validation function
        # TODO adapt notifications and process updates/new entries
        #      see import_df
        self.store = DataStore(parent_store.filesystem,
                               label=parent_store.label + '_code', 
                               variables=PersistentLogic.STORE_VARS,
                               use_annotations=False,
                               use_properties=False,
                               notifications={'pushed_entry' :
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
        if isinstance(msg, pd.DataFrame):
            msg = '\n' + str(msg)
        return '[%s] %s' % (self.extra['store_label'], msg), kwargs

class DataStore:

    # nofitications:
    # TODO adapt see import_df
    # 'pushed_entry', 'deleted_entry', 'variables_changed', 'flags_changed'
    # 'pushed_annotation'

    CSV_SEPARATOR = ','

    TRACKING_INDEX_LEVELS = ['__entry_id__',
                             '__version_idx__',
                             '__conflict_idx__']

    DATA_LABELS = ('value', 'timestamp', 'user', 'comment', 'validity')

    FLAG_DEF_VARS = [
        Var('flag_index', 'flag_index', index_position=0, nullable=False),
        Var('flag_label', 'string', is_unique=True),
        Var('flag_symbol', 'symbol'),
    ]

    FLAG_ENTRY_VARS = [
        Var('index_hash', 'int', index_position=0, nullable=False),
        Var('index_repr', 'string', nullable=False),
        Var('variable', 'string', index_position=1, nullable=False),
        Var('flag', 'int'),
    ]

    NOTES_VARIABLES = [
        Var('index_hash', 'int', index_position=0, nullable=False),
        Var('index_repr', 'string', nullable=False),
        Var('variable', 'string', index_position=1, nullable=False),
        Var('note', 'string'),
        Var('archived', 'boolean', nullable=False),
    ]

    PROPERTY_VARS = [
        Var('singleton', 'singleton', index_position=0, nullable=False),
        Var('variables_locked', 'boolean', nullable=False)
    ]

    DATA_FILE_EXT = '.csv'

    def __init__(self, filesystem, label=None, variables=None,
                 use_annotations=True, logic=None, validate_entry=None,
                 notifications=None, use_properties=True, log_label=None):
        """
        For variables and logic, use persistent versions with history if they
        are None.
        """
        expected_label = DataStore.label_from_filesystem(filesystem)
        logger.debug('DataStore init - resolve data directory. '
                     'Given label=%s, label from fs=%s',
                     label, expected_label)
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

        self.log_label = if_none(log_label, self.label)
        self.logger = DataStoreLogger(logger, {'store_label' : self.log_label})

        self.notifier = Notifier(notifications)

        self.logger.debug('Init dataframes')
        self.dfs = {}
        self.head_dfs = {}        
        for label in DataStore.DATA_LABELS:
            self.dfs[label] = (self.empty_df()
                               .set_index(DataStore.TRACKING_INDEX_LEVELS))
            self.head_dfs[label] = None
        self.data_files = pd.Series([], index=self.dfs['value'].index)

        self.props_ds = None
        if use_properties:
            self.logger.debug('Init property datastore')
            self.props_ds = DataStore(self.filesystem,
                                      label=self.label + '_props',
                                      variables=DataStore.PROPERTY_VARS,
                                      use_annotations=False,
                                      use_properties=False,
                                      log_label=self.log_label + '_props') 
            if self.props_ds.data_is_empty():
                self.props_ds.push_record({'variables_locked' : False})
        
        if variables is not None:
            self.logger.debug('Use fixed variables')
            self.variables = FixedVariables(variables)
            self.process_variable_changes([(None, variable.asdict())
                                           for variable in self.variables])
        else:
            self.logger.debug('Init variables datastore')
            self.variables = PersistentVariables(self)

        self.flag_ds = None
        self.note_ds = None
        if use_annotations:
            self.logger.debug('Init flag definition datastore')
            # TODO adapt notifications
            self.flag_defs_ds = DataStore(self.filesystem,
                                          label=self.label + '_flag_defs',
                                          variables=DataStore.FLAG_DEF_VARS,
                                          use_annotations=False,
                                          use_properties=False,
                                          notifications={'pushed_entry':
                                                         self.on_pushed_flag_def},
                                          log_label=self.log_label + '_flag_defs')

            self.logger.debug('Init flag datastore')
            self.flag_ds = DataStore(self.filesystem,
                                     label=self.label + '_flags',
                                     variables=DataStore.FLAG_ENTRY_VARS,
                                     use_annotations=False,
                                     use_properties=False,
                                     notifications={'pushed_entry':
                                                    self.on_pushed_flag_def},
                                     log_label=self.log_label + '_flags')

            self.logger.debug('Init note datastore')
            self.note_ds = DataStore(self.filesystem,
                                     label=self.label + '_notes',
                                     variables=DataStore.NOTES_VARIABLES,
                                     use_annotations=False,
                                     use_properties=False,
                                     notifications={'pushed_entry':
                                                    self.on_pushed_note},
                                     log_label=self.log_label + '_notes')

        self.validate_entry = if_none(validate_entry, lambda ds, df: None)
        if 0:
            if logic is not None:
                self.logic = logic # expect DataStoreLogic
            else:
                self.logic = PersistentLogic(self)

        self.user = None

        self.filesystem.makedirs('data')
        self.filesystem.enable_track_changes()

        self._refresh_data()

    def variables_are_locked(self):
        return self.props_ds.head_df()['variables_locked'].iat[0]

    def data_is_empty(self):
        return self.dfs['value'].empty

    def _refresh_data(self):
        self.logger.debug('Refresh data')
        modified_files, new_files, deleted_files = \
            self.filesystem.external_changes('data')
        if len(new_files) != 0:
            self.logger.debug('Files externally added: %s', new_files)
        if len(modified_files) != 0:
            self.logger.debug('Files externally modified: %s', modified_files)
        if len(deleted_files) != 0:
            self.logger.debug('Files externally deleted: %s', deleted_files)

        def _is_data_file(fn):
            return (fn.startswith('data') and
                    fn.endswith(DataStore.DATA_FILE_EXT))

        new_data_files = [fn for fn in new_files if _is_data_file(fn)]
        modified_data_files = [fn for fn in modified_files if _is_data_file(fn)]
        deleted_data_files = [fn for fn in deleted_files if _is_data_file(fn)]

        to_delete = set()
        for del_fn in chain(deleted_data_files, modified_data_files):
            m_delete = self.data_files == del_fn
            to_delete.update(self.dfs['value'].index[m_delete])
            self.data_files = self.data_files[~m_delete]
        for df_label, df in self.dfs.items():
            self.dfs[df_label] = df.drop(index=to_delete)
        self.notifier.notify('deleted_entries', to_delete)

        entry_dfs = defaultdict(list)
        for data_fn in chain(modified_data_files, new_data_files):
            content = json.loads(self.filesystem.load(data_fn))
            entry_dfs = {k:self.df_from_str(df_content, k)
                         for k, df_content in content.items()}
            # TODO: align entry_dfs with current variables
            self.import_df(entry_dfs, from_file=data_fn,
                           raise_error=False) # will notify added_entries
        self.filesystem.accept_all_changes('data')

    def df_from_str(self, df_str, data_label):
        if df_str == '':
            return pd.DataFrame()
        if data_label == 'value':
            converters = {v.var_label:partial(unformat, var_type=v.var_type)
                          for v in self.variables}
        elif data_label == 'timestamp':
            ufmt = partial(unformat, var_type='datetime')
            converters = {v.var_label : ufmt for v in self.variables}
        else:
            converters = None
        df = pd.read_csv(io.StringIO(df_str), sep=DataStore.CSV_SEPARATOR,
                         engine='python', index_col=False,
                         converters=converters)

        def hex_to_int(h):
            try:
                return np.int64(int(h, 16))
            except OverflowError:
                # TODO: check if that can still happen...
                logger.error('+++++++++++++++++++++++++++++++++++++++++')
                logger.error('Cannot convert uuid to signed int64. ' \
                             'Generate a new one. This must be saved later!')
                logger.error('+++++++++++++++++++++++++++++++++++++++++')
                return np.int64(int.from_bytes(uuid1().bytes,
                                               byteorder='big',
                                               signed=True) >> 64)
        df['__entry_id__'] = (df['__entry_id__']
                              .apply(hex_to_int)
                              .astype(np.int64))
        df['__version_idx__'] = (df['__version_idx__'].apply(int)
                                 .astype(np.int64))
        df['__conflict_idx__'] = np.int64(0)
        return df.set_index(DataStore.TRACKING_INDEX_LEVELS)

    def df_to_str(self, df, data_label):
        if df is None or df.shape[0] == 0:
            return ''

        for variable in self.variables:
            #self.logger.debug('df_to_str: format col %s', variable.var_label)
            fmt = None
            if data_label == 'value':
                fmt = VTYPES[variable.var_type]['format']
            elif data_label == 'timestamp':
                fmt = VTYPES['datetime']['format']

            if fmt is not None:
                f = lambda v: (fmt(v) if not pd.isna(v) else '')
                df[[variable.var_label]] = df[[variable.var_label]].applymap(f)

        try:
            df = df.reset_index().drop(columns=['__conflict_idx__'])
        except:
            from IPython import embed; embed() 
        df['__entry_id__'] = df['__entry_id__'].apply(lambda x: hex(x))
        df['__version_idx__'] = df['__version_idx__'].apply(str)
        content = df.to_csv(sep=DataStore.CSV_SEPARATOR, index=False,
                            quoting=csv.QUOTE_NONNUMERIC)
        return content

    def import_df(self, other_dfs, raise_error=True, from_file=None):
        """
        other_dfs: dict(label : panda.DataFrame)
        where labels are 'value', 'comment', 'user', 'timestamp'
        """
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        for df in other_dfs.values():
            if df.index.names != t_levels:
                raise Exception('Can only merge df with tracking index')

        other_value_df = other_dfs['value']
        main_value_df = self.dfs['value']
        self.logger.debug('Import value df:')
        self.logger.debug(other_value_df)
        self.logger.debug('Current main value df:')
        self.logger.debug(main_value_df)

        # Sort out conflicting entries (same entry id and version index)
        # There can already be some conflicting entries in main
        # So gather them all, sort by timestamp and reassign conflict indexes
        conflicting = (other_value_df.index
                       .intersection(main_value_df.index))
        if len(conflicting) != 0:
            self.logger.debug('Fixing %d conflicting entries...',
                              len(conflicting))
            main_value_df = main_value_df.copy()
            main_value_df['__origin_idx__'] = np.arange(main_value_df.shape[0],
                                                        dtype=int)
            main_value_df['__timestamp__'] = self.dfs['timestamp'].max()
            main_index = main_value_df.index.to_numpy()

            done = set()
            other_value_df = other_dfs['value'].copy()
            other_value_df['__origin_idx__'] = np.arange(other_value_df.shape[0],
                                                         dtype=int)
            other_value_df['__timestamp__'] = other_dfs['timestamp'].max()
            other_index = other_value_df.index.to_numpy()
            for eid, vidx, cidx in conflicting:
                if (eid, vidx) not in done:
                    done.add((eid, vidx))
                    o = (other_value_df.loc[(eid, vidx)][['__timestamp__',
                                                          '__origin_idx__']]
                         .reset_index())
                    o['__origin__'] = 'other'
                    o['__entry_id__'] = eid
                    o['__version_idx__'] = vidx
                    
                    m = (main_value_df.loc[(eid, vidx)][['__timestamp__',
                                                         '__origin_idx__']]
                         .reset_index())
                    m['__origin__'] = 'main'
                    m['__entry_id__'] = eid
                    m['__version_idx__'] = vidx
                    
                    om = pd.concat((o, m)).sort_values(by=['__timestamp__'])
                    om['__conflict_idx__'] = np.arange(om.shape[0],
                                                       dtype=np.int64) + 1
                    om = om.set_index(t_levels)
                    om_other = om[om.__origin__ == 'other']
                    other_index[(om_other.__origin_idx__,)] = om_other.index
    
                    om_main = om[om.__origin__ == 'main']
                    main_index[(om_main.__origin_idx__,)] = om_main.index

            other_value_df = other_value_df.drop(columns=['__timestamp__',
                                                         '__origin_idx__'])
            other_value_df.index = (pd.MultiIndex
                                    .from_tuples(other_index,
                                                 names=t_levels))
            main_value_df = main_value_df.drop(columns=['__timestamp__',
                                                        '__origin_idx__'])
            main_value_df.index = (pd.MultiIndex
                                   .from_tuples(main_index,
                                                names=t_levels))
        else:
            self.logger.debug('No conflict')
        other_columns = set(other_value_df.columns)
        fill_missing_columns = False
        if set(main_value_df.columns) != other_columns:
            self.logger.debug('Missing columns in df to import')
            cols_to_fill = [c for c in main_value_df.columns
                            if c not in other_columns
                            and not c.startswith('__')]
            filled_variables = [v for v in self.variables
                                if v.var_label not in other_columns]

            # Fill missing columns with NA values
            for var in filled_variables:
                other_value_df[var.var_label] = VTYPES[var.var_type]['na_value']

            # For entries that are updates, duplicate head values
            # to fill missing columns
            m_update = (other_value_df.index
                        .get_level_values('__version_idx__') != 0)
            before_update = other_value_df.index[m_update].to_frame()
            before_update.__version_idx__ = before_update.__version_idx__ - 1
            head_df = (self.head_df('value').reset_index()
                       .set_index(t_levels)
                       .loc[pd.MultiIndex.from_frame(before_update)])
            filled_cols = [v.var_label for v in filled_variables]
            if m_update.sum() != 0:
                other_value_df.loc[m_update, filled_cols] = head_df[filled_cols]
            fill_missing_columns = True
        else:
            self.logger.debug('No missing column in df to import')
        # First try to merge value and see if merged data is valid
        # if ok, merge everything
        merged_value_df = pd.concat((main_value_df, other_value_df))
        self.logger.debug('Merge:')
        self.logger.debug(merged_value_df)
        self.validate_entry(self, merged_value_df) # External validation
        validity = self.validate(merged_value_df)
        self.logger.debug('Validity:')
        self.logger.debug(validity)
        m_invalid = validity.loc[other_value_df.index] != ''
        other_invalid_index = other_value_df[m_invalid].index
        if m_invalid.sum().sum() > 0:
            if raise_error:
                self.logger.debug('Invalid entries:')
                # TODO fix reporting of validity
                self.logger.debug(validity[m_invalid])
                raise InvalidImport(other_invalid_index)

        self.data_files.index = main_value_df.index
        new = pd.Series([pd.NA] * len(other_value_df.index),
                        index=other_value_df.index)
        self.data_files = pd.concat((self.data_files, new), axis=1)
        # TODO notify invalid entries
        for df_label in self.dfs:
            if df_label == 'value':
                self.dfs[df_label] = merged_value_df
            elif df_label == 'validity':
                self.dfs[df_label] = validity
            else:
                # TODO Duplicate head values for all columns in main not in other
                main_df = self.dfs[df_label]
                other_df = other_dfs[df_label]
                if len(conflicting) != 0:
                    # Apply fixed conflicts
                    main_df.index = main_value_df.index
                    other_df.index = other_value_df.index
                if fill_missing_columns:
                    # Fill missing columns with NA values
                    for var in filled_variables:
                        other_df[var.var_label] = VTYPES[var.var_type]['na_value']

                    head_df = (self.head_df(df_label).reset_index()
                               .set_index(t_levels)
                               .loc[pd.MultiIndex.from_frame(before_update)])
                    if m_update.sum() != 0:
                        other_df.loc[m_update, filled_cols] = \
                            pd.concat((other_df, head_df[filled_cols]),
                                      axis=0)
                self.dfs[df_label] = pd.concat((main_df, other_df))

        if from_file is not None:
            self.data_files.loc[other_value_df.index] = from_file

        self.invalidate_cached_views()
        self.notifier.notify('pushed_entry', self, other_value_df)
        # TODO: notify merge
        # TODO: notify index change if any conflict

        # max_ver_idx = max version_idx from other & main
        # new entry: other_df.ver_idx == max_ver_idx and ver_idx == 0 
        # new full-only entry: where other.ver_idx is less than max_ver_idx
        # updated entry: ver_idx greater than 0
        # updated non-head entry: other.ver_idx less than max_version_idx
        #                         and ver_idx greater than 0
        # updated head entry: other.ver_idx == max_version_idx
        #                     and ver_idx greater than 0
        return other_value_df.index


    def validate(self, value_df):
        """ 
        ASSUME df has tracking index and columns consistent with current
        variable definitions
        """
        validity = df_like(value_df, fill_value='', dtype='string')

        # Checks on full df
        # TODO check dtypes

        # TODO report conflicts?

        hdf = value_df.groupby(level=0, group_keys=False).tail(1)

        # Check uniquess for index variables
        index_vars = [v.var_label for v in self.variables if v.is_index()]
        m_dups = hdf[index_vars].duplicated(keep=False)
        if m_dups.sum() != 0:
            validity.loc[hdf.index[m_dups], index_vars] += \
                ', non-unique-index'

        # Check conflicting updates
        m_conflict = value_df.index.get_level_values('__conflict_idx__') != 0
        validity.loc[m_conflict, :] += ', conflicting'

        for variable in self.variables:
            head_values = hdf[variable.var_label]
            if variable.is_unique:
                # Check duplicates only on head
                m_dups = ( (~pd.isna(head_values)) &
                           head_values.duplicated(keep=False) )
                if m_dups.sum() != 0:
                    validity.loc[hdf.index[m_dups], variable.var_label] += \
                        ', non-unique'

            if not variable.nullable:
                # Check na on full
                m_na = pd.isna(value_df[variable.var_label])
                if m_na.sum() != 0:
                    validity.loc[value_df.index[m_na], variable.var_label] += \
                        ', non-null'
        
            validity[variable.var_label] = (validity[variable.var_label]
                                            .str.lstrip(', '))
        return validity

    def __push_records(self, records):
        all_records = {}
        for record in records:
            for k in record:
                if k not in all_records:
                    all_records[k] = []
        
        for record in records:
            for k in all_records:
                if k in record:
                    all_records[k].append(record[k])
                else:
                    all_records[k].append(None)
        return self.push_record(all_records)

    def push_record(self, record, comment=None, timestamp=None,
                    tracking_index=None):
        if isinstance(record, dict):
            records = [record]
        elif isinstance(record, list):
            records = record
        else:
            raise TypeError('Type of record %s not handled' % type(record))
        value_df = pd.DataFrame.from_records(records)
        
        if comment is None:
            comment_df = df_like(value_df, fill_value=pd.NA, dtype='string')
        else:
            comment_df = pd.DataFrame.from_records([comment])

        timestamp_df = df_like(value_df,
                               fill_value=if_none(timestamp,
                                                  datetime.now()),
                               dtype='datetime64[ns]')
        #TODO: handle timezone?

        user_df = df_like(value_df, fill_value=if_none(self.user, pd.NA),
                          dtype='string')

        t_levels = DataStore.TRACKING_INDEX_LEVELS
        if tracking_index is None and set(t_levels).issubset(value_df.columns):
            self.logger.debug('Found tracking index in given record',
                              value_df[t_levels])
            value_df = value_df.set_index(t_levels)
            comment_df = comment_df.set_index(t_levels)
            user_df = user_df.set_index(t_levels)
            timestamp_df = timestamp_df.set_index(t_levels)
        elif tracking_index is not None:
            self.logger.debug('Update from tracking index: %s', tracking_index)
            value_df.index = tracking_index
            comment_df.index = tracking_index
            user_df.index = tracking_index
            timestamp_df.index = tracking_index

        return self.push_df(value_df, comment_df, user_df, timestamp_df)


    def new_entry_id(self):
        """ Return a 64-bit signed int that fits pandas.Int64Index """
        uid = np.int64(int.from_bytes(uuid1().bytes,
                                      byteorder='big',
                                      signed=True) >> 64)

        current_entry_ids = self.dfs['value'].index.get_level_values(0)
        while uid in current_entry_ids:
            uid = np.int64(int.from_bytes(uuid1().bytes,
                                          byteorder='big',
                                          signed=True) >> 64) 
        return uid

    def new_tracking_ids(self, size):
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        new_ids = pd.DataFrame({
            t_levels[0] : [self.new_entry_id() for _ in range(size)],
            t_levels[1] : [0] * size,
            t_levels[2] : [0] * size
        })
        for col in t_levels:
            new_ids[col] = new_ids[col].astype(np.int64)
        return new_ids

    def push_df(self, value_df, comment_df, user_df, timestamp_df):
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        self.logger.debug('Pushing df:')
        self.logger.debug(value_df)
        self.logger.debug('Current main value df:')
        self.logger.debug(self.dfs['value'])
        if value_df.index.names != t_levels:
            index_variables = self.variables.indexes()
            if len(index_variables) > 0:
                singleton_vars = [v.var_label for v in index_variables
                                  if v.var_type == 'singleton']
                index_variables = [v.var_label for v in index_variables]
                self.logger.debug('Join pushed df on index variables %s',
                                  index_variables)

                if (len(singleton_vars) != 0 and
                    not set(singleton_vars).issubset(value_df.columns)):
                    value_df[singleton_vars] = VTYPES['singleton']['na_value']
                    comment_df[singleton_vars] = VTYPES['string']['na_value']
                    user_df[singleton_vars] = VTYPES['string']['na_value']
                    timestamp_df[singleton_vars] = VTYPES['datetime']['na_value']
                try:
                    value_df = value_df.set_index(index_variables)
                except KeyError:
                    raise IndexNotFound(index_variables)
                main_hdf = self.head_df()
                # Resolve entries that are updates of existing ones
                if main_hdf.shape[0] != 0:
                    value_df = value_df.join(main_hdf[t_levels])
                    value_df['__version_idx__'] = value_df['__version_idx__']+1
                else:
                    value_df['__entry_id__'] = pd.NA
                    value_df['__version_idx__'] = pd.NA
                    value_df['__conflict_idx__'] = pd.NA
                self.logger.debug('After resolving updates:')
                self.logger.debug(value_df) 
                m_new = pd.isna(value_df.__entry_id__)
                
                if m_new.sum() != 0:
                    self.logger.debug('Add UIDs for %d new entries',
                                      m_new.sum())
                    value_df.loc[m_new, '__entry_id__'] = \
                        [self.new_entry_id() for _ in range(m_new.sum())]
                    value_df.loc[m_new, '__version_idx__'] = 0
                    value_df.loc[m_new, '__conflict_idx__'] = 0
                self.logger.debug('Before dtype fix:')
                self.logger.debug(value_df)
                for col in t_levels:
                    value_df[col] = value_df[col].astype(np.int64)
                self.logger.debug('After resolving new entries:')
                self.logger.debug(value_df) 

                value_df = value_df.reset_index()

            else: # pushed df has no entry tracking index and
                  # there is no index variable
                  # all pushed entries are considered new
                self.logger.debug('Import pushed df as new entries')
                value_df['__entry_id__'] = \
                    [self.new_entry_id() for _ in range(value_df.shape[0])]
                value_df['__version_idx__'] = 0
                value_df['__conflict_idx__'] = 0

            value_df = value_df.set_index(t_levels)

        else: # pushed df already has entry tracking index
              # TODO: utest push from previous version
            self.logger.debug('Import pushed df using its tracking index')
            m_update = value_df.index.isin(self.dfs['value'].index)
            version_idx = (value_df.index.get_level_values('__version_idx__')
                           .to_numpy())
            version_idx[m_update] += 1
            value_df.index = (value_df.index
                              .set_levels(version_idx, level='__version_idx__'))

        comment_df.index = value_df.index
        user_df.index = value_df.index
        timestamp_df.index = value_df.index

        other_dfs = {
            'value' : value_df,
            'comment' : comment_df,
            'user' : user_df,
            'timestamp' : timestamp_df,
        }
        df = other_dfs['value']
        for v in self.variables:
            dtype = VTYPES[v.var_type]['dtype_pd']
            df[v.var_label] = df[v.var_label].astype(dtype)
        other_dfs['value'] = df

        for d_label, tdef in (('timestamp', VTYPES['datetime']),
                              ('user', VTYPES['string']),
                              ('comment', VTYPES['string'])):
            for v in self.variables:
                other_dfs[d_label][v.var_label] = \
                    other_dfs[d_label][v.var_label].astype(tdef['dtype_pd'])

        tracking_index = self.import_df(other_dfs)
        self.save_entry(other_dfs)
        return tracking_index

    def save_all_data(self):
        """ WARNING: this can cause conflicts if done concurrently """
        # TODO: admin role + lock?
        self.filesystem.remove_all('data')
        self.data_files[:] = self.save_entry(self.dfs)

    def save_entry(self, dfs):
        entry_rfn = '%d.csv' % uuid1().int
        while self.filesystem.exists(op.join('data', entry_rfn)):
            entry_rfn = '%d.csv' % uuid1().int
        entry_fn = op.join('data', entry_rfn)
        if dfs['value'].shape[0] > 10:
            entry_str = '%d entries' % len(dfs['value'].index)
        else:
            entry_str = 'entry %s' % dfs['value'].index.to_list()
        self.logger.debug('Save %s to %s', entry_str, entry_fn)
        content = json.dumps({k:self.df_to_str(df, k)
                              for k,df in dfs.items()
                              if k != 'validity'})
        self.filesystem.save(entry_fn, content)
        return entry_fn

    def delete_all_entries(self):
        self.notifier.notify('pre_clear_data')
        self.df = self.df.drop(self.df.index)
        self.notifier.notify('cleared_data')

    def refresh(self):
        self.variables.refresh()
        # self.logic.refresh() # TODO
        if self.flag_ds is not None:
            self.flag_ds.refresh()
        if self.note_ds is not None:
            self.note_ds.refresh()
        self._refresh_data()

    def iter_previous(self, tracking_index):
        m_update = (tracking_index.get_level_values('__version_idx__') != 0)
        df = self.dfs['value']
        for eid, vidx, cidx in tracking_index:
            if vidx == 0:
                yield None
            else:
                max_cidx = (df.index[df.index.get_locs((eid, vidx-1))]
                            .get_level_values(2).max())
                yield df.loc[(eid, vidx-1, max_cidx)]

    def on_variable_entry(self, var_store, entry_df):
        iter_changes = zip(var_store.iter_previous(entry_df.index),
                           (r for _,r in entry_df.iterrows()))
        self.process_variable_changes(iter_changes)

    def process_variable_changes(self, changes):
        # ASSUME validation has been done before push
            
        for ichange, (var_old, var_new) in enumerate(changes):

            if ichange == 0:
                # do it before notifications because
                # notifiees can request updated views:
                self.invalidate_cached_views() 
                
            if var_old is not None:
                label_old = var_old['var_label']
                if var_new is not None: # modified variable
                    label_new = var_new['var_label']

                    if label_old != label_new:
                        self.logger.debug('Process change of variable label: '
                                          '%s to %s', label_old, label_new) 
                        for dlabel, df in self.dfs.items():
                            self.dfs[dlabel] = df.rename({label_old : label_new})
                        self.notifier.notify('column_renamed', label_old,
                                             label_new)

                    if var_old['var_type'] != var_new['var_type']:
                        self.logger.debug('Process change of variable type '
                                          'for %s from %s to %s', label_new,
                                          var_old['var_type'],
                                          var_new['var_type']) 

                        dtype_new = VTYPES[var_new['var_type']]['dtype_pd']
                        self.dfs['value'][label_new] = \
                            (self.dfs['value'][label_new].astype(dtype_new))
                        self.notifier.notify('column_values_changed', label_new)

                    if var_old['nullable'] and not var_new['nullable']:
                        self.logger.debug('Process variable %s '
                                          'that becomes nullable ', label_new)
                        nans = pd.isna(self.dfs['value'][label_new])
                        if nans.any():
                            na_fill = VTYPES[var_new['var_new']]['null_value']
                            self.log.warning(('%s becomes nullable but has '
                                              '%d NA values. They will be filled '
                                              'with %s'), label_new, na_fill)
                            for dlabel, df in self.dfs.items():
                                self.dfs[dlabel][label_new] = \
                                    (df[label_new].fillna(na_fill))
                            index_changed = self.dfs['value'].index[nans]
                            self.notifier.notify('values_changed',
                                                 index_changed, label_new)

                    if (not (pd.isna(var_old['index_position']) and
                             pd.isna(var_new['index_position'])) and
                         ( (pd.isna(var_old['index_position']) and
                            not pd.isna(var_new['index_position'])) or
                           (pd.isna(var_new['index_position']) and
                            not pd.isna(var_old['index_position'])) or
                           var_old['index_position'] != var_new['index_position'])
                        ):
                        self.logger.debug('Process change of index position for '
                                          'variable %s, from %s to %s',
                                          label_new, var_old['index_position'],
                                          var_new['index_position'])

                        if pd.isna(var_new['index_position']):
                            self.notifier.notify('head_index_removed',
                                                 label_new)
                        else:
                            self.notifier.notify('head_index_added', label_new)
                    if var_old['is_used'] != var_new['is_used']:
                        if not var_new['is_used']:
                            self.logger.debug('Process variable %s '
                                              'that becomes unused ', label_new)
                            self.notifier.notify('variable_unused',
                                                 label_new)
                        else:
                            self.logger.debug('Process variable %s '
                                              'that becomes used ', label_new)

                            self.notifier.notify('variable_unused',
                                                 label_new)

                    if (not (pd.isna(var_old['column_position']) and
                             pd.isna(var_new['column_position'])) and
                         ( (pd.isna(var_old['column_position']) and
                            not pd.isna(var_new['column_position'])) or
                           (pd.isna(var_new['column_position']) and
                            not pd.isna(var_old['column_position'])) or
                           var_old['column_position']!=var_new['column_position'])
                        ):
                        self.logger.debug('Process change of column position '
                                          'for variable %s, from %s to %s',
                                          label_new, var_old['column_position'],
                                          var_new['column_position'])
                        
                        self.notifier.notify('head_column_position_changed',
                                             label_new,
                                             var_old['column_position'],
                                             var_new['column_position'])
                else: # deleted variable
                    logger.debug('Process deletion of variable %s', label_old)
                    for dlabel, df in self.dfs.items():
                        self.dfs[dlabel] = df.drop(column=[var_old['var_label']])
                    self.notifier.notify('column_removed', var_old['var_label'])
                    self.save_all_data()
            else: # new variable
                vlabel = var_new['var_label']
                self.logger.debug('Process addition of variable %s (type:%s)',
                                  vlabel, var_new['var_type'])
                tdef = VTYPES[var_new['var_type']]
                for d_label, tdef in (('value', VTYPES[var_new['var_type']]),
                                      ('timestamp', VTYPES['datetime']),
                                      ('user', VTYPES['string']),
                                      ('comment', VTYPES['string'])):
                    if d_label != 'value' or var_new['nullable']:
                        fill_value = tdef['na_value']
                    else:
                        fill_value = tdef['null_value']
                    self.dfs[d_label][vlabel] = fill_value
                    self.dfs[d_label][vlabel] = \
                        self.dfs[d_label][vlabel].astype(tdef['dtype_pd'])

                self.notifier.notify('column_added', vlabel)

    def invalidate_cached_views(self):
        self.logger.debug('invalidate cached views')
        for dlabel in DataStore.DATA_LABELS:
            self.head_dfs[dlabel] = None

            # should be cached_views['__validity__']:
            # self.cached_validity[view] = None

            # self.cached_inconsistent_entries = None

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

    def push_variable(self, var_label, var_type, nullable=True,
                      index_position=None, is_unique=False, is_used=True,
                      column_position=None):
        variable = Var(var_label, var_type, nullable=nullable,
                       index_position=index_position, is_unique=is_unique,
                       is_used=is_used, column_position=column_position)
        return self.variables.store.push_record(variable.asdict())

    def invalid_entries(self):
        return []

    def validate_dtypes(self):
        self.logger.debug('Validate dtypes of %s', self.label)

        is_valid = True

        # Validate index in full df
        validate_int = VTYPES['int']['validate_dtype_pd']
        for dlabel, df in self.dfs.items():
            for index_level in DataStore.TRACKING_INDEX_LEVELS:
                dtype = df.index.dtypes[index_level]
                validity = validate_int(dtype)
                if not validity:
                    self.logger.error('Index level %s in %s has invalid '
                                      'dtype: %s', index_level, dtype)
                is_valid &= validity

        # Validate columns in full & head df
        for df in (self.head_df(), self.dfs['value']):
            for variable in self.variables:
                type_def = VTYPES[variable.var_type]
                dtype = df[variable.var_label].dtype
                validity = type_def['validate_dtype_pd'](dtype)
                if not validity:
                    self.logger.error('Column of %s (%s) has invalid '
                                      'dtype: %s', variable.var_label,
                                      variable.var_type, dtype)
                is_valid &= validity

        if self.flag_ds is not None:
            is_valid &= self.flag_ds.validate_dtypes()

        if self.annotation_ds is not None:
            is_valid &= self.annotation_ds.validate_dtypes()

        if self.props_ds is not None:
            is_valid &= self.props_ds.validate_dtypes()

        return is_valid

    def full_df(self, data_label='value'):
        return self.dfs[data_label]

    def empty_df(self):
        df = pd.DataFrame(columns=DataStore.TRACKING_INDEX_LEVELS)
        for col in DataStore.TRACKING_INDEX_LEVELS:
            df[col] = df[col].astype(np.int64)
        return df
        
    def head_df(self, data_label='value'):
        variables = list(self.variables)
        if self.head_dfs[data_label] is None:
            # Recompute cached head views

            # if self.data_is_empty():
            #     hdf = self.empty_df()
            #     for variable in variables:
            #         tdef = VTYPES[variable.var_type]
            #         hdf[variable.var_label] = tdef['na_value']
            #         hdf[variable.var_label] = (hdf[variable.var_label]
            #                                    .astype(tdef['dtype_pd']))
            # else:

            if data_label in self.dfs:
                df = self.dfs[data_label]
            elif data_label == 'validity':
                df = self.validity
            else:
                raise Exception('Uknown data_label %s', data_label)
            hdf = (df.groupby(level=0, group_keys=False)
                   .tail(1).reset_index())

            index_variables = self.variables.indexes()
            if len(index_variables) != 0:
                hdf = (hdf.set_index([v.var_label for v in index_variables])
                       .sort_index())

            self.head_dfs[data_label] = hdf

        hdf = self.head_dfs[data_label]
        order = ([v.var_label
                  for v in chain(sorted((v for v in variables
                                         if (v.index_position is None and
                                             v.column_position is not None)),
                                        key=lambda v: v.column_position),
                                 sorted((v for v in variables
                                         if (v.index_position is None and
                                             v.column_position is None)),
                                         key=lambda v: v.var_label))] +
                 DataStore.TRACKING_INDEX_LEVELS)
        return hdf[order]

class TestDataStore(TestCase):

    def setUp(self):
        self.setUpPyfakefs()
        logger.setLevel(logging.DEBUG)
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

    # TODO test format / unformat for all VTYPES

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

        _check_store(DataStore(ds.filesystem))

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
                         for v in (list(td['corner_cases'].values()) +
                                   ([None] if tl in nullables
                                    else []))]
                        for tl, td in VTYPES.items()]
        ds.push_record([dict(e) for e in product(*combinations)])

        self._check_store(ds, nullables, uniques, indexes, unused)

        def _fv(d):
            return next(iter(d.values()))

        for tlabel in uniques:
            tdef = VTYPES[tlabel]
            self.assertRaises(DuplicateValueError,
                              ds.push_record,
                              {tlabel:_fv(tdef['corner_cases'])})

        # Check store reloading
        ds2 = DataStore(ds.filesystem)
        self._check_store(ds2, nullables, uniques, indexes, unused)
        assert_frame_equal(ds.full_df(), ds2.full_df())

    def __test_data_entry(self):
        self._test_push_data()

    def test_datafile_single_entry_deletion(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(ds.filesystem)

        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx1 = ds1.push_record({'v1' : 'test'})
        tidx2 = ds1.push_record({'v1' : 'other test'})

        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()

        fn1 = ds1.data_file(tidx1)
        self.assertTrue(self.filesystem.exists(fn1))
        assert_frame_equal(full_df1, full_df2)

        ds1.delete_single_entry(tidx1)
        full_df1 = ds1.full_df()
        ds2.refresh()
        full_df2 = ds2.full_df()

        self.assertFalse(tixd1 in full_df1.index)
        self.assertFalse(self.filesystem.exists(fn1))
        assert_frame_equal(full_df1, full_df2)

    def test_datafile_multi_entry_deletion(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(ds1.filesystem)
        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx = ds1.push_record({'v1' : ['test', 'other test']})

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

    def test_main_datafile_modification(self):

        ds1 = DataStore(self.filesystem, 'test_ds')
        ds2 = DataStore(ds1.filesystem)

        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        tidx1 = ds1.push_record({'v1' : 'test'})
        tidx2 = ds1.push_record({'v1' : 'other test'})
        ds2.refresh()

        full_df1 = ds1.full_df()
        fn1 = full_df1.data_file(tidx1)
        fn2 = full_df1.data_file(tidx2)

        ds1.save_all_data()
        self.assertFalse(self.filesystem.exists(fn1))
        self.assertFalse(self.filesystem.exists(fn2))

        main_fn = op.join('test_ds', 'data', 'data_main.csv')
        self.assertEqual(ds1.data_file(tidx1), main_fn)
        self.assertEqual(ds1.data_file(tidx2), main_fn)

        ds2.refresh()
        full_df2 = ds2.full_df()
        self.assertEqual(ds2.data_file(tidx1), main_fn)
        self.assertEqual(ds2.data_file(tidx2), main_fn)

        ds1.delete_single_entry(tidx1) # data_main.csv will be modified
        self.assertFalse(tixd1 in ds1.full_df().index)
        self.assertTrue(self.filesystem.exists(main_fn))

        tidx3 = ds1.push_record({'v1' : 'another test'})
        ds1.save_all_data()

        ds2.refresh()
        full_df2 = ds2.full_df()
        self.assertFalse(tixd1 in full_df2.index)
        self.assertTrue(tixd3 in full_df2.index)

        self.assertEqual(ds2.data_file(tidx2), main_fn)
        self.assertEqual(ds2.data_file(tidx3), main_fn)

    def __test_data_entry_nullable(self):
        # TODO test nullable for all dtypes
        self._test_push_data(nullables=VTYPES.keys())

    def __test_data_entry_unique(self):
        # TODO test unique for all dtypes
        self._test_push_data(uniques=VTYPES.keys())

    def __test_data_entry_index(self):
        for type_label in VTYPES:
            self._test_push_data(indexes=[type_label])

        vtypes = list(VTYPES.keys())
        self._test_push_data(indexes=vtypes[:2])

    def __test_data_entry_unused(self):
        # TODO simpler test for unused variable that becomes used
        for type_label in VTYPES:
            self._test_push_data(unused=[type_label])

    def test_data_push_non_indexed_entry(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_record({'v1' : 'test'})
        tidx = ds.push_record({'v1' : 'other test'})

        t_levels = DataStore.TRACKING_INDEX_LEVELS

        expected = pd.DataFrame({'v1' : ['test', 'other test']})
        expected['v1'] = expected['v1'].astype('string')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected)

        ds.push_record({'v1' : 'other test update'}, tracking_index=tidx)
        expected = pd.DataFrame({'v1' : ['test', 'other test',
                                         'other test update']})
        expected['v1'] = expected['v1'].astype('string')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected)

    def test_data_push_indexed_entry(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_variable('my_index', 'int', index_position=0)
        ds.push_record({'v1' : 'test',
                        'my_index' : 10})

        ds.push_record({'v1' : 'other',
                        'my_index' : 34})
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        expected_df = pd.DataFrame({'v1' : ['test', 'other'],
                                    'my_index' : [10, 34]})
        expected_df.my_index = expected_df.my_index.astype('Int64')
        expected_df.v1 = expected_df.v1.astype('string')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected_df.set_index('my_index'))

        ds.push_record({'v1' : 'updated',
                        'my_index' : 34})

        expected_df = pd.DataFrame({'v1' : ['test', 'updated'],
                                    'my_index' : [10, 34]})
        expected_df.my_index = expected_df.my_index.astype('Int64')
        expected_df.v1 = expected_df.v1.astype('string')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected_df.set_index('my_index'))

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
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        expected = (pd.DataFrame({'pid' : ['CE01'],
                                  'interview' : ['preliminary'],
                                  'age' : [54]}))
        expected[['pid', 'interview']] = \
            expected[['pid', 'interview']].astype('string')
        expected['age'] = expected['age'].astype('Int64')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected.set_index(['pid', 'interview']))

    def test_forbidden_variable_type_change(self):
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

        t_levels = DataStore.TRACKING_INDEX_LEVELS
        expected = pd.DataFrame({'pid' : ['CE01', 'CE02'],
                                          'age' : [55, 33]})
        expected['pid'] = expected['pid'].astype('string')
        expected['age'] = expected['age'].astype('Int64')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected.set_index(['pid']))

        ds.push_variable('pid', 'string', index_position=None)
        expected = pd.DataFrame({'pid' : ['CE01', 'CE02'],
                                 'age' : [55, 33]})
        expected['pid'] = expected['pid'].astype('string')
        expected['age'] = expected['age'].astype('Int64')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected[['age', 'pid']])

        ds.push_record({'pid' : 'CE02', 'age' : 42})
        expected = pd.DataFrame({'pid' : ['CE01', 'CE02', 'CE02'],
                                 'age' : [55, 33, 42]})
        expected['pid'] = expected['pid'].astype('string')
        expected['age'] = expected['age'].astype('Int64')
        assert_frame_equal(ds.head_df().drop(columns=t_levels),
                           expected[['age', 'pid']])

        self.assertRaises(VariableChangeError,
                          ds.push_variable, 'pid', 'string', index_position=0)

    def test_variable_unique_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')
        ds.push_record({'v1' : 'test'})
        ds.push_variable('v1', 'string', is_unique=True)
        
        self.assertRaises(InvalidImport, ds.push_record, {'v1' : 'test'})

        ds.push_variable('v1', 'string', is_unique=False)
        ds.push_record({'v1' : 'test'})
        self.assertRaises(VariableChangeError, ds.push_variable, 'v1', 'string',
                          is_unique=True)

    def test_variable_used_change(self):
        pass

    def test_variable_nullable_change(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string', nullable=False)
        self.assertRaises(InvalidImport, ds.push_record, {'v1' : None})

        ds.push_variable('v1', 'string', nullable=True)
        ds.push_record({'v1' : None})

        self.assertTrue((ds.dfs['validity']=='').all(axis=None))

        self.assertRaises(VariableChangeError, ds.push_variable, 'v1', 'string',
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

        ds2 = DataStore(ds.filesystem)
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
        t_levels = DataStore.TRACKING_INDEX_LEVELS
        self.assertListEqual(list(ds.head_df().drop(columns=t_levels).columns),
                             ['v1', 'v2', 'v3'])

        logger.debug('Reload as ds2')
        ds2 = DataStore(ds.filesystem)
        self.assertListEqual(list(ds2.head_df().drop(columns=t_levels).columns),
                             ['v1', 'v2', 'v3'])

        ds.push_variable('v1', 'string', column_position=3)
        ds.push_variable('v2', 'int', column_position=1)
        ds.push_variable('v3', 'string', column_position=2)
        ds.push_variable('v4', 'string')

        self.assertListEqual(list(ds.head_df().drop(columns=t_levels).columns),
                             ['v2', 'v3', 'v1', 'v4'])

        logger.debug('Refresh ds2')
        ds2.refresh()
        self.assertListEqual(list(ds2.head_df().drop(columns=t_levels).columns),
                             ['v2', 'v3', 'v1', 'v4'])
        
        ds.push_variable('v4', 'string', column_position=2.5)
        self.assertListEqual(list(ds.head_df().drop(columns=t_levels).columns),
                                  ['v2', 'v3', 'v4', 'v1'])
        ds2.refresh()
        self.assertListEqual(list(ds2.head_df().drop(columns=t_levels).columns),
                             ['v2', 'v3', 'v4', 'v1'])

    def test_flag_indexed_head_df(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('vid', 'string', index_position=0)
        ds.push_variable('age', 'int')

        ds.push_flag_def(0, 'to_check', 'triangle_orange')
        ds.push_flag_def(1, 'double_checked', 'tick_mark_green')

        tidx = ds.push_record({'vid' : 'ID1', 'age' : 111})
        ds.push_flag(tidx, 'age', 1) # flag using tracking index
        ds.push_flag('ID1', 'age', 1<<2) # flag using head index

        symbols_full_df = ds.full_df('single_flag_symbols')
        self.assertListEqual(symbols_full_df.loc[tidx, 'age'],
                             ['double_checked'])

        symbols_head_df = ds.head_df('single_flag_symbols')
        self.assertListEqual(symbols_head_df.loc['ID1', 'age'],
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
        self.assertRaises(InvalidFlagIndex, ds.push_flag_def,
                          flag_index=65, flag_label='f',
                          flag_symbol='triangle_orange')

        tidx1 = ds.push_record({'v1' : 'has flags'}),
        ds.flag(tidx1, 'v1', 1<<1)
        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assertSequenceEqual(single_flag_symbols_df.loc[tidx1, 'v1'],
                                 ['dummy'])

        ds.push_flag_def(1, 'error', 'cross_red')

        single_flag_symbols_df = ds.full_df('single_flag_symbols')
        self.assert_equal(single_flag_symbols_df.loc[tidx1, 'v1'],
                          ['cross_red'])

    def test_many_flags(self):
        ds = DataStore(self.filesystem, 'test_ds')
        ds.set_user('me')
        ds.push_variable('v1', 'string')

        ds.push_flag_def(0, 'to_check', 'triangle_orange')
        ds.push_flag_def(1, 'dummy', 'question_mark')
        ds.push_flag_def(2, 'double_checked', 'tick_mark_green')
    
        tidx = ds.push_record([{'v1' : 'has flags'},
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

        ds.push_flag_def(0, 'to_check', 'triangle_orange')
        ds.push_flag_def(1, 'dummy', 'question_mark')
        ds.push_flag_def(2, 'double_checked', 'tick_mark_green')

        ds.flag('id1', 'v1', 1<<1)
        self.assertSequenceEqual(ds.flags_of('id1', 'v1'),
                                 [1])

        ds.flag('id1', 'v1', 1 | (1<<1))
        self.assertSequenceEqual(ds.flags_of('id1', 'v1'),
                                 [0, 1])
        
    def __test_refresh(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds1.set_user('me')

        ds2 = DataStore(ds1.filesystem)

        ds1.push_variable('v1', 'string')
        ds2.refresh()
        self.assertSequenceEqual(list(ds2.variables), [Var('v1', 'string')])

        ds1.push_record({'v1' : 'first_val'})
        ds2.refresh()
        assert_frame_equal(ds2.head_df()
                           .drop(columns=DataStore.TRACKING_INDEX_LEVELS),
                           pd.DataFrame({'v1' : ['first_val']}))

        ds1.push_flag_def(0, 'to_check', 'triangle_orange')

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
        
        ds1 = DataStore(self.filesystem, 'test_ds', log_label='DS1')
        ds1.set_user('me')
        ds1.push_variable('v1', 'string')
        idx1 = ds1.push_record({'v1' : 'orig'})

        ds2 = DataStore(ds1.filesystem, log_label='DS2')

        idx2 = ds1.push_record({'v1' : 'update from ds1'},
                               tracking_index=idx1)
        idx3 = ds2.push_record({'v1' : 'conflicting update from ds2'},
                               tracking_index=idx1)

        ds1.refresh()
        ds2.refresh()

        idx2_cft = (idx2[0][0], idx2[0][1], 1)
        self.assertEqual('conflicting', ds1.dfs['validity'].loc[idx2_cft, 'v1'])
        idx3_cft = (idx3[0][0], idx3[0][1], 2)
        self.assertEqual('conflicting', ds2.dfs['validity'].loc[idx3_cft, 'v1'])

    def test_conflict_unique(self):
        ds1 = DataStore(self.filesystem, 'test_ds')
        ds1.set_user('me')
        ds1.push_variable('v1', 'string', is_unique=True)

        logger.debug('utest: reload as ds2')
        ds2 = DataStore(ds1.filesystem)

        idx1 = ds1.push_record({'v1' : 'test'})
        idx2 = ds2.push_record({'v1' : 'test'})

        logger.debug('utest: refresh ds1')
        ds1.refresh()
        logger.debug('utest: refresh ds2')
        ds2.refresh()

        self.assertEqual('non-unique', ds1.dfs['validity'].loc[idx1, 'v1'].iat[0])
        self.assertEqual('non-unique', ds2.dfs['validity'].loc[idx2, 'v1'].iat[0])

    def test_user_view(self):
        # Any cell of head where user name is in value
        pass

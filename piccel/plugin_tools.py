# -*- coding: utf-8 -*-
import logging
import re
from datetime import date, datetime, timedelta, time

import numpy as np
import pandas as pd

from .sheet_plugin import SheetPlugin
from .core import df_filter_from_dict, if_none, SheetNotFound, Hint, Hints
from .form import Form

logger = logging.getLogger('piccel')

DATE_FMT = '%Y-%m-%d'
DATETIME_FMT = '%Y-%m-%d %H:%M:%S'
DEFAULT_INTERVIEW_PLAN_SHEET_LABEL = 'Interview_Plan'

test_participant_ID_re = re.compile(".+[^0-9]9[0-9]+$")

class DataDefinitionError(Exception): pass
class ColumnsNotFound(Exception): pass

class LescaDashboard(SheetPlugin):
    def __init__(self, sheet):
        super(LescaDashboard, self).__init__(sheet)
        self.df = None
        self.progress_notes_sheets = []

    def sheets_to_watch(self):
        to_watch = ['Participants_Status']
        for sheet_label in ['Progress_Notes_Common', 'Progress_Notes']:
            if self.workbook.has_sheet(sheet_label):
                to_watch.append(sheet_label)
                self.progress_notes_sheets.append(sheet_label)
        return super(LescaDashboard, self).sheets_to_watch() + to_watch

    def after_workbook_load(self):
        # TODO: utest proper status tracking scenarios
        # with multiple progress note sheets
        super().after_workbook_load()
        self.init()

    def init(self):
        if not self.update_watched_sheets():
            return

        pg_sheet_label = self.progress_notes_sheets[0]
        logger.info('Tracking of participant status watches %s '\
                    'to get drop events', pg_sheet_label)
        self.status_tracker = ParticipantStatusTracker('Participants_Status',
                                                       pg_sheet_label,
                                                       self.workbook)

        self.pp = self.workbook['Participants_Status']
        self.df = pd.DataFrame()

        for sheet_label in self.sheets_to_watch():
            logger.debug('Check Participant_ID in sheet %s', sheet_label)
            if not (self.workbook[sheet_label].form_master
                    .has_key('Participant_ID')):
                raise DataDefinitionError('Participant_ID not found in '\
                                          'keys of sheet %s' % sheet_label)

        self.reset_data()

    def reset_data(self):
        if self.pp.df is not None and self.pp.df.shape[0] > 0:
            self.df = (self.pp.get_df_view('latest_active')[['Participant_ID']]
                       .sort_values(by='Participant_ID')
                       .reset_index(drop=True))
            self.df.set_index('Participant_ID', inplace=True)
            self.refresh_entries(self.df.index)
        else:
            self.df = (pd.DataFrame(columns=['Participant_ID'])
                       .set_index('Participant_ID'))
        logger.debug('LescaDashboard.reset_data - df: %s', self.df.shape)
        self.sheet.invalidate_cached_views()

    def show_index_in_ui(self):
        return True

    def get_full_view(self, df):
        return self.df

    def views(self, base_views):
        return {'full' : self.get_full_view}

    def default_view(self):
        return 'full'

    def update(self, sheet_source, entry_df, deletion=False, clear=False):
        logger.debug('Lesca Dashboard update from sheet %s', sheet_source.label)

        if self.df is None:
            logger.debug('df is none... call init')
            self.init()
            return # self.df initialized only after full load of workbook
                   # cannot do much here anyway...

        logger.debug('df.shape: %s', self.df.shape)

        if sheet_source.label == self.pp.label:
            if clear:
                self.df = (pd.DataFrame(columns=['Participant_ID'])
                           .set_index('Participant_ID'))
                self.sheet.invalidate_cached_views()
                self.sheet.notifier.notify('cleared_data')
                return
            if deletion:
                deleted_pid = entry_df.Participant_ID.iat[0]
                self.sheet.notifier.notify('pre_delete_entry',
                                           entry_id=deleted_pid)
                self.df.drop(index=deleted_pid, inplace=True)
                self.sheet.invalidate_cached_views()
                self.sheet.notifier.notify('deleted_entry', entry_df=entry_df)
                return

        if clear or deletion: # Should not happen very often, only when maintenance
            # Refresh all:
            self.refresh_entries(self.df.index)
            self.sheet.invalidate_cached_views()
            self.sheet.notifier.notify('cleared_data')
            return

        entry_df = entry_df.set_index('Participant_ID')

        if sheet_source.label == self.pp.label and \
           entry_df.index[0] not in self.df.index:
            # New participant
            empty_df = pd.DataFrame([], index=entry_df.index)
            self.df = self.df.append(empty_df)
            self.df.sort_index(inplace=True)
            self.sheet.invalidate_cached_views()
            self.sheet.notifier.notify('appended_entry', empty_df)
        if entry_df.index[0] in self.df.index:
            self.refresh_entries(entry_df.index)
            self.sheet.invalidate_cached_views()
            self.sheet.notifier.notify('entry_set',
                                       entry_idx=entry_df.index[0])
        else:
            logger.warning('Update plugin of sheet %s: '\
                           'udpated entry from %s with id=%s is not in index',
                           self.sheet.label, sheet_source.label,
                           entry_df.index[0])

    def refresh_entries(self, pids):
        logger.debug('Common Lesca Dashboard refresh for: %s', pids)

        # Reset all values to empty string
        cols_to_clear = [c for c in self.df.columns if c != 'Participant_ID']
        self.df.loc[pids, cols_to_clear] = ''

        self.status_tracker.track(self.df, pids)
        for progress_notes_sheet_label in self.progress_notes_sheets:
            self.df.loc[pids, progress_notes_sheet_label] = 'add_note'

        # Filter drop-outs
        df_selected = self.df.loc[pids]
        mask_drops = df_selected['Study_Status'] != 'drop_out'
        pids = set(pids).intersection(df_selected[mask_drops].index)

        return pids

    def action(self, entry_df, selected_column):
        result, result_label = None, None
        participant_id = entry_df.index[0]
        logger.debug('action_lesca for %s, col %s' % \
                     (participant_id, selected_column))
        if selected_column.startswith('Progress_Notes'):
            if selected_column == 'Progress_Notes_Common':
                pn_sheet_label = 'Progress_Notes_Common' # project PN
            else:
                pn_sheet_label = 'Progress_Notes' # workbook-specific PN
            result, result_label = form_new(pn_sheet_label, self.workbook,
                                            entry_dict={'Participant_ID' :
                                                        participant_id})
        elif selected_column == 'Participant_ID':
            result_label = 'Progress Notes %s' % participant_id
            result = self.collect_progress_notes(participant_id,
                                                 self.progress_note_extractions())
        elif selected_column == 'Study_Status':
            pkeys = {'Participant_ID' : participant_id}
            result, result_label = form_update_or_new('Participants_Status',
                                                      self.workbook,
                                                      primary_keys=pkeys)

        if result is not None and isinstance(result, Form):
            form = result
            section0 = form[form.first_section()]
            if section0.has_key('Participant_ID'):
                section0['Participant_ID'].set_editable(False)

        return result, result_label

    def progress_note_extractions(self):
        # TODO: handle language translations in Report?
        return [
            {'sheet_label' : 'Progress_Notes_Common',
             'context' : 'Général',
             'short_values' : ['Note_Type', 'Event_Date'],
             'long_texts' : {'Détails' : "Description"},
            },
            {'sheet_label' : 'Progress_Notes',
             'context' : 'Général',
             'short_values' : ['Note_Type', 'Event_Date'],
             'long_texts' : {'Détails' : "Description"},
            },
        ]

    def collect_progress_notes(self, pid, extractions):
        """
        extractions is a list of dict, each defining how to extract a progress note
        entry
        """
        pnotes = ParticipantProgressNotes(pid, datetime.now().strftime(DATETIME_FMT))
        for extraction in extractions:
            sheet_label = extraction['sheet_label']
            if not self.workbook.has_sheet(sheet_label):
                continue

            sheet_df = self.workbook[sheet_label].latest_update_df()
            selected_df = sheet_df[sheet_df.Participant_ID==pid]
            if selected_df.shape[0] == 0:
                continue


                # if not (pd.isna(text) or text == NA_STRING):
                #     long_texts.append((title, text))

            def if_na(v, default):
                if pd.isna(v):
                    return default
                return v

            short_values = extraction.get('short_values',[])
            missing = set(short_values).difference(selected_df.columns)
            if len(missing) > 0:
                raise ColumnsNotFound(missing)
            for _, row in selected_df.iterrows():
                long_texts = []
                for title, column in extraction.get('long_texts', {}).items():
                    long_texts.append((title, if_na(row[column], 'Non renseigné')))
                pnotes.add(ProgressNoteEntry(row.Timestamp_Submission,
                                             row.get('User', 'na'),
                                             extraction['context'],
                                             row[short_values],
                                             long_texts))
        return pnotes.to_report()

    def hint(self, column, value):
        if pd.isna(value):
            return None

        if column=='Study_Status':
            if value.startswith('confirm'):
                return Hints.QUESTION
            elif value == "study_over":
                return Hints.COMPLETED
            elif value == "drop_out":
                return Hints.IGNORED
        elif column=='Participant_ID' and \
             test_participant_ID_re.match(value) is not None:
                return Hints.TEST
        else:
            if value.lower().endswith('fail'):
                return Hints.IGNORED

import copy
from bs4 import BeautifulSoup

from .ui.main_qss import progress_note_report_style

class Report:
    def __init__(self, content, header=None, footer=None):
        self.content = content
        self.header = header
        self.footer = footer

class ParticipantProgressNotes:

    def __init__(self, participant_id, update_date_str):
        self.participant_id = participant_id
        self.update_date = update_date_str
        self.progress_notes = []

    def add(self, entry):
        self.progress_notes.append(entry)

    def to_report(self, title_pat='{Participant_ID}'):
        header_text = title_pat.format(Participant_ID=self.participant_id)

        pgs_soup = BeautifulSoup('<style type="text/css">%s</style>'\
                                 '<div id="content"></div>' %
                                 progress_note_report_style)
        for pn in reversed(sorted(self.progress_notes,
                                  key=lambda p: p.get_timestamp())):
            pn.append_soup(pgs_soup)

        footer_text = 'Report generated on %s' % self.update_date

        return Report(pgs_soup.prettify(), header_text, footer_text)

class ProgressNoteEntry:

    PG_HTML = \
"""
<p>
 <table>
  <tr class="report_odd_row">
   <th>Context:</th>
   <td>{context}</td>
  </tr>
  <tr>
   <th>Timestamp:</th>
   <td>{timestamp}</td>
  </tr>
  <tr class="report_odd_row">
   <th>Staff:</th>
   <td>{staff}</td>
  </tr>
 </table>
</p>
"""
    def __init__(self, timestamp, staff, context, short_values, long_texts):
        self.timestamp = timestamp
        self.staff = staff
        self.context = context
        self.short_values = short_values
        self.long_texts = long_texts

    def get_timestamp(self):
        return self.timestamp

    def append_soup(self, main_soup):
        ts_str = self.timestamp.strftime(DATETIME_FMT)

        def _append_key_val_row(_table, key, val, odd_row):
            tr = main_soup.new_tag('tr')
            _table.append(tr)
            if odd_row:
                tr['class'] = "report_odd_row"
            th = main_soup.new_tag('th')
            th.string = '%s' % key
            tr.append(th)
            td = main_soup.new_tag('td')
            if isinstance(val, datetime):
                val = val.strftime(DATETIME_FMT)
            elif isinstance(val, date):
                val = val.strftime(DATE_FMT)

            td.string = '%s' % val
            tr.append(td)

        soup = BeautifulSoup()
        ptag = main_soup.new_tag('p')
        soup.body.append(ptag)
        table = main_soup.new_tag('table')
        ptag.append(table)
        for irow, (key, val) in enumerate([('Context', self.context),
                                           ('Timestamp', ts_str),
                                           ('Staff', self.staff)]):
            _append_key_val_row(table, key, val, irow % 2 == 0)


        if len(self.short_values) > 0:
            _append_key_val_row(table, '', '', False)
            for irow, (k,v) in enumerate(self.short_values.items()):
                _append_key_val_row(table, k, v, irow % 2 == 0)

        for title, text in self.long_texts:
            htag = main_soup.new_tag('h4')
            htag.string = title
            soup.body.append(htag)

            ptag = main_soup.new_tag('p')
            ptag.string = text
            soup.body.append(ptag)

        soup.append(main_soup.new_tag('hr'))
        main_soup.find(id='content').append(soup)

class InconsistentIndex(Exception): pass

class Operation:
    def __init__(self, *args):
        self.items = args
class And(Operation): pass
class Or(Operation): pass

def conditional_set(df, column, value, other_df, other_col, other_values,
                    indexes):
    # TODO: add a lot of error catching and clear feedback
    if df.index.name != other_df.index.name:
        raise InconsistentIndex('Index of df (%s) is not the same as '\
                                'other_df (%s)' % (df.index.name,
                                                   other_df.index.name))

    other_mask = other_df[other_col].isin(other_values)
    other_selection = other_df[other_mask]
    extra = other_selection.index.difference(df.index)
    if len(extra) > 0:
        logger.warning('Index values in other but not in df: %s',
                       ', '.join(['%s' % e for e in extra]))
    # TODO: check that all index values in other mask are in df.index
    if indexes is not None:
        index_to_set = other_selection.index.intersection(indexes)
    else:
        index_to_set = other_selection.index
    df.loc[index_to_set, column] = value

def map_set(dest_df, dest_column, conditions):
    for dest_value, condition in conditions.items():
        logger.debug('MapSet of dest value = %s', dest_value)
        selector = IndexMatcher(condition)
        if dest_df.index.name != selector.index_name:
            raise InconsistentIndex('Inconsistent index: destination is "%s" '\
                                    'and selection is "%s"' % \
                                    (dest_df.index.name, selector.index_name))
        extra = selector.index.difference(dest_df.index)
        if len(extra) > 0:
            logger.warning('Index values in source df but not in selection: %s',
                           ', '.join(['%s' % e for e in extra]))
        if dest_column not in dest_df.columns:
            raise DestColumnNotFound(dest_column)

        # if isintance(dest_value)
        # TODO: format dest_value if str

        logger.debug('MapSet set %s in column %s for %s',
                     dest_value, dest_column, selector.index)
        dest_df.loc[selector.index, dest_column] = dest_value

def set_intersection(s, s_other):
    s.intersection_update(s_other)

def set_union(s, s_other):
    s.update(s_other)

class IndexMatcher:

    def __init__(self, match_def):
        # TODO: make a function
        self.index = set()

        if not isinstance(match_def, (And, Or)):
            match_def = Or(match_def)

        self.index_name = match_def.items[0][0].index.name

        if isinstance(match_def, And):
            combine_sets = set_intersection
        else:
            combine_sets = set_union

        if any(md[0].index.name != self.index_name for md in match_def.items):
            logger.warning('Index names in index matcher not consistent')

        self.index.update(filter_indexes(match_def.items[0]))
        for filter_def in match_def.items[1:]:
            if combine_sets == set_intersection and len(self.index)==0:
                break

            combine_sets(self.index, filter_indexes(filter_def))

class Comparator:
    def __init__(self, value=None):
        self._value = value

    def value(self, src_df, src_col):
        if callable(self._value):
            return self._value(src_df, src_col)
        else:
            return self._value

class NotIn(Comparator):
    def __init__(self, value):
        super(NotIn, self).__init__(value)
        assert(isinstance(value, list))

class IsNotNA(Comparator): pass
class IsNA(Comparator): pass
class Lower(Comparator): pass
class LowerEqual(Comparator): pass
class Greater(Comparator): pass
class GreaterEqual(Comparator): pass
class Any(Comparator): pass

class SrcColumnNotFound(Exception):
    def __init__(self, message):
        super(SrcColumnNotFound, self).__init__(message)
        self.message = message

class DestColumnNotFound(Exception):
    def __init__(self, message):
        super(SrcColumnNotFound, self).__init__(message)
        self.message = message

def filter_indexes(filter_def):

    src_df, src_col, predicate_def = filter_def

    if src_col not in src_df.columns:
        raise SrcColumnNotFound(src_col)

    if not callable(predicate_def):
        if not isinstance(predicate_def, list):
            predicate_value = predicate_def.value(src_df, src_col)
        else:
            predicate_value = predicate_def

    if isinstance(predicate_def, list):
        mask = lambda src_df, src_col: src_df[src_col].isin(predicate_value)
    elif isinstance(predicate_def, Any):
        mask = lambda src_df, src_col: src_df[src_col].apply(lambda x: True)
    elif isinstance(predicate_def, NotIn):
        mask = lambda src_df, src_col: ~src_df[src_col].isin(predicate_value)
    elif isinstance(predicate_def, Lower):
        mask = lambda src_df, src_col: src_df[src_col] < predicate_value
    elif isinstance(predicate_def, LowerEqual):
        mask = lambda src_df, src_col: src_df[src_col] <= predicate_value
    elif isinstance(predicate_def, Greater):
        mask = lambda src_df, src_col: src_df[src_col] > predicate_value
    elif isinstance(predicate_def, GreaterEqual):
        mask = lambda src_df, src_col: src_df[src_col] >= predicate_value
    elif isinstance(predicate_def, IsNotNA):
        mask = lambda src_df, src_col: ~pd.isna(src_df[src_col])
    elif isinstance(predicate_def, IsNA):
        mask = lambda src_df, src_col: pd.isna(src_df[src_col])
    elif callable(predicate_def):
        mask = predicate_def()
    else:
        raise Exception('Invalid predicate_def %s' % predicate_def)

    return src_df[mask(src_df, src_col)].index

def form_new(sheet_label, workbook, entry_dict=None):
    entry_dict = {} if entry_dict is None else entry_dict
    sheet = workbook[sheet_label]
    form = sheet.form_new_entry()
    form.set_values_from_entry(entry_dict)
    action_label = '%s | New' % sheet_label
    return form, action_label

def form_update_or_new(sheet_label, workbook, primary_keys, entry_dict=None):
    primary_keys = {} if primary_keys is None else primary_keys
    entry_dict = {} if entry_dict is None else entry_dict

    sheet = workbook[sheet_label]
    entry_index = sheet.df_index_from_value(primary_keys, view='latest')
    if len(entry_index) == 0:
        form = sheet.form_new_entry()
        form.set_values_from_entry(primary_keys)
        action_label = '%s | New' % sheet_label
    else:
        if len(entry_index) > 1:
            logger.warning('Multiple entries matching %s: %s',
                           primary_keys, entry_index)
        form = sheet.form_update_entry(entry_index[-1])
        action_label = '%s | Update' % sheet_label
    form.set_values_from_entry(entry_dict)
    return form, action_label

def dashboard_error_if_none(df, dashboard_df, column, error):
    if df is None:
        dashboard_df.loc[:, column] = pd.NA
        dashboard_df.iloc[0, dashboard_df.columns.get_loc(column)] = error
        return True
    return False

class ParticipantStatusTracker:
    def __init__(self, participant_sheet_label, progress_notes_sheet_label,
                 workbook, dashboard_column_status='Study_Status'):
        self.participant_sheet_label = participant_sheet_label
        self.progress_notes_sheet_label = progress_notes_sheet_label
        self.workbook = workbook
        self.dashboard_column_status = dashboard_column_status

        errors = self.check()
        if len(errors) > 0:
            for error in errors:
                logger.error(error)
            raise DataConsistencyError(errors)

    def check(self):
        expected_fields = {
            'Participant_ID' : 'text',
            'Study_Status' : Choice('text', ['inactive']),
            'User' : 'user_name',
            'Timestamp_Submission' : 'datetime'
        }
        errors = check_sheet(self.workbook, self.participant_sheet_label,
                             expected_fields=expected_fields)
        expected_fields = {
            'Participant_ID' : 'text',
            'Note_Type' : Choice('text', ['withdrawal', 'exclusion']),
            'User' : 'user_name',
            'Timestamp_Submission' : 'datetime'
        }
        errors.extend(check_sheet(self.workbook, self.progress_notes_sheet_label,
                                  expected_fields=expected_fields))
        return errors

    def action(self, entry_df, selected_column):
        participant_id = entry_df.index[0]
        return form_update_or_new(self.participant_sheet_label, self.workbook,
                                  {'Participant_ID' : participant_id})

    def track(self, dashboard_df, pids):
        """
        If progress note with drop status is more recent than latest entry in
        participant_status_sheet -> confirm_drop
        Else: Display current participant status in participant_status_sheet
        """
        # dashboard_df.loc[:, self.dashboard_column_status] = 'error'

        pnotes_df = latest_sheet_data(self.workbook,
                                      self.progress_notes_sheet_label,
                                      filter_dict={'Participant_ID' : list(pids)})

        # Keep only drop-related progress notes:
        mask_drop = pnotes_df.Note_Type.isin(['withdrawal', 'exclusion'])
        pns_drop_df = pnotes_df[mask_drop]

        # In case there have been multi drop-related pnotes for a given subject,
        # keep on the most recent one:
        pns_drop_df = ts_data_latest_by_pid(pns_drop_df)

        if dashboard_error_if_none(pns_drop_df, dashboard_df,
                                   self.dashboard_column_status,
                                   'error %s' % self.progress_notes_sheet_label):
            return

        status_df = latest_sheet_data(self.workbook,
                                      self.participant_sheet_label,
                                      view='latest_active',
                                      index_column='Participant_ID',
                                      indexes=pids)
        if dashboard_error_if_none(status_df, dashboard_df,
                                   self.dashboard_column_status,
                                   'error %s' % self.participant_sheet_label):
            return


        pns_drop_fresher, status_fresher = df_keep_higher(pns_drop_df, status_df)

        dashboard_df.loc[status_fresher.index, self.dashboard_column_status] = \
            status_fresher.loc[:, 'Study_Status']

        dashboard_df.loc[pns_drop_fresher.index, self.dashboard_column_status] = \
            'confirm_drop'

class PollTracker:
    def __init__(self, poll_sheet_label, workbook, default_status,
                 dashboard_column=None, poll_answer_column=None,
                 answered_tag='answered'):
        self.poll_sheet_label = poll_sheet_label
        self.workbook = workbook
        self.dashboard_column = if_none(dashboard_column, poll_sheet_label)
        self.poll_answer_column = poll_answer_column
        self.answered_tag = answered_tag
        self.default_status = default_status

    def check(self):
        # TODO insure that poll_answer_column is in fields
        #      (field can have any type)
        return check_sheet(self.workbook, self.interview_label,
                           expected_fields={'Participant_ID' : 'text'})

    def track(self, dashboard_df, pids, poll_filter=None):
        poll_df = latest_sheet_data(self.workbook, self.poll_sheet_label,
                                    index_column='Participant_ID',
                                    filter_dict=poll_filter,
                                    indexes=pids)
        if dashboard_error_if_none(poll_df, dashboard_df,
                                   self.dashboard_column,
                                   'error %s' % self.poll_sheet_label):
            return

        dashboard_df.loc[pids, self.dashboard_column] = self.default_status
        if poll_df.shape[0] > 0:
            if self.poll_answer_column is not None:
                answered_df = poll_df[~pd.isna(poll_df[self.poll_answer_column])]
                dashboard_df.loc[answered_df.index, self.dashboard_column] = \
                    answered_df[self.poll_answer_column]
            else:
                dashboard_df.loc[poll_df.index, self.dashboard_column] = \
                    self.answered_tag

def filter_pids(df, pids, column, sheet_label=None, workbook=None,
                not_equal=None, equal=None):

    if sheet_label is not None:
        df_selected = latest_sheet_data(workbook, sheet_label,
                                        index_column='Participant_ID',
                                        indexes=pids)
    else:
        df_selected = df.loc[pids]

    mask = pd.Series(np.ones(df_selected.shape[0], dtype=bool),
                     index=df_selected.index)

    if not_equal is not None:
        mask &= df_selected[column] != not_equal

    if equal is not None:
        mask &= df_selected[column] == equal

    return set(pids).intersection(df_selected[mask].index)

def conditional_tag(dest_df, pids, dest_column, tag, workbook,
                    source_sheet_label, source_column, source_values):
    source_df = latest_sheet_data(workbook, source_sheet_label,
                                  index_column='Participant_ID',
                                  indexes=pids)

    if (dashboard_error_if_none(source_df, dest_df, dest_column,
                                'error') or
        source_df.shape[0]==0):
        return

    map_set(dest_df, dest_column,
            {tag : (source_df, source_column, source_values)})


def ___track_emailled_poll(dashboard_df, poll_label, email_sheet_label,
                        workbook, pids, date_now=None):
    poll_tag = poll_label.lower()
    default_status = ('%s_to_send' % poll_tag)
    column_status = poll_label

    if column_status not in dashboard_df.columns:
        dashboard_df[column_status] = pd.NA

    date_now = date_now if date_now is not None else datetime.now()

    pids = set(pids).intersection(dashboard_df.index)

    email_df = latest_sheet_data(workbook, email_sheet_label,
                                 filter_dict={'Email_Template' : poll_label},
                                 index_column='Participant_ID', indexes=pids)

    # expected_columns=['Participant_ID',
    #                   'Timestamp_Submission'],
    poll_df = latest_sheet_data(workbook, poll_label,
                                index_column='Participant_ID', indexes=pids)

    dashboard_df.loc[pids, column_status] = default_status

    if email_df.shape[0] > 0:
        try:
            def od_ts(email_df, email_col):
                f_ts = lambda x: date_now - timedelta(days=x)
                return email_df['Overdue_Days'].apply(f_ts)

            map_set(dashboard_df, column_status,
                    conditions={
                        '%s_cancelled' % poll_tag:
                        (email_df, 'Email_Action', ['cancelled']),
                        '%s_email_pending' % poll_tag:
                        And((email_df, 'Email_Action', ['plan']),
                            (email_df, 'Email_Status', ['to_send'])),
                        '%s_email_sent' % poll_tag:
                        And((email_df, 'Email_Action', ['plan']),
                            (email_df, 'Email_Status', ['sent']),
                            (email_df, 'Overdue_Days', IsNotNA()),
                            (email_df, 'Timestamp_Submission',
                             GreaterEqual(od_ts))),
                        '%s_overdue' % poll_tag:
                        And((email_df, 'Email_Action', ['plan']),
                            (email_df, 'Email_Status', ['sent']),
                            (email_df, 'Overdue_Days', IsNotNA()),
                            (email_df, 'Timestamp_Submission', Lower(od_ts))),
                        '%s_email_error' % poll_tag:
                        And((email_df, 'Email_Action', ['plan']),
                            (email_df, 'Email_Status', ['error'])),
                    })
        except SrcColumnNotFound as e:
            msg = 'Column %s not found in df of sheet %s' % \
                (e.message, email_sheet_label)
            raise SrcColumnNotFound(msg) from e
        except DestColumnNotFound as e:
            msg = 'Column %s not found in dashboard df' % e.message
            raise DestColumnNotFound(msg) from e

    if poll_df.shape[0] > 0:
        try:
            map_set(dashboard_df, column_status,
                    conditions={'%s_answered' % poll_tag:
                                (poll_df, 'Timestamp_Submission', Any())})
        except SrcColumnNotFound as e:
            msg = 'Column %s not found in df of sheet %s' % \
                (e.message, poll_label)
            raise SrcColumnNotFound(msg) from e
        except DestColumnNotFound as e:
            msg = 'Column %s not found in dashboard df' % e.message
            raise DestColumnNotFound(msg) from e

def interview_action_old(entry_df, interview_column, workbook,
                         plan_sheet_label=DEFAULT_INTERVIEW_PLAN_SHEET_LABEL):

    value = entry_df[interview_column].iat[0]
    if value=='' or pd.isna(value) or value is None:
        return None, ''

    participant_id = entry_df.index[0]
    form = None
    action_label = ''
    plan_sheet = workbook[plan_sheet_label]

    if interview_column.endswith('_Plan'):
        interview_label = interview_column[:-len('_Plan')]
        return form_update_or_new(plan_sheet_label, workbook,
                                  {'Participant_ID' : participant_id,
                                   'Interview_Type' : interview_label},
                                  {'Plan_Action' : 'plan',
                                   'Send_Email' : True,
                                   'Email_Schedule' : 'days_before_2',
                                   'Email_Template' : interview_label})
        # if value.endswith('_not_done') or value.endswith('_cancelled'):
        # elif value.endswith('_scheduled') or value.endswith('_email_pending') or \
        #  value.endswith('_email_sent') or value.endswith('_email_error') or \
        #  value.endswith('_ok') or value.endswith('_redo'):
    elif interview_column.endswith('_Staff'):
        interview_label = interview_column[:-len('_Staff')]
        return form_update_or_new(plan_sheet_label, workbook,
                                  {'Participant_ID' : participant_id,
                                   'Interview_Type' : interview_label},
                                  {'Plan_Action' : 'assign_staff',
                                   'Send_Email' : False})
    else:
        interview_label = interview_column
        interview_sheet = workbook[interview_label]
        interview_df = interview_sheet.get_df_view('latest')
        selection = (interview_df[interview_df.Participant_ID == participant_id] \
                     if interview_df is not None else pd.DataFrame([]))
        if selection.shape[0] == 0:
            form = interview_sheet.form_new_entry()
            form.set_values_from_entry({'Participant_ID' : participant_id})
            action_label = '%s | New' % interview_sheet.label
        else:
            assert(selection.shape[0] == 1)
            form = interview_sheet.form_update_entry(selection.index[0])
            action_label = '%s | Update' % interview_sheet.label
        form.set_values_from_entry({
            'Session_Action' : 'do_session',
            'Staff' : interview_sheet.user
        })
    return form, action_label

def latest_sheet_data(workbook, sheet_label, view='latest', filter_dict=None,
                      index_column=None, indexes=None):
    df = workbook[sheet_label].get_df_view(view)

    if df is None:
        return None

    if df.shape[0] > 0 and filter_dict is not None:
        df = df_filter_from_dict(df, filter_dict)

    if index_column is not None:
        df = df.set_index(index_column)
        if not df.index.is_unique:
            logger.warning('Index of latest data from sheet %s is not unique',
                           sheet_label)
    if df.shape[0] > 0 and indexes is not None:
        df = df.loc[indexes.intersection(df.index)]

    return df

def df_keep_higher(df1, df2, compare_column='Timestamp_Submission'):
    common_index = df1.index.intersection(df2.index)
    mask = (df1.loc[common_index, compare_column] > \
            df2.loc[common_index, compare_column])
    mask = mask[mask]
    index1_more_recent = df1.loc[mask.index].index
    index2_more_recent = common_index.difference(index1_more_recent)

    index1 = index1_more_recent.union(df1.index.difference(common_index))
    index2 = index2_more_recent.union(df2.index.difference(common_index))
    return df1.loc[index1], df2.loc[index2]

class DataConsistencyError(Exception): pass

class Choice:
    def __init__(self, vtype, choices):
        self.vtype = vtype
        self.choices = choices

def check_sheet(workbook, sheet_label, expected_fields=None):

    errors = []
    expected_fields = if_none(expected_fields, {})
    expected_columns = set(expected_fields.keys())
    try:
        sheet = workbook[sheet_label]
    except SheetNotFound:
        return ['Sheet %s not found' % sheet_label]
    # missing_columns = ', '.join(sorted(expected_columns
    #                                    .difference(sheet.df.columns)))
    # if len(missing_columns) > 0:
    #     errors.append('Missing columns in sheet %s: %s' % \
    #                   (sheet_label, missing_columns))

    form_master = sheet.form_master
    form_fields = form_master.get_vtypes()
    fields_choices = form_master.get_vchoices()
    # missing_fields = ', '.join(sorted(set(expected_columns)
    #                                   .difference(form_fields.keys())))
    # if len(missing_fields) > 0:
    #     errors.append('Missing fields in form of sheet %s: %s' % \
    #                   (sheet_label, missing_fields))
    for field_name, expected_type in expected_fields.items():
        if field_name not in form_fields:
            errors.append('Missing field %s in form of sheet %s' % \
                          (field_name, sheet_label))
        elif not isinstance(expected_type, Choice):
            if form_fields[field_name] != expected_type:
                errors.append('Type of field %s in form of sheet %s is %s '\
                              'but must be %s' % \
                              (field_name, sheet_label, form_fields[field_name],
                               expected_type))
        else:
            if form_fields[field_name] != expected_type.vtype:
                errors.append('Type of field %s in form of sheet %s is %s '\
                              'but must be %s' % \
                              (field_name, sheet_label, expected_type))
            field_choices = if_none(fields_choices[field_name], [])
            missing_choices = (set(expected_type.choices)
                               .difference(field_choices))
            if len(missing_choices) > 0:
                errors.append('Missing choice(s) %s for field %s '\
                              'in form of sheet %s' % \
                              (', '.join(['"%s"'%c for c in missing_choices]),
                               field_name, sheet_label))
    return errors

class EmailledPollTracker:
    """
    * default status -> _to_send

    if form answered -> _answered
    ElseIf email action == plan
        If email status == to_send
            If  date_now < scheduled_send_date
                -> _email_pending
            Else
                -> _email_overdue
        ElseIf email status == error -> _email_error
        ElseIf email status == sent:
            If  date_now < timestamp + overdue_days
                -> _email_sent
            Else
                -> _overdue
        ElseIf email action == call_off -> _cancelled
    """

    def __init__(self, poll_label, email_sheet_label, workbook):

        self.poll_label = poll_label
        self.email_sheet_label = email_sheet_label
        self.workbook = workbook

        errors = self.check()
        if len(errors) > 0:
            for error in errors:
                logger.error(error)
            raise DataConsistencyError(errors)


    def check(self):
        """
        Errors to handle:
        - missing poll sheet
        """
        # TODO: cross check that poll_label is values of email_template
        expected_fields = {
            'Participant_ID' : 'text',
            'Email_Action' : Choice('text', ['plan', 'cancel', 'revoke']),
            'Email_Status' : Choice('text', ['to_send', 'sent', 'error']),
            'Email_Scheduled_Send_Date' : 'datetime',
            'Email_Template' : Choice('text', [self.poll_label]),
            'Overdue_Days' : 'int',
            'User' : 'user_name',
            'Timestamp_Submission' : 'datetime'
        }
        errors = check_sheet(self.workbook, self.email_sheet_label,
                             expected_fields=expected_fields)
        errors.extend(check_sheet(self.workbook, self.poll_label,
                                  expected_fields={'Participant_ID' : 'text',
                                                   'Timestamp_Submission' : \
                                                   'datetime'}))
        return errors

    def track(self, dashboard_df, pids, date_now=None):
        poll_tag = self.poll_label.lower()
        default_status = ('%s_to_send' % poll_tag)
        column_status = self.poll_label

        if column_status not in dashboard_df.columns:
            dashboard_df[column_status] = pd.NA

        date_now = date_now if date_now is not None else datetime.now()

        pids = set(pids).intersection(dashboard_df.index)

        email_df = latest_sheet_data(self.workbook, self.email_sheet_label,
                                     filter_dict={'Email_Template' :
                                                  self.poll_label},
                                     index_column='Participant_ID', indexes=pids)
        if dashboard_error_if_none(email_df, dashboard_df, column_status,
                                   'error %s' % self.email_sheet_label):
            return

        poll_df = latest_sheet_data(self.workbook, self.poll_label,
                                    index_column='Participant_ID', indexes=pids)
        if dashboard_error_if_none(poll_df, dashboard_df, column_status,
                                   'error %s' % self.poll_label):
            return

        dashboard_df.loc[pids, column_status] = default_status

        if email_df.shape[0] > 0:
            try:
                def od_ts(email_df, email_col):
                    f_ts = lambda x: date_now - timedelta(days=x)
                    return email_df['Overdue_Days'].apply(f_ts)

                map_set(dashboard_df, column_status,
                        conditions={
                            '%s_to_send' % poll_tag:
                            (email_df, 'Email_Action', ['cancelled']),
                            '%s_cancelled' % poll_tag:
                            (email_df, 'Email_Action', ['revoke']),
                            '%s_email_pending' % poll_tag:
                            And((email_df, 'Email_Action', ['plan']),
                                (email_df, 'Email_Status', ['to_send']),
                                (email_df, 'Email_Scheduled_Send_Date',
                                 Lower(date_now))),
                            '%s_email_overdue' % poll_tag:
                            And((email_df, 'Email_Action', ['plan']),
                                (email_df, 'Email_Status', ['to_send']),
                                (email_df, 'Email_Scheduled_Send_Date',
                                 GreaterEqual(date_now))),
                            '%s_email_sent' % poll_tag:
                            And((email_df, 'Email_Action', ['plan']),
                                (email_df, 'Email_Status', ['sent']),
                                (email_df, 'Overdue_Days', IsNotNA()),
                                (email_df, 'Timestamp_Submission',
                                 GreaterEqual(od_ts))),
                            '%s_overdue' % poll_tag:
                            And((email_df, 'Email_Action', ['plan']),
                                (email_df, 'Email_Status', ['sent']),
                                (email_df, 'Overdue_Days', IsNotNA()),
                                (email_df, 'Timestamp_Submission',
                                 Lower(od_ts))),
                            '%s_email_error' % poll_tag:
                            And((email_df, 'Email_Action', ['plan']),
                                (email_df, 'Email_Status', ['error'])),
                        })
            except SrcColumnNotFound as e:
                msg = 'Column %s not found in df of sheet %s' % \
                    (e.message, self.email_sheet_label)
                raise SrcColumnNotFound(msg) from e
            except DestColumnNotFound as e:
                msg = 'Column %s not found in dashboard df' % e.message
                raise DestColumnNotFound(msg) from e

        if poll_df.shape[0] > 0:
            try:
                map_set(dashboard_df, column_status,
                        conditions={'%s_answered' % poll_tag:
                                    (poll_df, 'Timestamp_Submission', Any())})
            except SrcColumnNotFound as e:
                msg = 'Column %s not found in df of sheet %s' % \
                    (e.message, self.poll_label)
                raise SrcColumnNotFound(msg) from e
            except DestColumnNotFound as e:
                msg = 'Column %s not found in dashboard df' % e.message
                raise DestColumnNotFound(msg) from e

    def action(self, entry_df, poll_column):
        poll_status = entry_df[poll_column].iat[0]
        if poll_status=='' or pd.isna(poll_status) or poll_status is None or \
           poll_status == '%s_answered' % poll_column:
            return None, ''
        participant_id = entry_df.index[0]
        return form_update_or_new(self.email_sheet_label, self.workbook,
                                  {'Participant_ID' : participant_id,
                                   'Email_Template' : poll_column},
                                  {'Email_Action' : 'plan'})

class InterviewTracker:
    def __init__(self, interview_label, workbook,
                 plan_sheet_label=DEFAULT_INTERVIEW_PLAN_SHEET_LABEL,
                 show_staff_column=True):
        self.interview_label = interview_label
        self.workbook = workbook
        self.plan_sheet_label = plan_sheet_label
        self.show_staff_column = show_staff_column

        errors = self.check()
        if len(errors) > 0:
            for error in errors:
                logger.error(error)
            raise DataConsistencyError(errors)

    def check(self):

        errors = []
        expected_fields = {
            'Participant_ID' : 'text',
            'Session_Action' : Choice('text', ['do_session', 'cancel_session']),
            'Session_Status' : Choice('text', ['done', 'redo']),
            'User' : 'user_name',
            'Timestamp_Submission' : 'datetime'
        }
        errors = check_sheet(self.workbook, self.interview_label,
                             expected_fields=expected_fields)

        expected_fields = {
            'Participant_ID' : 'text',
            'Staff' : 'text',
            'Plan_Action' : Choice('text', ['assign_staff', 'plan']),
            'Interview_Type' : Choice('text', [self.interview_label]),
            'Interview_Date' : 'datetime',
            'Availability' : 'text',
            'Date_Is_Set' : 'boolean',
            'Send_Email' : 'boolean',
            'Email_Schedule' : Choice('text', ['days_before_2']),
            'Email_Template' : Choice('text', [self.interview_label]),
            'Email_Status' : Choice('text', []),
            'Callback_Days' : 'int',
            'User' : 'user_name',
            'Timestamp_Submission' : 'datetime'
        }
        errors.extend(check_sheet(self.workbook, self.plan_sheet_label,
                                  expected_fields=expected_fields))
        return errors

    def action(self, entry_df, interview_column):

        value = entry_df[interview_column].iat[0]
        if value=='' or pd.isna(value) or value is None:
            return None, ''

        participant_id = entry_df.index[0]
        form = None
        action_label = ''
        plan_sheet = self.workbook[self.plan_sheet_label]

        if interview_column.endswith('_Plan'):
            interview_label = interview_column[:-len('_Plan')]
            return form_update_or_new(self.plan_sheet_label, self.workbook,
                                      {'Participant_ID' : participant_id,
                                       'Interview_Type' : interview_label},
                                      {'Plan_Action' : 'plan',
                                       'Send_Email' : True,
                                       'Email_Schedule' : 'days_before_2',
                                       'Email_Template' : interview_label})
            # if value.endswith('_not_done') or value.endswith('_cancelled'):
            # elif value.endswith('_scheduled') or value.endswith('_email_pending') or \
            #  value.endswith('_email_sent') or value.endswith('_email_error') or \
            #  value.endswith('_ok') or value.endswith('_redo'):
        elif interview_column.endswith('_Staff'):
            interview_label = interview_column[:-len('_Staff')]
            return form_update_or_new(self.plan_sheet_label, self.workbook,
                                      {'Participant_ID' : participant_id,
                                       'Interview_Type' : interview_label},
                                      {'Plan_Action' : 'assign_staff',
                                       'Send_Email' : False})
        else:
            interview_label = interview_column
            interview_sheet = self.workbook[interview_label]
            interview_df = interview_sheet.get_df_view('latest')
            selection = (interview_df[interview_df.Participant_ID == participant_id] \
                         if interview_df is not None else pd.DataFrame([]))
            if selection.shape[0] == 0:
                form = interview_sheet.form_new_entry()
                form.set_values_from_entry({'Participant_ID' : participant_id})
                action_label = '%s | New' % interview_sheet.label
            else:
                assert(selection.shape[0] == 1)
                form = interview_sheet.form_update_entry(selection.index[0])
                action_label = '%s | Update' % interview_sheet.label
            form.set_values_from_entry({
                'Session_Action' : 'do_session',
            })
        return form, action_label

    def track(self, dashboard_df, pids, date_now=None):
        interview_tag = self.interview_label.lower()

        logger.debug('Update interview tracking of %s for pids: %s',
                     interview_tag, pids)

        # Keep only entries seen in the dashboard:
        pids = set(pids).intersection(dashboard_df.index)
        logger.debug('pids kept (that are in Dashboard)  : %s', pids)

        default_status = ('%s_not_done' % interview_tag)
        column_status = self.interview_label

        if column_status not in dashboard_df.columns:
            dashboard_df[column_status] = pd.NA

        column_staff = '%s_Staff' % self.interview_label
        default_staff = ('%s_set_staff' % interview_tag)
        if self.show_staff_column and column_staff not in dashboard_df.columns:
            dashboard_df[column_staff] = pd.NA

        column_date = '%s_Plan' % self.interview_label
        default_date = ('%s_plan' % interview_tag)
        if column_date not in dashboard_df.columns:
            dashboard_df[column_date] = pd.NaT

        if self.workbook is None:
            return

        date_now = date_now if date_now is not None else datetime.now()

        interview_df = latest_sheet_data(self.workbook, self.interview_label,
                                         index_column='Participant_ID',
                                         indexes=pids)
        if dashboard_error_if_none(interview_df, dashboard_df, column_status,
                                   'error %s' % self.interview_label):
            return

        plan_df = latest_sheet_data(self.workbook, self.plan_sheet_label,
                                    filter_dict={'Interview_Type' :
                                                 self.interview_label},
                                    index_column='Participant_ID',
                                    indexes=pids)
        if dashboard_error_if_none(plan_df, dashboard_df, column_status,
                                   'error %s' % self.plan_sheet_label):
            return

        if 0:
            print('dashboard_df beginning of track_interview')
            print(dashboard_df)

            print('plan_df beginning of track_interview')
            print(plan_df)

            print('interview_df beginning of track_interview')
            print(interview_df)

        def set_date_from_plan(plan_sel_df):
            availability = plan_sel_df[((plan_sel_df['Plan_Action']=='plan') & \
                                        (~plan_sel_df['Date_Is_Set']))]
            dashboard_df.loc[availability.index, column_date] = \
                availability.loc[availability.index, 'Availability']

            planned = plan_sel_df[((plan_sel_df['Plan_Action']=='plan') & \
                                   (plan_sel_df['Date_Is_Set']))]

            dates = (planned.loc[planned.index, 'Interview_Date']
                     .apply(lambda x: x.strftime(DATE_FMT)))
            dashboard_df.loc[planned.index, column_date] = dates

        def set_date_from_interview(int_sel_df):
            done = int_sel_df[((int_sel_df['Session_Action']!='cancel_session') & \
                               ((int_sel_df['Session_Status']=='done') | \
                                (int_sel_df['Session_Status']=='redo')))]
            dates = (done.loc[done.index, 'Timestamp_Submission']
                     .apply(lambda x: x.strftime(DATE_FMT)))
            dashboard_df.loc[done.index, column_date] = dates

            cancelled = int_sel_df[((int_sel_df['Session_Action']=='cancel_session') | \
                                    (int_sel_df['Session_Status']=='cancel_session'))]
            dashboard_df.loc[cancelled.index, column_date] = '%s_plan' % interview_tag

        common_pids = plan_df.index.intersection(interview_df.index)
        if 0:
            print('Get most recent entry btwn plan and interview')

            print('plan_df:')
            print(plan_df)

            print('interview_df:')
            print(interview_df)

            print('common_pids')
            print(common_pids)

        dashboard_df.loc[pids, column_date] = default_date
        plan_df_fresher, interview_df_fresher = df_keep_higher(plan_df, interview_df)

        # More readable API to replace map_set:
        # match_set(dashboard_df, column_date,
        #           setters=[SetWhere(where=And((plan_df, 'Plan_Action', ['plan']),
        #                                       (plan_df, 'Availability', IsNotNa())),
        #                             value=FetchDf(plan_df, 'Availability')),
        #                    SetWhere(where=And((plan_df, 'Plan_Action', ['plan']),
        #                                       (plan_df, 'Interview_Date', IsNotNa())),
        #                             value=FetchDf(plan_df, 'Interview_Date',
        #                                           apply=fmt_date)),
        #                    SetWhere(where=And((itv_df, 'Session_Action',
        #                                        NotIn('cancel_session')),
        #                                       (itv_df, 'Session_Status',
        #                                        ['done', 'redo'])),
        #                             value=FetchDf(itv_df, 'Timestamp_Submission', apply=fmt_date)),
        #                    SetWhere(where=Or((itv_df, 'Session_Action',
        #                                       ['cancel_session']),
        #                                      (itv_df, 'Session_Status',
        #                                       ['cancel_session'])),
        #                             value='%s_plan' % interview_tag)])

        set_date_from_plan(plan_df_fresher)
        set_date_from_interview(interview_df_fresher)

        # Staff
        if 0:
            print('Set Staff...')
            print('dashboard_df:')
            print(dashboard_df)

            print('plan_df:')
            print(plan_df)

        if self.show_staff_column:
            dashboard_df.loc[pids, column_staff] = default_staff
            dashboard_df.loc[plan_df_fresher.index, column_staff] = \
                plan_df_fresher.loc[:, 'Staff']
            dashboard_df.loc[interview_df_fresher.index, column_staff] = \
                interview_df_fresher.loc[:, 'User']

        # Status
        dashboard_df.loc[pids, column_status] = default_status

        if 1:
            print('dashboard_df before map_set')
            print(dashboard_df)

        logger.debug('Set interview status from %s (selected pids=%s)',
                     self.plan_sheet_label, interview_df_fresher.index)
        if plan_df_fresher.shape[0] > 0:
            try:

                def cb_ts(plan_df, plan_col):
                    f_ts = lambda x: (date_now - timedelta(days=x)
                                      if not pd.isna(x)
                                      else pd.NA)
                    return plan_df['Callback_Days'].apply(f_ts)

                map_set(dashboard_df, column_status,
                        conditions={'%s_scheduled' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Send_Email', [False]),
                             (plan_df_fresher, 'Date_Is_Set', [True]),
                             (plan_df_fresher, 'Interview_Date', IsNotNA())),
                         '%s_callback_tbd' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Date_Is_Set', [False]),
                             (plan_df_fresher, 'Callback_Days', IsNotNA()),
                             (plan_df_fresher, 'Timestamp_Submission',
                              Greater(cb_ts))),
                        '%s_callback_now' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Date_Is_Set', [False]),
                             (plan_df_fresher, 'Callback_Days', IsNotNA()),
                             (plan_df_fresher, 'Timestamp_Submission', Lower(cb_ts))),
                         '%s_email_pending' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Interview_Date', IsNotNA()),
                             (plan_df_fresher, 'Date_Is_Set', [True]),
                             (plan_df_fresher, 'Send_Email', [True]),
                             (plan_df_fresher, 'Email_Status', ['to_send'])),
                         '%s_email_sent' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Interview_Date', IsNotNA()),
                             (plan_df_fresher, 'Date_Is_Set', [True]),
                             (plan_df_fresher, 'Send_Email', [True]),
                             (plan_df_fresher, 'Email_Status', ['sent'])),
                         '%s_email_error' % interview_tag:
                         And((plan_df_fresher, 'Plan_Action', ['plan']),
                             (plan_df_fresher, 'Interview_Date', IsNotNA()),
                             (plan_df_fresher, 'Date_Is_Set', [True]),
                             (plan_df_fresher, 'Send_Email', [True]),
                             (plan_df_fresher, 'Email_Status', ['error'])),
                        })
            except SrcColumnNotFound as e:
                msg = 'Column %s not found in df of sheet %s' % \
                    (e.message, plan_sheet_label)
                raise SrcColumnNotFound(msg) from e
            except DestColumnNotFound as e:
                msg = 'Column %s not found in dashboard df' % e.message
                raise DestColumnNotFound(msg) from e

            mask_callback_tbd = (dashboard_df
                                 .loc[plan_df_fresher.index, column_status] \
                                 == '%s_callback_tbd' % interview_tag)
            pids_callback_tbd = mask_callback_tbd[mask_callback_tbd].index
            if len(pids_callback_tbd) > 0:
                plan_df_for_cb_tbd = plan_df_fresher.loc[pids_callback_tbd]
                cb_days = (plan_df_for_cb_tbd['Timestamp_Submission'] \
                           + pd.to_timedelta(plan_df_for_cb_tbd['Callback_Days'],
                                             unit='d') \
                           - date_now).dt.days
                dashboard_df.loc[pids_callback_tbd, column_status] = \
                    cb_days.apply(lambda d : '%s_callback_%dD' % (interview_tag,d))
        if 1:
            print('dashboard_df after map_set from plan_df')
            print(dashboard_df)

        logger.debug('Set interview status from %s', self.interview_label)
        if interview_df_fresher.shape[0] > 0:
            try:
                map_set(dashboard_df, column_status,
                        {'%s_done' % interview_tag:
                         And((interview_df_fresher, 'Session_Action', ['do_session']),
                             (interview_df_fresher, 'Session_Status', ['done'])),
                         '%s_redo' % interview_tag:
                         And((interview_df_fresher, 'Session_Action', ['do_session']),
                             (interview_df_fresher, 'Session_Status', ['redo'])),
                         '%s_cancelled' % interview_tag:
                         (interview_df_fresher, 'Session_Action', ['cancel_session'])
                        })
            except SrcColumnNotFound as e:
                msg = 'Column %s not found in df of sheet %s' % \
                    (e.message, interview_sheet_label)
                raise SrcColumnNotFound(msg) from e
            except DestColumnNotFound as e:
                msg = 'Column %s not found in dashboard df' % e.message
                raise DestColumnNotFound(msg) from e

        if 1:
            print('dashboard_df after map_set from interview_df')
            print(dashboard_df)


def ___track_interview_old(dashboard_df, interview_label, workbook, pids,
                        plan_sheet_label=DEFAULT_INTERVIEW_PLAN_SHEET_LABEL,
                        date_now=None, show_staff_column=True):
    """

    Date
    * default status -> _to_plan

    * if more recent entry in plan_sheet
      (Evaluation_Type matches given interview_label) and action != cancel_date
         If action != cancel_date:
             If Reachable:
                 If Interview_Plan != NA:
                     -> show Interview_Plan
                 Else If Availability != NA:
                     -> show Availability

       ACTION: new/update entry in plan_sheet with:
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              email_template=interview_label

    * else more recent entry in interview_sheet and status==done
       -> show session date

       ACTION: new entry in plan_sheet with:
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              email_template=interview_label

    Staff

    * if more recent entry in plan_sheet
      (Evaluation_Type matches given interview_label) and action != cancel_date
       -> show staff name from plan_sheet

    * else more rencent entry in interview_sheet
       -> show staff name from interview_sheet

    Status

    * Default status -> _not_done
        ACTION: new/update entry in plan_sheet with :
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              callback_delay_days=7, email_template=interview_label

    ** Most recent entry is in plan sheet **

    * if plan_sheet.action==plan and plan_sheet.interview_date==NA and
      callback
           If now < entry_timestamp + callback_delay_days:
               -> _callback_{nb_days}_days
               where nb_days = entry_timestamp + callback_delay_days - now
           Else
               -> _callback

    * if plan_sheet.action==plan and plan_sheet.interview_date defined and
         not plan_sheet.send_email
       -> '_scheduled'"
       ACTION: new entry in interview_sheet with:
              pid, staff=interview_staff, action=do_session

    * if plan_sheet.action==plan and plan_sheet.send_email and
          plan_sheet.email_status=='pending':
       -> _email_pending
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, send_email=True,
              email_date=days_before_2,
              email_template=interview_label + '_remind'

    * if plan_sheet.action==plan and plan_sheet.send_email and
          plan_sheet.email_status=='sent':
       -> _email_sent
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if plan_sheet.action==plan and plan_sheet.send_email and
          plan_sheet.email_status=='error':
       -> "interview_label + '_email_error'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session


    ** Most recent entry is in plan sheet **

    * if interview_sheet.action==do_session and
          interview_sheet.session_status=='done':
       -> _ok
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==do_session and
          interview_sheet.session_status=='redo':
       -> _redo
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==cancel_session or
          interview_sheet.action==do_session and
          interview_sheet.session_status=='cancel':
       -> _cancelled
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    """
    interview_tag = interview_label.lower()

    logger.debug('Update interview tracking of %s for pids: %s',
                 interview_tag, pids)

    # Keep only entries seen in the dashboard:
    pids = set(pids).intersection(dashboard_df.index)
    logger.debug('pids kept (that are in Dashboard)  : %s', pids)

    default_status = ('%s_not_done' % interview_tag)
    column_status = interview_label

    if column_status not in dashboard_df.columns:
        dashboard_df[column_status] = pd.NA

    column_staff = '%s_Staff' % interview_label
    default_staff = ('%s_set_staff' % interview_tag)
    if show_staff_column and column_staff not in dashboard_df.columns:
        dashboard_df[column_staff] = pd.NA

    column_date = '%s_Plan' % interview_label
    default_date = ('%s_plan' % interview_tag)
    if column_date not in dashboard_df.columns:
        dashboard_df[column_date] = pd.NaT

    if workbook is None:
        return

    date_now = date_now if date_now is not None else datetime.now()

    # expected_columns=['Participant_ID', 'Staff',
    #                   'Session_Action',
    #                   'Session_Status',
    #                   'Timestamp_Submission'],

    interview_df = latest_sheet_data(workbook, interview_label,
                                     index_column='Participant_ID',
                                     indexes=pids)
    # expected_columns=[
    #     'Participant_ID', 'Staff', 'Plan_Action',
    #     'Interview_Type', 'Interview_Date',
    #     'Availability', 'Send_Email',
    #     'Email_Schedule', 'Email_Template',
    #     'Email_Status', 'Timestamp_Submission'],

    plan_df = latest_sheet_data(workbook, plan_sheet_label,
                                filter_dict={'Interview_Type' : interview_label},
                                index_column='Participant_ID',
                                indexes=pids)
    if 0:
        print('dashboard_df beginning of track_interview')
        print(dashboard_df)

        print('plan_df beginning of track_interview')
        print(plan_df)

        print('interview_df beginning of track_interview')
        print(interview_df)

    def set_date_from_plan(plan_sel_df):
        availability = plan_sel_df[((plan_sel_df['Plan_Action']=='plan') & \
                                    (~plan_sel_df['Date_Is_Set']))]
        dashboard_df.loc[availability.index, column_date] = \
            availability.loc[availability.index, 'Availability']

        planned = plan_sel_df[((plan_sel_df['Plan_Action']=='plan') & \
                               (plan_sel_df['Date_Is_Set']))]

        dates = (planned.loc[planned.index, 'Interview_Date']
                 .apply(lambda x: x.strftime(DATE_FMT)))
        dashboard_df.loc[planned.index, column_date] = dates

    def set_date_from_interview(int_sel_df):
        done = int_sel_df[((int_sel_df['Session_Action']!='cancel_session') & \
                           ((int_sel_df['Session_Status']=='done') | \
                            (int_sel_df['Session_Status']=='redo')))]
        dates = (done.loc[done.index, 'Timestamp_Submission']
                 .apply(lambda x: x.strftime(DATE_FMT)))
        dashboard_df.loc[done.index, column_date] = dates

        cancelled = int_sel_df[((int_sel_df['Session_Action']=='cancel_session') | \
                                (int_sel_df['Session_Status']=='cancel_session'))]
        dashboard_df.loc[cancelled.index, column_date] = \
            '%s_plan' % interview_tag

    common_pids = plan_df.index.intersection(interview_df.index)
    if 0:
        print('Get most recent entry btwn plan and interview')

        print('plan_df:')
        print(plan_df)

        print('interview_df:')
        print(interview_df)

        print('common_pids')
        print(common_pids)

    dashboard_df.loc[pids, column_date] = default_date
    plan_df_fresher, interview_df_fresher = df_keep_higher(plan_df, interview_df)

    # More readable API to replace map_set:
    # match_set(dashboard_df, column_date,
    #           setters=[SetWhere(where=And((plan_df, 'Plan_Action', ['plan']),
    #                                       (plan_df, 'Availability', IsNotNa())),
    #                             value=FetchDf(plan_df, 'Availability')),
    #                    SetWhere(where=And((plan_df, 'Plan_Action', ['plan']),
    #                                       (plan_df, 'Interview_Date', IsNotNa())),
    #                             value=FetchDf(plan_df, 'Interview_Date',
    #                                           apply=fmt_date)),
    #                    SetWhere(where=And((itv_df, 'Session_Action',
    #                                        NotIn('cancel_session')),
    #                                       (itv_df, 'Session_Status',
    #                                        ['done', 'redo'])),
    #                             value=FetchDf(itv_df, 'Timestamp_Submission', apply=fmt_date)),
    #                    SetWhere(where=Or((itv_df, 'Session_Action',
    #                                       ['cancel_session']),
    #                                      (itv_df, 'Session_Status',
    #                                       ['cancel_session'])),
    #                             value='%s_plan' % interview_tag)])

    set_date_from_plan(plan_df_fresher)
    set_date_from_interview(interview_df_fresher)

    # Staff
    if 0:
        print('Set Staff...')
        print('dashboard_df:')
        print(dashboard_df)

        print('plan_df:')
        print(plan_df)

    if show_staff_column:
        dashboard_df.loc[pids, column_staff] = default_staff
        dashboard_df.loc[plan_df_fresher.index, column_staff] = \
            plan_df_fresher.loc[:, 'Staff']
        dashboard_df.loc[interview_df_fresher.index, column_staff] = \
            interview_df_fresher.loc[:, 'Staff']

    # Status
    dashboard_df.loc[pids, column_status] = default_status

    if 1:
        print('dashboard_df before map_set')
        print(dashboard_df)

    logger.debug('Set interview status from %s (selected pids=%s)',
                 plan_sheet_label, interview_df_fresher.index)
    if plan_df_fresher.shape[0] > 0:
        try:

            def cb_ts(plan_df, plan_col):
                f_ts = lambda x: (date_now - timedelta(days=x)
                                  if not pd.isna(x)
                                  else pd.NA)
                return plan_df['Callback_Days'].apply(f_ts)

            map_set(dashboard_df, column_status,
                    conditions={'%s_scheduled' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Send_Email', [False]),
                         (plan_df_fresher, 'Date_Is_Set', [True]),
                         (plan_df_fresher, 'Interview_Date', IsNotNA())),
                     '%s_callback_tbd' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Date_Is_Set', [False]),
                         (plan_df_fresher, 'Callback_Days', IsNotNA()),
                         (plan_df_fresher, 'Timestamp_Submission',
                          Greater(cb_ts))),
                    '%s_callback_now' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Date_Is_Set', [False]),
                         (plan_df_fresher, 'Callback_Days', IsNotNA()),
                         (plan_df_fresher, 'Timestamp_Submission', Lower(cb_ts))),
                     '%s_email_pending' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Interview_Date', IsNotNA()),
                         (plan_df_fresher, 'Date_Is_Set', [True]),
                         (plan_df_fresher, 'Send_Email', [True]),
                         (plan_df_fresher, 'Email_Status', ['to_send'])),
                     '%s_email_sent' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Interview_Date', IsNotNA()),
                         (plan_df_fresher, 'Date_Is_Set', [True]),
                         (plan_df_fresher, 'Send_Email', [True]),
                         (plan_df_fresher, 'Email_Status', ['sent'])),
                     '%s_email_error' % interview_tag:
                     And((plan_df_fresher, 'Plan_Action', ['plan']),
                         (plan_df_fresher, 'Interview_Date', IsNotNA()),
                         (plan_df_fresher, 'Date_Is_Set', [True]),
                         (plan_df_fresher, 'Send_Email', [True]),
                         (plan_df_fresher, 'Email_Status', ['error'])),
                    })
        except SrcColumnNotFound as e:
            msg = 'Column %s not found in df of sheet %s' % \
                (e.message, plan_sheet_label)
            raise SrcColumnNotFound(msg) from e
        except DestColumnNotFound as e:
            msg = 'Column %s not found in dashboard df' % e.message
            raise DestColumnNotFound(msg) from e

        mask_callback_tbd = (dashboard_df
                             .loc[plan_df_fresher.index, column_status] \
                             == '%s_callback_tbd' % interview_tag)
        pids_callback_tbd = mask_callback_tbd[mask_callback_tbd].index
        if len(pids_callback_tbd) > 0:
            plan_df_for_cb_tbd = plan_df_fresher.loc[pids_callback_tbd]
            cb_days = (plan_df_for_cb_tbd['Timestamp_Submission'] \
                       + pd.to_timedelta(plan_df_for_cb_tbd['Callback_Days'],
                                         unit='d') \
                       - date_now).dt.days
            dashboard_df.loc[pids_callback_tbd, column_status] = \
                cb_days.apply(lambda d : '%s_callback_%dD' % (interview_tag,d))
    if 1:
        print('dashboard_df after map_set from plan_df')
        print(dashboard_df)

    logger.debug('Set interview status from %s', interview_label)
    if interview_df_fresher.shape[0] > 0:
        try:
            map_set(dashboard_df, column_status,
                    {'%s_done' % interview_tag:
                     And((interview_df_fresher, 'Session_Action', ['do_session']),
                         (interview_df_fresher, 'Session_Status', ['done'])),
                     '%s_redo' % interview_tag:
                     And((interview_df_fresher, 'Session_Action', ['do_session']),
                         (interview_df_fresher, 'Session_Status', ['redo'])),
                     '%s_cancelled' % interview_tag:
                     (interview_df_fresher, 'Session_Action', ['cancel_session'])
                    })
        except SrcColumnNotFound as e:
            msg = 'Column %s not found in df of sheet %s' % \
                (e.message, interview_sheet_label)
            raise SrcColumnNotFound(msg) from e
        except DestColumnNotFound as e:
            msg = 'Column %s not found in dashboard df' % e.message
            raise DestColumnNotFound(msg) from e

    if 1:
        print('dashboard_df after map_set from interview_df')
        print(dashboard_df)

def ts_data_latest_by_pid(df):
    if df is None or df.shape[0]==0:
        return df.set_index('Participant_ID')
    max_ts = lambda x: x.loc[x['Timestamp_Submission']==x['Timestamp_Submission'].max()]
    df = df.groupby(by='Participant_ID', group_keys=False).apply(max_ts)
    df.set_index('Participant_ID', inplace=True)
    return df

import pandas as pd
import logging
from datetime import datetime, timedelta, time
from .sheet_plugin import SheetPlugin
from .core import df_filter_from_dict

logger = logging.getLogger('piccel')

class DataDefinitionError(Exception): pass
class LescaDashboard(SheetPlugin):
    def __init__(self, sheet):
        super(LescaDashboard, self).__init__(sheet)
        self.df = None

    def after_workbook_load(self):
        super(LescaDashboard, self).after_workbook_load()
        self.pp = self.workbook['Participants']
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
            self.df = (self.pp.latest_update_df()[['Participant_ID']]
                       .sort_values(by='Participant_ID')
                       .reset_index(drop=True))
            self.df.set_index('Participant_ID', inplace=True)
            self.refresh_entries(self.df.index)
        else:
            self.df = (pd.DataFrame(columns=['Participant_ID'])
                       .set_index('Participant_ID'))
        self.sheet.invalidate_cached_views()

    def sheets_to_watch(self):
        return ['Participants']

    def show_index_in_ui(self):
        return True

    def refresh_entries(self, pids):
        logger.warning('refresh_entries not implemented in plugin of sheet %s',
                       self.sheet.label)

    def get_full_view(self, df):
        return self.df

    def views(self, base_views):
        return {'full' : self.get_full_view}

    def default_view(self):
        return 'full'

    def update(self, sheet_source, entry_df, deletion=False, clear=False):
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


    def action(self):
        raise NotImplementedError('TODO: default action')

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

DATE_FMT = '%Y-%m-%d %H:%M:%S'
DEFAULT_INTERVIEW_PLAN_SHEET_LABEL = 'Interview_Plan'

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


class ParticipantStatusTracker:
    def __init__(self, participant_sheet_label, progress_note_sheet_label,
                 workbook, dashboard_column_status='Study_Status'):
        self.participant_sheet_label = participant_sheet_label
        self.progress_note_sheet_label = progress_note_sheet_label
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
            'Study_Status' : 'text',
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
        errors.extend(check_sheet(self.workbook, self.progress_note_sheet_label,
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

        pnotes_df = latest_sheet_data(self.workbook,
                                      self.progress_note_sheet_label,
                                      index_column='Participant_ID')

        status_df = latest_sheet_data(self.workbook,
                                      self.participant_sheet_label,
                                      index_column='Participant_ID')

        pnotes_fresher, status_fresher = df_keep_higher(pnotes_df, status_df)

        dashboard_df.loc[status_fresher.index, self.dashboard_column_status] = \
            status_fresher.loc[:, 'Study_Status']

        map_set(dashboard_df, self.dashboard_column_status,
                conditions={'confirm_drop':
                            (pnotes_fresher, 'Note_Type',
                             ['withdrawal', 'exclusion'])})

class PollTracker:
    def __init__(self, poll_sheet_label, poll_answer_column, workbook,
                 default_status, dashboard_column=None):
        self.poll_sheet_label = poll_sheet_label
        self.workbook = workbook
        self.dashboard_column = if_none(dashboard_column, poll_sheet_label)
        self.poll_answer_column = poll_answer_column

    def check(self):
        return check_sheet(self.workbook, self.interview_label,
                           expected_fields={'Participant_ID' : 'text'})

    def track(self, dashboard_df, pids, poll_filter=None):
        poll_df = latest_sheet_data(self.workbook, self.poll_sheet_label,
                                    index_column='Participant_ID',
                                    filter_dict=poll_filter,
                                    indexes=pids)
        dashboard_df.loc[pids, self.dashboard_column] = self.default_status
        if poll_df.shape[0] > 0:
            answered_df = poll_df[~pd.isna(poll_df[self.poll_answer_column])]
            dashboard_df.loc[answered_df.index, self.dashboard_column] = \
                answered_df[self.poll_answer_column]


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
                # from IPython import embed; embed()
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

def latest_sheet_data(workbook, sheet_label, filter_dict=None,
                      index_column=None, indexes=None):
    df = workbook[sheet_label].get_df_view('latest')

    if df is None:
        from IPython import embed; embed()
    if filter_dict is not None:
        df = df_filter_from_dict(df, filter_dict)
    if index_column is not None:
        df = df.set_index('Participant_ID')
        if not df.index.is_unique:
            logger.warning('Index of latest data from sheet %s is not unique',
                           sheet_label)
    if indexes is not None:
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

def if_none(value, default_value):
    return value if value is not None else default_value

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
                              (sheet_label, field_name, expected_type))
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
        If email status == to_send -> _email_pending
        ElseIf email status == error -> _email_error
        ElseIf email status == sent:
            If  date_now < timestamp + overdue_days
                -> _email_sent
            Else
                -> _email_overdue
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

        poll_df = latest_sheet_data(self.workbook, self.poll_label,
                                    index_column='Participant_ID', indexes=pids)

        dashboard_df.loc[pids, column_status] = default_status

        if email_df.shape[0] > 0:
            try:
                def od_ts(email_df, email_col):
                    f_ts = lambda x: date_now - timedelta(days=x)
                    # from IPython import embed; embed()
                    return email_df['Overdue_Days'].apply(f_ts)

                map_set(dashboard_df, column_status,
                        conditions={
                            '%s_to_send' % poll_tag:
                            (email_df, 'Email_Action', ['cancelled']),
                            '%s_cancelled' % poll_tag:
                            (email_df, 'Email_Action', ['revoke']),
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

        plan_df = latest_sheet_data(self.workbook, self.plan_sheet_label,
                                    filter_dict={'Interview_Type' :
                                                 self.interview_label},
                                    index_column='Participant_ID',
                                    indexes=pids)
        if 1:
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
        if 1:
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
        if 1:
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


def track_interview_old(dashboard_df, interview_label, workbook, pids,
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
    if 1:
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
    if 1:
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
    if 1:
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
        return None
    max_ts = lambda x: x.loc[x['Timestamp_Submission']==x['Timestamp_Submission'].max()]
    df = df.groupby(by='Participant_ID', group_keys=False).apply(max_ts)
    df.set_index('Participant_ID', inplace=True)
    return df

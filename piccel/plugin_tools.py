import pandas as pd
import logging
from .sheet_plugin import SheetPlugin

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
            if not (self.workbook[sheet_label].form_master
                    .has_key('Participant_ID')):
                raise DataDefinitionError('Participant_ID not found in '\
                                          'keys of sheet %s' % sheet_label)

        self.reset_data()

    def reset_data(self):
        if self.pp.df is not None and self.pp.df.shape[0] > 0:
            self.df = (self.pp.df[['Participant_ID']]
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

    def reset_view_index_for_display(self):
        return True

    def refresh_entries(self, pids):
        logger.warning('refresh_entries not implement in plugin of sheet %s',
                       self.sheet.label)

    def get_full_view(self, df, for_display=False):
        df = self.df.sort_index()
        return df.reset_index() if for_display else df

    def views(self, base_views, for_display=False):
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
        entry_df = entry_df.set_index('Participant_ID')

        if sheet_source.label == self.pp.label and \
           entry_df.index.array[0] not in self.df.index:
            empty_df = pd.DataFrame([], index=entry_df.index)
            self.df = self.df.append(empty_df)
            self.sheet.invalidate_cached_views()
            self.sheet.notifier.notify('appended_entry')
            # self.df.sort_index(inplace=True) # TODO: handle in UI view
        if entry_df.index[0] in self.df.index:
            self.refresh_entries(entry_df.index)
            self.sheet.invalidate_cached_views()
            self.sheet.notifier.notify('entry_set', entry_id=entry_df.index[0])
        else:
            logger.warning('Update plugin of sheet %s: '\
                           'udpated entry from %s with id=%s is not in index',
                           self.sheet.label, sheet_source.label,
                           entry_df.index.values[0])


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
    def __init__(self, value):
        self.value = value

class NotIn(Comparator):
    def __init__(self, value):
        super(NotIn, self).__init__(value)
        assert(isinstance(value, list))

class Less(Comparator): pass
class LessEqual(Comparator): pass
class Greater(Comparator): pass
class GreaterEqual(Comparator): pass

class SrcColumnNotFound(Exception): pass
class DestColumnNotFound(Exception): pass

def filter_indexes(filter_def):

    src_df, src_col, predicate_def = filter_def

    if src_col not in src_df.columns:
        raise SrcColumnNotFound(src_col)

    if isinstance(predicate_def, list):
        mask = lambda src_df, src_col: src_df[src_col].isin(predicate_def)
    elif isinstance(predicate_def, NotIn):
        mask = lambda src_df, src_col: ~src_df[src_col].isin(predicate_def)
    elif isinstance(predicate_def, Less):
        mask = lambda src_df, src_col: src_df[src_col] < predicate_def.value
    elif isinstance(predicate_def, LessEqual):
        mask = lambda src_df, src_col: src_df[src_col] <= predicate_def.valu
    elif isinstance(predicate_def, Greater):
        mask = lambda src_df, src_col: src_df[src_col] > predicate_def.value
    elif isinstance(predicate_def, GreaterEqual):
        mask = lambda src_df, src_col: src_df[src_col] >= predicate_def.value
    elif callable(predicate_def):
        mask = predicate_def()
    else:
        raise Exception('Invalid predicate_def %s' % predicate_def)
    return src_df[mask(src_df, src_col)].index


def interview_action(entry_df, interview_column, workbook):

    value = entry_df[interview_column].iat[0]
    if value=='' or pd.isna(value) or value is None:
        return None

    form = None
    action_label = ''
    if interview_column.endswith('_Date'):
        # if value.endswith('_not_scheduled') or value.endswith('_cancelled'):
        # elif value.endswith('_scheduled') or value.endswith('_email_pending') or \
        #  value.endswith('_email_sent') or value.endswith('_email_error') or \
        #  value.endswith('_ok') or value.endswith('_redo'):
        raise NotImplementedError()
    elif interview_column.endswith('_Staff'):
        raise NotImplementedError()
    else:
        interview_label = interview_column
        interview_sheet = workbook[interview_label]
        participant_id = entry_df.index.values[0]
        interview_df = interview_sheet.get_df_view('latest')
        selection = interview_df[interview_df.Participant_Id == participant_id] \
            if interview_df is not None else pd.DataFrame([])
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

DATE_FMT = '%Y-%m-%d %H:%M:%S'
DEFAULT_INTERVIEW_PLAN_SHEET_LABEL = 'Interview_Plan'
def track_interview(dashboard_df, interview_label, workbook, pids,
                    plan_sheet_label=DEFAULT_INTERVIEW_PLAN_SHEET_LABEL):
    """

    Date
    * default status -> None

    * if more recent entry in date_sheet
      (Evaluation_Type matches given interview_label) and action != cancel_date
         if Interview_Date != NA
            -> show Interview_Date
         else
            -> show Availability

       ACTION: new entry in plan_sheet with:
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              email_template=interview_label + '_remind'

    * else more recent entry in interview_sheet and status==done
       -> show session date

       ACTION: new entry in plan_sheet with:
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              email_template=interview_label + '_remind'

    Staff

    * if more recent entry in plan_sheet
      (Evaluation_Type matches given interview_label) and action != cancel_date
       -> show staff name from plan_sheet

    * else more rencent entry in interview_sheet
       -> show staff name from interview_sheet

    Status

    * Default status -> "interview_label + '_not_scheduled'"
        ACTION: new entry in plan_sheet with :
              pid, evaluation_type=interview_label, action=plan,
              send_email=True, email_date=days_before_2,
              email_template=interview_label

    * if plan_sheet.action==plan and plan_sheet.interview_date defined and
         not plan_sheet.send_email
       -> "interview_label + '_scheduled'"
       ACTION: new entry in interview_sheet with:
              pid, staff=interview_staff, action=do_session

    * if plan_sheet.action==plan and plan_sheet.send_email and
          plan_sheet.email_status=='to_send':
       -> "interview_label + '_email_pending'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, send_email=True,
              email_date=days_before_2,
              email_template=interview_label + '_remind'

    * if plan_sheet.action==plan and plan_sheet.send_email and
          plan_sheet.email_status=='sent':
       -> "interview_label + '_email_sent'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==plan and interview_sheet.send_email and
          interview_sheet.email_status=='error':
       -> "interview_label + '_email_error'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==do_session and
          interview_sheet.session_status=='done':
       -> "interview_label + '_ok'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==do_session and
          interview_sheet.session_status=='redo':
       -> "interview_label + '_redo'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    * if interview_sheet.action==cancel_session:
       -> "interview_label + '_cancelled'"
       ACTION: new entry in interview_sheet with:
              pid, interview_staff, action=do_session

    """
    interview_tag = interview_label.lower()
    default_status = ('%s_not_scheduled' % interview_tag)
    column_status = interview_label

    if column_status not in dashboard_df.columns:
        dashboard_df[column_status] = default_status

    column_staff = '%s_Staff' % interview_label
    if column_staff not in dashboard_df.columns:
        dashboard_df[column_staff] = pd.NA

    column_date = '%s_Date' % interview_label
    if column_date not in dashboard_df.columns:
        dashboard_df[column_date] = pd.NaT

    if 0:
        print('dashboard_df beginning of track_interview')
        print(dashboard_df)

    if workbook is None:
        return

    interview_df = (workbook[interview_label].get_df_view('latest') \
                    if workbook.has_sheet(plan_sheet_label) else None)

    if interview_df is None:
        interview_df = pd.DataFrame(columns=['Participant_ID', 'Staff',
                                             'Session_Action', 'Session_Status',
                                             'Timestamp'])
    interview_df = interview_df.set_index('Participant_ID')

    plan_df = (workbook[plan_sheet_label].get_df_view('latest') \
               if workbook.has_sheet(plan_sheet_label) else None)

    if plan_df is None:
        plan_df = pd.DataFrame(columns=['Participant_ID', 'Staff', 'Plan_Action',
                                        'Interview_Type', 'Interview_Date',
                                        'Availability', 'Send_Email',
                                        'Email_Schedule', 'Email_Template',
                                        'Email_Status', 'Timestamp'])
    plan_df = plan_df.set_index('Participant_ID')
    plan_df = plan_df[plan_df['Interview_Type'] == interview_label]

    common_index = (set(pids)
                    .intersection(dashboard_df.index)
                    .intersection(interview_df.index))
    interview_df = interview_df.loc[common_index, :]

    common_index = (set(pids)
                    .intersection(dashboard_df.index)
                    .intersection(plan_df.index))
    plan_df = plan_df.loc[common_index, :]

    # Date
    dashboard_df.loc[common_index, column_date] = pd.NaT

    def set_date_from_plan(pids):

        availability = plan_df[((plan_df['Plan_Action']=='plan') & \
                                (~pd.isna(plan_df['Availability'])))]
        common_index = set(pids).intersection(availability.index)
        dashboard_df.loc[common_index, column_date] = \
            availability.loc[common_index, 'Availability']

        planned = plan_df[((plan_df['Plan_Action']=='plan') & \
                           (~pd.isna(plan_df['Interview_Date'])))]
        common_index = set(pids).intersection(planned.index)

        dates = (planned.loc[common_index,'Interview_Date']
                 .apply(lambda x: x.strftime(DATE_FMT)))
        dashboard_df.loc[common_index, column_date] = dates

    def set_date_from_interview(pids):
        done = interview_df[((interview_df['Session_Action']!='cancel_session') & \
                             ((interview_df['Session_Status']=='done') | \
                              (interview_df['Session_Status']=='redo')))]
        common_index = set(pids).intersection(done.index)
        dates = (done.loc[common_index, 'Timestamp']
                 .apply(lambda x: x.strftime(DATE_FMT)))
        dashboard_df.loc[common_index, column_date] = dates

    common_pids = plan_df.index.intersection(interview_df.index)
    if 1:
        print('Get most recent entry btwn plan and interview')

        print('plan_df:')
        print(plan_df)

        print('interview_df:')
        print(interview_df)

        print('common_pids')
        print(common_pids)

    mask = (plan_df.loc[common_pids, 'Timestamp'] > \
            interview_df.loc[common_pids, 'Timestamp'])
    mask = mask[mask]
    pids_plan_more_recent = plan_df.loc[mask.index].index

    pids_interview_more_recent = common_pids.difference(pids_plan_more_recent)

    pids_plan_only = plan_df.index.difference(common_pids)
    pids_plan = pids_plan_more_recent.union(pids_plan_only)
    set_date_from_plan(pids_plan)

    pids_interview_only = interview_df.index.difference(common_pids)

    pids_interview = pids_interview_more_recent.union(pids_interview_only)
    set_date_from_interview(pids_interview)

    # Staff
    if 0:
        print('Set Staff...')
        print('dashboard_df:')
        print(dashboard_df)

        print('plan_df:')
        print(plan_df)

    dashboard_df.loc[common_index, column_staff] = ''
    dashboard_df.loc[pids_plan, column_staff] = \
        plan_df.loc[pids_plan, 'Staff']
    dashboard_df.loc[pids_interview, column_staff] = \
        interview_df.loc[pids_interview, 'Staff']

    # Status
    dashboard_df.loc[pids, column_status] = default_status

    if 1:
        print('dashboard_df before map_set')
        print(dashboard_df)

    plan_df_selected = plan_df.loc[pids_plan, :]

    logger.debug('Set interview status from %s (selected pids=%s)',
                 plan_sheet_label, pids_plan)
    try:
        map_set(dashboard_df, column_status,
                {'%s_scheduled' % interview_tag:
                 And((plan_df_selected, 'Plan_Action', ['plan']),
                     (plan_df_selected, 'Send_Email', [False])),
                 '%s_email_pending' % interview_tag:
                 And((plan_df_selected, 'Plan_Action', ['plan']),
                     (plan_df_selected, 'Send_Email', [True]),
                     (plan_df_selected, 'Email_Status', ['to_send'])),
                 '%s_email_sent' % interview_tag:
                 And((plan_df_selected, 'Plan_Action', ['plan']),
                     (plan_df_selected, 'Send_Email', [True]),
                     (plan_df_selected, 'Email_Status', ['sent'])),
                 '%s_email_error' % interview_tag:
                 And((plan_df_selected, 'Plan_Action', ['plan']),
                     (plan_df_selected, 'Send_Email', [True]),
                     (plan_df_selected, 'Email_Status', ['error'])),
                })
    except SrcColumnNotFound as e:
        msg = 'Column %s not found in df of sheet %s' % (e.msg, plan_sheet_label)
        raise SrcColumnNotFound(msg) from e
    except DestColumnNotFound as e:
        msg = 'Column %s not found in dashboard df' % e.msg
        raise DestColumnNotFound(msg) from e

    if 1:
        print('dashboard_df after map_set from plan_df')
        print(dashboard_df)

    interview_df_selected = interview_df.loc[pids_interview, :]

    logger.debug('Set interview status from %s', interview_label)
    try:
        map_set(dashboard_df, column_status,
                {'%s_ok' % interview_tag:
                 And((interview_df_selected, 'Session_Action', ['do_session']),
                     (interview_df_selected, 'Session_Status', ['done'])),
                 '%s_redo' % interview_tag:
                 And((interview_df_selected, 'Session_Action', ['do_session']),
                     (interview_df_selected, 'Session_Status', ['redo'])),
                 '%s_cancelled' % interview_tag:
                 (interview_df_selected, 'Session_Action', ['cancel_session'])
                })
    except SrcColumnNotFound as e:
        msg = 'Column %s not found in df of sheet %s' % \
            (e.msg, interview_sheet_label)
        raise SrcColumnNotFound(msg) from e
    except DestColumnNotFound as e:
        msg = 'Column %s not found in dashboard df' % e.msg
        raise DestColumnNotFound(msg) from e

    if 1:
        print('dashboard_df after map_set from interview_df')
        print(dashboard_df)

def ts_data_latest_by_pid(df):
    if df is None or df.shape[0]==0:
        return None
    max_ts = lambda x: x.loc[x['Timestamp']==x['Timestamp'].max()]
    df = df.groupby(by='Participant_ID', group_keys=False).apply(max_ts)
    df.set_index('Participant_ID', inplace=True)
    return df

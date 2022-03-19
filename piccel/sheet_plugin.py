import pandas as pd
import numpy as np
import inspect

from piccel.core import LazyFunc, SheetNotFound, strip_indent, UserRole

import logging
logger = logging.getLogger('piccel')

plugin_source_header = \
"""
import pandas as pd
import numpy as np
from piccel import UserRole
from piccel.sheet_plugin import SheetPlugin
from piccel.plugin_tools import map_set, And, Or, form_new
from piccel.plugin_tools import (LescaDashboard, InterviewTracker,
                                 form_update_or_new,
                                 DEFAULT_INTERVIEW_PLAN_SHEET_LABEL,
                                 PollTracker, EmailledPollTracker,
                                 ParticipantStatusTracker)
from piccel.form import Form
from piccel.logging import logger
"""

class SheetPlugin:

    def __init__(self, data_sheet):
        """
        Called when user has logged in the associated data_sheet,
        after data loading.

        Useful methods:
           - workbook.user_roles():
                 Itrator over user, role
           - workbook.get_user_role():
                 get the role of the user who opened the workbook
           - workbook.get_user():
                 get the name of the user who opened the workbook
           - workbook.sheets():
                 iterator over sheets
           - sheet = workbook.get_sheet(sheet_label):
                get a given sheet

        Useful sheet methods:
           - df = sheet.get_df_view(view_label)
        """
        self.sheet = data_sheet
        self._all_watched = None
        self.watched_sheets = set()

    def all_watched(self):
        if self._all_watched is None:
            self.update_watched_sheets()
        return self._all_watched

    def set_workbook(self, workbook):
        logger.debug('Plugin of sheet %s, set workbook: %s',
                     self.sheet.label, workbook.label \
                     if workbook is not None else 'None')
        self.workbook = workbook

    def after_workbook_load(self):
        self.update_watched_sheets()

    def update_watched_sheets(self):
        logger.debug('update_watched_sheets for plugin of %s', self.sheet.label)
        to_watch = self.sheets_to_watch()

        if len(to_watch) == 0:
            if not self._all_watched:
                self._all_watched = True
                self.sheet.invalidate_cached_views()
            return True

        if self.workbook is None or not self.workbook.logged_in:
            return False

        if self._all_watched:
            return True

        new_to_watch = []
        _all_watched = True
        for sheet_label in to_watch:
            if sheet_label not in self.watched_sheets:
                if self.workbook.has_sheet(sheet_label):
                    logger.debug('Plugin of %s should watch sheet %s',
                                 self.sheet.label, sheet_label)
                    sheet = self.workbook[sheet_label]
                    # if sheet is None:
                    #     raise SheetNotFound('Sheet %s not found in workbook %s',
                    #                         sheet_label, self.workbook.label)
                    if sheet is not None:
                        new_to_watch.append(sheet)
                else:
                    logger.debug('Plugin of %s cannot watch unavailable sheet %s',
                                 self.sheet.label, sheet_label)
                    _all_watched = False
        self._watch_sheets(new_to_watch)

        if _all_watched:
            for sheet_label in self.watched_sheets:
                if not self.workbook[sheet_label].plugin.all_watched():
                    logger.debug('Plugin of %s: watch chain not fully ok because of %s',
                                 self.sheet.label, sheet_label)
                    _all_watched = False
                    break

        if not self._all_watched and _all_watched:
            self._all_watched = True
            self.sheet.invalidate_cached_views()
        self._all_watched = _all_watched

    def _on_entry_append(self, sheet, entry_df=None):
        self.update(sheet, entry_df)

    def _on_entry_set(self, sheet, entry_idx):
        self.update(sheet, sheet.df.loc[[entry_idx]])

    def _on_entry_deletion(self, sheet, entry_df):
        self.update(sheet, entry_df, deletion=True)

    def _on_clear(self, sheet):
        self.update(sheet, None, clear=True)

    def _watch_sheets(self, sheets_to_watch):
        for sheet_to_watch in sheets_to_watch:
            logger.debug('Plugin of %s watches %s', self.sheet.label,
                         sheet_to_watch.label)
            # Watch update
            fu = LazyFunc(self._on_entry_append, sheet_to_watch)
            sheet_to_watch.notifier.add_watcher('appended_entry', fu)
            # Watch entry set
            fs = LazyFunc(self._on_entry_set, sheet_to_watch)
            sheet_to_watch.notifier.add_watcher('entry_set', fs)
            # Watch deletion
            fd = LazyFunc(self._on_entry_deletion, sheet_to_watch)
            sheet_to_watch.notifier.add_watcher('deleted_entry', fd)
            # Watch clear
            fc = LazyFunc(self._on_clear, sheet_to_watch)
            sheet_to_watch.notifier.add_watcher('cleared_data', fc)
            self.watched_sheets.add(sheet_to_watch.label)

    def show_index_in_ui(self):
        return False

    def access_level(self):
        return UserRole.VIEWER

    def get_property(self, property_name):
        """ Custom property """
        return None

    def views(self, base_views):
        """
        Return a dictionnary that maps a view label to a callable.
        The callable will be given the raw panda.Dataframe of the sheet and
        should return a transformed panda.Dataframe (view).

        Example:
            def views(self, base_views):
                # Keep default 'full' and 'latest' view and
                # add a John-specific one
                base_view.update({
                   'John' : lambda df: df[df.Staff=='John']
                })
                return base_views
        """
        return base_views

    def default_view(self):
        """
        The default view to be used by the sheet.
        Must be a label defined in views()

        Return None to keep the original default view.
        """
        return 'full'

    def view_validity(self, df, view):
        """
        Indicate if the given view is valid.
        Return a DataFrame with boolean values and the same shape as df
        """
        df_validity = pd.DataFrame(np.ones(df.shape, dtype=bool))
        df_validity.index = df.index
        df_validity.columns = df.columns
        return df_validity

    def sheets_to_watch(self):
        """
        Return a list of sheet labels to watch for changes (method update will
        be called when they change).
        Note that the associated sheet is always watched for changes
        """
        return []

    def update(self, sheet_source, changed_entry, deletion=False, clear=False):
        """
        Called when a watched sheet has been modified.
        Watched sheets consist of the associated sheet and
        sheets returned by sheets_to_watch
        """
        pass

    def action(self, entry_df, selected_column):
        """
        Called after clicking on a cell.
        By default, return a form to update the selected entry.

        Return: None | Form | html str | Plotter | svg str
        """
        label = '%s | update' % self.sheet.label
        return self.sheet.form_update_entry(entry_df.index.values[0]), label

    def hint(self, column, value):
        """
        Return hints to display icon, tooltips, background...
        Return a Hint object.
        Default Hint objects available are in piccel.Hints
        """
        return None

    @classmethod
    def get_code_str(cls):
        return (plugin_source_header + \
                strip_indent(inspect.getsource(cls)
                             .replace(cls.__name__, 'CustomSheetPlugin')))

class UserSheetPlugin(SheetPlugin):
    def active_view(self, df):
        latest = self.sheet.latest_update_df(df)
        return latest[latest['Status'] == 'active']

    def access_level(self):
        return UserRole.MANAGER

    def default_view(self):
        return 'latest'

    def views(self, base_views):
        base_views.update({'active' : self.active_view})
        return base_views

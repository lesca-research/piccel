import pandas as pd
import numpy as np

from piccel.core import LazyFunc, SheetNotFound

import logging
logger = logging.getLogger('piccel')


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

    def set_workbook(self, workbook):
        logger.debug('Plugin of sheet %s, set workbook: %s',
                     self.sheet.label, workbook.label \
                     if workbook is not None else 'None')
        self.workbook = workbook

    def check(self):
        pass

    def after_workbook_load(self):
        watched_sheets = []
        for sheet_label in self.sheets_to_watch():
            sheet = self.workbook[sheet_label]
            if sheet is None:
                raise SheetNotFound('Sheet %s not found in workbook %s',
                                    sheet_label, self.workbook.label)
            watched_sheets.append(sheet)
        self._watch_sheets(watched_sheets)

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

    def show_index_in_ui(self):
        return False

    def views(self, base_views):
        """
        Return a dictionnary that maps a view label to a callable.
        The callable will be given the raw panda.Dataframe of the sheet and
        should return a transformed panda.Dataframe (view).

        Example:
            def views(self, base_views):
                # Keep default 'raw' and 'latest' view and
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
        return 'raw'

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
        Watch sheets comprise the associated sheet and sheets defined by
        method sheets_to_watch
        """
        pass

    def action(self, entry_df, selected_column):
        """
        Called after clicking on a cell.
        By default, return a form to update the selected entry.

        Return: None | Form | html str | Plotter | svg str
        """
        label = '%s | update' % self.sheet
        return self.sheet.form_update_entry(entry_df.index.values[0]), label

    def hint(self, column, value):
        """
        Return hints to display icon, tooltips, background...
        Return a Hint object.
        Default Hint objects available are in piccel.Hints
        """
        return None

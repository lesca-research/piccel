import pandas as pd
import numpy as np

class SheetPlugin:

    def __init__(self, data_sheet, workbook=None):
        """
        workbook (WorkBook | None): workbook in which the sheet has been loaded.
        May be None if the sheet is stand-alone.

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
        self.workbook = workbook

    def sheet_index(self):
        """ Return index in the sheet list, for display order """
        return -1

    def compute(self):
        """
        Generate a DataFrame. Called only if sheet.dynamic_only == True
        """
        self.sheet.df = pd.DataFrame()

    def views(self):
        """
        Return a dictionnary that maps a view label to a callable.
        The callable will be given the raw panda.Dataframe of the sheet and
        should return a transformed panda.Dataframe (view).

        Example:
            def views(self):
                views = {
                   'Staff' : lambda df: df[df.staff=='John']
                }
                return views
        """
        return {}

    def default_view(self):
        """
        The default view to be used by the sheet.
        Must be a label defined in views()

        Return None to keep the original default view.
        """
        return None

    def view_validity(self, df, view):
        """
        Indicate if the given view is valid.
        Return a DataFrame with boolean values and the same shape as df
        """
        df_validity = pd.DataFrame(np.ones(df.shape, dtype=bool))
        df_validity.index = df.index
        df_validity.columns = df.columns
        return df_validity

    def update(self, sheet_source, changed_entry):
        """ Called when another sheet has been modified """
        pass

    def action(self, entry_df, selected_column):
        """
        Called after clicking on a cell.
        By default, return a form to update the selected entry.

        Return: None | Form | html str | Plotter | svg str
        """
        return self.sheet.form_update_entry(entry_df.index.values[0])

    def hints(self, df, view):
        """
        Return hints to display as icon and tooltips.
        Return a tuple of DataFrame (decorations, tooltip)
        *decorations* values are in:
            - Hint.NONE
            - Hint.WARNING
            - Hint.ERROR
            - Hint.OK
            - Hint.NOT_OK
        *tooltip* values are str
        """
        pass

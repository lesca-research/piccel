import pandas as pd
import numpy as np
class DataSheetPlugin:
    # TODO: refactor to allow seemless usage of DataSheetPlugin and
    # DynamicSheetPlugin
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
        df_validity = pd.DataFrame(np.zeros(df.shape, dtype=np.bool))
        df_validity.index = df.index
        df_validity.columns = df.columns
        return df_validity
    # def style(self)

    # def request_new_entry(self, column, row_df)
    #  Action = None | (sheet_label, {key:values}) # Important! form item key must be valid identifier!


class DynamicSheetPlugin:
    pass

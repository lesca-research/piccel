import pandas as pd
import numpy as np

from piccel.plugin_tools import conditional_set
from piccel.sheet_plugin import SheetPlugin

class CustomSheetPlugin(SheetPlugin):

    def __init__(self, data_sheet):
        """
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
        super(CustomSheetPlugin, self).__init__(data_sheet)

    def views(self, base_views):
        """
        Return a dictionnary that maps a view label to a callable.
        The callable will be given the raw panda.Dataframe of the sheet and
        should return a transformed panda.Dataframe (view).

        Example:
            def views(self, base_views):
                return base_views.update({
                    'Staff' : lambda df: df[df.staff=='John']
                    }
        """
        base_views = super(CustomSheetPlugin, self).views(base_views)
        return base_views

    def default_view(self):
        """
        The default view to be used by the sheet.
        Must be a label defined in views()

        Return None to keep the original default view.
        """
        return super(CustomSheetPlugin, self).default_view()

    def view_validity(self, df, view):
        """
        Indicate if the given view is valid.
        Return a DataFrame with boolean values and the same shape as df
        """
        return super(CustomSheetPlugin, self).view_validity(df, view)

    def hint(self, value):
        return super(CustomSheetPlugin, self).hint(value)

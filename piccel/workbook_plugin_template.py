from piccel.workbook_plugin import WorkBookPlugin

class CustomWorkBookPlugin(WorkBookPlugin):

    def __init__(self, workbook):
        super(WorkBookPlugin, self).__init__()

    def sheet_order(self):
        return []

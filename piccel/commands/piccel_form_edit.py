import sys
import logging
from optparse import OptionParser

from PyQt5.QtWidgets import QApplication

from piccel.form import FormEditor, FormEditorFileIO

logger = logging.getLogger('piccel')

def main():

    min_args = 1
    max_args = 1

    usage = 'usage: %prog [options] FORM_FILE'
    description = 'Run piccel form editor.'

    parser = OptionParser(usage=usage, description=description)

    parser.add_option('-v', '--verbose', dest='verbose',
                      metavar='VERBOSELEVEL',
                      type='int', default=0,
                      help='Amount of verbose: '\
                           '0 (NOTSET: quiet, default), '\
                           '50 (CRITICAL), ' \
                           '40 (ERROR), ' \
                           '30 (WARNING), '\
                           '20 (INFO), '\
                           '10 (DEBUG)')

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    app = QApplication(sys.argv)
    form_editor = FormEditor(FormEditorFileIO(args[0]))
    form_editor.show()
    sys.exit(app.exec_())

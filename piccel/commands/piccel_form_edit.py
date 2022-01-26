import sys
import logging
from optparse import OptionParser

from PyQt5.QtWidgets import QApplication

from piccel.form import FormFileEditor

logger = logging.getLogger('piccel')

def main():

    min_args = 0
    max_args = 1

    usage = 'usage: %prog [options] [FORM_FILE]'
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

    parser.add_option('-t', '--test', action='store_true', default=False)

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    form_fn = args[0] if len(args) == 1 else None
    app = QApplication(sys.argv)
    form_editor = FormFileEditor(form_fn)
    form_editor.show()
    if options.test:
        form_editor.test_form()
    sys.exit(app.exec_())

import sys
import logging
from optparse import OptionParser
import piccel

logger = logging.getLogger('piccel')

def main():

    min_args = 0
    max_args = 1

    usage = 'usage: %prog [options] [WORKBOOK_FILE | FORM_FILE]'
    description = 'Run piccel data input client.'

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

    parser.add_option('-u', '--user', help='User for workbook login')
    parser.add_option('-p', '--access-password',
                      help='Access password for workbook login')
    parser.add_option('-r', '--role-password',
                      help='Role-specific password for workbook login')

    parser.add_option('-f', '--refresh-rate', type='int', default=10000,
                      help='Refresh rate in milliseconds')

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    fn = args[0] if nba > 0 else None

    app = piccel.PiccelApp(sys.argv, fn, options.user,
                           options.access_password, options.role_password,
                           refresh_rate_ms=options.refresh_rate)
    app.show()
    sys.exit(app.exec_())

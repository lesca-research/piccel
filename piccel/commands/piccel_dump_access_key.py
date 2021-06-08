import sys
import os
import os.path as op
import logging
from optparse import OptionParser

from piccel import WorkBook, LocalFileSystem

logger = logging.getLogger('piccel')

import getpass

def main():

    min_args = 2
    max_args = 2

    usage = 'usage: %prog [options] WORKBOOK_FILE OUTPUT_KEY_FILE'
    description = 'Save the access key to a file'

    parser = OptionParser(usage=usage, description=description)

    parser.add_option('-v', '--verbose', dest='verbose', metavar='VERBOSELEVEL',
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

    cfg_fn, key_fn = args

    access_password = getpass.getpass("Access password:")
    filesystem = LocalFileSystem(op.dirname(cfg_fn))
    wb = WorkBook.from_configuration_file(cfg_fn, filesystem)
    wb.decrypt(access_password)
    wb.dump_access_key(key_fn)

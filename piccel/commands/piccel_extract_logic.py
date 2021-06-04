import sys
import os
import os.path as op
import logging
from datetime import datetime

from optparse import OptionParser

import piccel

logger = logging.getLogger('piccel')

def main():

    min_args = 1
    max_args = 1

    usage = 'usage: %prog [options] WORKBOOK_FILE'
    description = 'Extract forms and plugins from a workbook'

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
    # TODO: prompt for password instead of passing as option!
    parser.add_option('-p', '--access-password',
                      help='Access password for workbook login')
    parser.add_option('-r', '--role-password',
                      help='Role-specific password for workbook login')
    parser.add_option('-o', '--output-dir',
                      help='Folder where to extract workbook definitions')

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    cfg_fn  = args[0]

    filesystem = piccel.LocalFileSystem(op.dirname(cfg_fn))
    wb = piccel.WorkBook.from_configuration_file(cfg_fn, filesystem)
    wb.decrypt(options.access_password)
    wb.user_login(options.user, options.role_password, load_sheets=False)

    output_dir = options.output_dir
    if output_dir is None:
        output_dir = '%s_logic_%s' % \
            (wb.label, datetime.now().strftime('%Y_%m_%d_%Hh%M.%S'))
    assert(not op.exists(output_dir))
    os.makedirs(output_dir)

    sheet_folder = op.join(wb.data_folder, piccel.WorkBook.SHEET_FOLDER)
    for sheet_name in wb.filesystem.listdir(sheet_folder):
        output_sheet_folder = op.join(output_dir, sheet_folder, sheet_name)
        os.makedirs(output_sheet_folder)
        master_fn = op.join(sheet_folder, sheet_name, 'master.form')
        plugin_fn = op.join(sheet_folder, sheet_name,
                            'plugin_%s.py' % sheet_name)
        for fn in [master_fn, plugin_fn]:
            if wb.filesystem.exists(fn):
                wb.filesystem.copy_to_tmp(fn, decrypt=True,
                                          tmp_dir=output_sheet_folder)

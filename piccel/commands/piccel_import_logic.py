import sys
import os
import os.path as op
import logging
from datetime import datetime
import shutil
from optparse import OptionParser

import piccel

logger = logging.getLogger('piccel')

def main():

    min_args = 3
    max_args = 3

    usage = 'usage: %prog [options] WORKBOOK_FILE LOGIC_FOLDER BACKUP_DIR'
    description = 'Import forms and plugins into a workbook'

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

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    cfg_fn, logic_dir, backup_dir  = args
    assert(op.exists(backup_dir))

    filesystem = piccel.LocalFileSystem(op.dirname(cfg_fn))
    wb = piccel.WorkBook.from_configuration_file(cfg_fn, filesystem)
    wb.decrypt(options.access_password)
    wb.user_login(options.user, options.role_password, load_sheets=False)

    shutil.copytree(op.join(wb.filesystem.root_folder, wb.data_folder),
                    op.join(backup_dir, '%s_%s' % \
                            (wb.label,
                             datetime.now().strftime('%Y_%m_%d_%Hh%M.%S'))))

    sheets_folder = op.join(wb.data_folder, piccel.WorkBook.SHEET_FOLDER)
    for sheet_name in wb.filesystem.listdir(sheets_folder):
        master_rfn = op.join(sheets_folder, sheet_name, 'master.form')
        plugin_rfn = op.join(sheets_folder, sheet_name,
                             'plugin_%s.py' % sheet_name)
        for rfn in [master_rfn, plugin_rfn]:
            wb.filesystem.import_file(op.join(logic_dir, rfn), rfn,
                                      overwrite=True)

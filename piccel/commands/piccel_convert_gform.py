import logging
from optparse import OptionParser

from piccel import import_gform_file

logger = logging.getLogger('piccel')

def main():

    min_args = 3
    max_args = 3

    usage = 'usage: %prog [options] GOOGLE_FORM_JSON_FILE PICCEL_FORM_FILE LANGUAGE'
    description = 'Import a google form (json format) into a piccel form. '\
        'If PICCEL_FORM_FILE exists, the google form structure must align '\
        'with it and content will be updated by language. Use option --overwrite '\
        'to replace any existing piccel form (no language update)'

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
    # TODO: overwrite option
    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        return 1

    # TODO: overwrite option
    import_gform_file(*args)

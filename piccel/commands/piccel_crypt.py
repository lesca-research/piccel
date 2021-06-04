import os
import os.path as op
import sys
from piccel import Encrypter
from optparse import OptionParser
import getpass
import logging
import json

logger = logging.getLogger('piccel')

def encrypt_cmd():
    usage = 'usage: %prog [options] INPUT_FILE OUTPUT_RYPTED_FILE'
    description = 'Encrypt a given file using Fernet'

    encrypt(*parse_cmd(usage, description))

def encrypt(in_file, out_file, pwd):
    pwd = ask_pwd(pwd)
    salt_bytes = os.urandom(32)
    encrypter = Encrypter(pwd, salt_bytes)

    with open(in_file, 'r') as fin:
        content_str = fin.read()
        crypted_content_str = encrypter.encrypt_str(content_str)

    output = {
        'salt' : salt_bytes.hex(),
        'crypted_content' :  crypted_content_str
    }
    with open(out_file, 'w') as fout:
        json.dump(output, fout)

def decrypt_cmd():
    usage = 'usage: %prog [options] INPUT_CRYPTED_FILE OUTPUT_DECRYPTED_FILE'
    description = 'Decrypt a given file using Fernet'
    decrypt(*parse_cmd(usage, description))

import tempfile
def decrypt_to_tmp(in_file, pwd=None):
    tmp_fn = op.join(tempfile.mkdtemp(), 'decrypted')
    return tmp_fn, decrypt(in_file, tmp_fn, pwd)

def decrypt(in_file, out_file, pwd):
    pwd = ask_pwd(pwd)
    with open(in_file, 'r') as fin:
        json_content = json.load(fin)
        salt_bytes = bytes.fromhex(json_content['salt'])
        encrypter = Encrypter(pwd, salt_bytes)
        crypted_content_str = json_content['crypted_content']
        decrypted_content_str = encrypter.decrypt_to_str(crypted_content_str)

    with open(out_file, 'w') as fout:
        fout.write(decrypted_content_str)
    return pwd

def ask_pwd(pwd):
    if pwd is None:
        pwd = getpass.getpass()
    return pwd

def parse_cmd(usage, description):
    min_args = 2
    max_args = 2

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

    parser.add_option('-p', '--password')
    parser.add_option('-f', '--force', action='store_true',
                      default=False)

    (options, args) = parser.parse_args()
    logger.setLevel(options.verbose)

    nba = len(args)
    if nba < min_args or (max_args >= 0 and nba > max_args):
        parser.print_help()
        sys.exit(1)

    in_file, out_file = args
    pwd = options.password
    force = options.force

    if op.exists(out_file) and not force:
        logger.error('Output file %s exists. Use -f option to overwrite',
                     out_file)
        sys.exit(1)

    if pwd is not None:
        logger.warning('Providing password as a command argument is unsecure')

    return in_file, out_file, pwd

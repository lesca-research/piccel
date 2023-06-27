


"""
import secrets
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# Generate a random secret key (AES256 needs 32 bytes)
key = secrets.token_bytes(32)

# Encrypt a message
nonce = secrets.token_bytes(12)  # GCM mode needs 12 fresh bytes every time
ciphertext = nonce + AESGCM(key).encrypt(nonce, b"Message", b"")

# Decrypt (raises InvalidTag if using wrong key or corrupted ciphertext)
msg = AESGCM(key).decrypt(ciphertext[:12], ciphertext[12:], b"")
"""
import json

from getpass import getpass
import secrets
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from hashlib import scrypt
import base64

from ..core import if_none
from ..logging import logger, debug2, debug3

def derive_key(password_str, salt_bytes):
    return scrypt(password_str.encode(), salt=salt_bytes,
                  n=16384, r=8, p=1, dklen=32)

class InvalidSaltSize(Exception): pass

class SymmetricAESGCMEncrypter:

    KEY_SALT_SIZE = 128

    def __init__(self, password, key_salt_bytes=None, get_password=getpass):
        self.get_password = get_password
        if password is None:
            password = self.get_password()
        self.key_salt_bytes = \
            if_none(key_salt_bytes,
                    secrets.token_bytes(SymmetricAESGCMEncrypter.KEY_SALT_SIZE))
        if len(self.key_salt_bytes) != SymmetricAESGCMEncrypter.KEY_SALT_SIZE:
            raise InvalidSaltSize('Size of salt must be %s' %
                                  SymmetricAESGCMEncrypter.KEY_SALT_SIZE)

        self.gcm = AESGCM(derive_key(password, self.key_salt_bytes))

    def set_password_input_func(self, password_func):
        self.get_password = password_func

    def encrypt_str(self, content_str):
        key_salt_hex = self.key_salt_bytes.hex()
        # Save key salt to be able to decrypt in a self-contained manner
        nonce = secrets.token_bytes(12)
        return json.dumps({
            'key_salt_hex' : key_salt_hex,
            'nonce_hex' : nonce.hex(),
            'crypted_content_hex' : (self.gcm.encrypt(nonce, content_str.encode(),
                                                      None)
                                     .hex())
        })

    def decrypt_to_str(self, crypted_str):
        content = json.loads(crypted_str)

        if 'key_salt_hex' not in content:
            raise IOError('Bad format')

        if self.key_salt_bytes.hex() != content['key_salt_hex']:
            logger.warning('Different key salt found in content to decrypt. '\
                           'Encryption key needs to be built again.')
            if self.get_password is None:
                raise IOError('Cannot decrypt because cannot get password again')
            else:
                loaded_key_salt_bytes = bytes.fromhex(content['key_salt_hex'])
                gcm = AESGCM(derive_key(self.get_password(),
                                        loaded_key_salt_bytes))
        else:
            gcm = self.gcm

        return gcm.decrypt(bytes.fromhex(content['nonce_hex']),
                           bytes.fromhex(content['crypted_content_hex']),
                           None).decode()

import tempfile
from pyfakefs.fake_filesystem_unittest import TestCase


class TestEncryption(TestCase):

    def test_crypter(self):
        password = "password"
        salt_bytes = secrets.token_bytes(SymmetricAESGCMEncrypter.KEY_SALT_SIZE)
        crypter = SymmetricAESGCMEncrypter(password, salt_bytes)
        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

    def test_auto_salt(self):
        password = "password"
        crypter = SymmetricAESGCMEncrypter(password)
        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

    def test_password_input(self):
        password = "password"
        def give_pwd():
            return password
        crypter = SymmetricAESGCMEncrypter(None, get_password=give_pwd)
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str('message')),
                         'message')

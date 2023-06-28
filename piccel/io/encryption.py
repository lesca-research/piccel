


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

    def __init__(self, get_password=getpass):
        self.get_password = get_password
        self.gcm = None

    @classmethod
    def new(cls, password, key_salt_bytes=None, get_password=getpass):
        encrypter = SymmetricAESGCMEncrypter(get_password=lambda: password)
        encrypter._insure_init(key_salt_bytes)
        encrypter.set_password_input_func(get_password)
        return encrypter

    def set_password_input_func(self, password_func):
        self.get_password = password_func

    def _insure_init(self, key_salt_bytes=None):

        if (key_salt_bytes is not None and
            len(key_salt_bytes) != SymmetricAESGCMEncrypter.KEY_SALT_SIZE):
            raise InvalidSaltSize('Size of salt must be %s' %
                                  SymmetricAESGCMEncrypter.KEY_SALT_SIZE)

        if self.gcm is None: # No previous key init
            self.key_salt_bytes = \
                if_none(key_salt_bytes,
                        secrets.token_bytes(SymmetricAESGCMEncrypter.KEY_SALT_SIZE))
            self.gcm = AESGCM(derive_key(self.get_password(), self.key_salt_bytes))
        else:
            if (key_salt_bytes is not None and
                self.key_salt_bytes != key_salt_bytes):
                logger.warning('Different key salt found in content to decrypt')
                self.key_salt_bytes = key_salt_bytes
                self.gcm = AESGCM(derive_key(self.get_password(),
                                             self.key_salt_bytes))

    def encrypt_str(self, content_str):
        self._insure_init()
        # Save key salt to be able to decrypt in a self-contained manner
        nonce = secrets.token_bytes(12)
        return json.dumps({
            'key_salt_hex' : self.key_salt_bytes.hex(),
            'nonce_hex' : nonce.hex(),
            'crypted_content_hex' : (self.gcm.encrypt(nonce, content_str.encode(),
                                                      None)
                                     .hex())
        })

    def decrypt_to_str(self, crypted_str):
        content = json.loads(crypted_str)
        self._insure_init(bytes.fromhex(content['key_salt_hex']))

        return self.gcm.decrypt(bytes.fromhex(content['nonce_hex']),
                                bytes.fromhex(content['crypted_content_hex']),
                                None).decode()

import tempfile
from pyfakefs.fake_filesystem_unittest import TestCase

class TestEncryption(TestCase):

    def test_crypter(self):
        password = "password"
        salt_bytes = secrets.token_bytes(SymmetricAESGCMEncrypter.KEY_SALT_SIZE)
        crypter = SymmetricAESGCMEncrypter.new(password)
        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

    def test_auto_salt(self):
        password = "password"
        crypter = SymmetricAESGCMEncrypter.new(password)
        message = 'Secret message!!'
        self.assertEqual(crypter.decrypt_to_str(crypter.encrypt_str(message)),
                         message)

    def test_password_input(self):
        password = "password"
        def give_pwd():
            return password
                
        crypter1 = SymmetricAESGCMEncrypter(give_pwd)
        crypted_msg = crypter1.encrypt_str('message')

        crypter2 = SymmetricAESGCMEncrypter(give_pwd)
        self.assertEqual(crypter2.decrypt_to_str(crypted_msg), 'message')
        

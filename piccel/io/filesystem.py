import os
import os.path as op
import tempfile

from pyfakefs.fake_filesystem_unittest import TestCase

from ..logging import logger, debug2, debug3

def rm_content(path):
    for root, dirs, files in os.walk(path):
        for bfn in files:
            os.unlink(op.join(root, bfn))
        for d in dirs:
            shutil.rmtree(op.join(root, d))

class LocalFileSystem:
    """
    Save / Load strings to/from files using encryption.
    Keep track of file modifications based on stats.
    """
    def __init__(self, root_folder, encrypter=None, track_changes=False):
        self.root_folder = op.normpath(root_folder)
        self.encrypter = encrypter
        self.enable_track_changes(track_changes)

    def is_encrypted(self):
        return self.encrypter is not None

    def enable_track_changes(self, state=True):
        self.track_changes = state
        self.current_stats = {}

    def file_stats(self, subfolder=''):
        stats = {}
        if self.track_changes:
            root = op.join(self.root_folder, subfolder)
            for wroot, dirs, files in os.walk(root):
                for bfn in files:
                    rdir = op.relpath(wroot, self.root_folder)
                    fn = op.normpath(op.join(rdir, bfn))
                    stats[fn] = self.file_size(fn)
        return stats

    def external_changes(self, path=None):
        modifications = []
        additions = []
        deletions = []
        if path is not None:
            walk_root = op.join(self.root_folder, path)
        else:
            walk_root = self.root_folder
        if self.track_changes:
            logger.debug('Check tracked changes in %s', walk_root)
            for wroot, dirs, files in os.walk(walk_root):
                for bfn in files:
                    rdir = op.relpath(wroot, self.root_folder)
                    fn = op.normpath(op.join(rdir, bfn))
                    if fn not in self.current_stats:
                        additions.append(fn)
                    elif self.current_stats[fn] != self.file_size(fn):
                        modifications.append(fn)
            deletions = [f for f in self.current_stats if not self.exists(f)]
        return modifications, additions, deletions

    def accept_changes(self, modifications=None, additions=None, deletions=None):
        if self.track_changes:
            modifications = modifications if modifications is not None else []
            additions = additions if additions is not None else []
            deletions = deletions if deletions is not None else []
            for fn in modifications+additions:
                self.current_stats[fn] = self.file_size(fn)
            for fn in deletions:
                self.current_stats.pop(fn)

    def accept_all_changes(self, subfolder=''):
        if subfolder == '':
            self.current_stats = {}
        self.current_stats.update(self.file_stats(subfolder=subfolder))

    def change_dir(self, folder, track_changes=False):
        """ Note: change tracking will be reset """
        if not self.exists(folder):
            raise IOError('%s does not exist' % folder)
        logger.debug('Create new filesystem with root %s' % folder)
        return LocalFileSystem(op.join(self.root_folder, folder),
                               self.encrypter, track_changes)

    def clone(self):
        return LocalFileSystem(self.root_folder, self.encrypter,
                               self.track_changes)

    def set_encrypter(self, encrypter):
        self.encrypter = encrypter

    def unset_encrypter(self):
        self.encrypter = None

    def exists(self, fn):
        return op.exists(op.join(self.root_folder, fn))

    def is_file(self, fn):
        return op.isfile(op.join(self.root_folder, fn))

    def file_size(self, fn):
        return op.getsize(op.join(self.root_folder, fn))

    def makedirs(self, folder):
        full_folder = op.join(self.root_folder, folder)
        if op.exists(full_folder):
            logger.debug('Folder %s already exists', full_folder)
            return
        logger.debug('Create folder %s', full_folder)
        os.makedirs(full_folder)
        # assert(op.exists(full_folder))

    def test_write_access(self):
        success = True
        try:
            self.save('test_write', '')
        except Exception as e:
            logger.error('Cannot write to %s, exception: %s',
                         self.root_folder, e)
            success = False
        else:
            self.remove('test_write')
        return success

    def full_path(self, fn):
        return op.join(self.root_folder, fn)

    def listdir(self, folder, list_folders_only=False):
        afolder = op.join(self.root_folder, folder)
        predicate = (lambda e : op.isdir(op.join(afolder, e)) \
                     if list_folders_only else lambda e : True)
        return [e for e in os.listdir(afolder) if predicate(e)]

    def dir_is_empty(self, folder):
        try:
            next(iter(os.scandir(op.join(self.root_folder, folder))))
        except StopIteration:
            return True
        return False

    def rmtree(self, folder):
        full_folder = op.join(self.root_folder, folder)
        if not op.exists(full_folder):
            logger.debug2('rmtree: Folder %s does not exist', full_folder)
            return

        for wroot, dirs, files in os.walk(op.join(self.root_folder, folder)):
            for bfn in files:
                rdir = op.relpath(wroot, self.root_folder)
                fn = op.normpath(op.join(rdir, bfn))
                if self.track_changes:
                    self.current_stats.pop(fn)

        logger.debug2('Remove folder %s', full_folder)
        shutil.rmtree(full_folder)

    def copy_to_tmp(self, fn, decrypt=False, tmp_dir=None, dest_afn=None):
        """ Return destination temporary file """
        if dest_afn is None:
            if tmp_dir is None:
                tmp_dir = tempfile.mkdtemp()
            tmp_fn = op.join(tmp_dir, op.basename(fn))
        else:
            tmp_fn = dest_afn
        if not decrypt:
            shutil.copy(op.join(self.root_folder, fn), tmp_fn)
        else:
            assert(self.encrypter is not None)
            logger.warning('Copying UNCRYPTED %s to %s', fn, tmp_fn)
            content_str = self.load(fn)
            with open(tmp_fn, 'w') as fout:
                fout.write(content_str)
        return tmp_fn

    def import_file(self, src_fn, dest_rfn, overwrite=False):
        with open(src_fn, 'r') as fin:
            content = fin.read()
        self.save(dest_rfn, content, overwrite=overwrite)

    def remove(self, fn):
        logger.debug2('Remove file %s', fn)
        os.remove(op.join(self.root_folder, fn))
        if self.track_changes:
            self.current_stats.pop(fn)

    def remove_all(self, path):
        logger.debug2('Remove all files and subdirs in %s', path)
        rm_content(op.join(self.root_folder, path))
        if self.track_changes:
            self.current_stats = {}

    def save(self, fn, content_str='', overwrite=False, crypt=True):
        fn = op.normpath(fn)
        afn = op.join(self.root_folder, fn)
        logger.debug2('Filesystem - save to abs fn: %s', afn)
        logger.debug2('Filesystem - working directory: %s', os.getcwd())
        if self.encrypter is not None and crypt:
            content_str = self.encrypter.encrypt_str(content_str)

        if op.exists(afn) and not overwrite:
            raise FileExistsError(afn)

        with open(afn, 'w') as fout:
            fout.write(content_str)

        if self.track_changes:
            self.current_stats[fn] = self.file_size(fn)

    def load(self, fn, crypted_content=True):
        afn = op.join(self.root_folder, fn)

        with open(afn, 'r') as fin:
            content_str = fin.read()

        if crypted_content and self.encrypter is not None:
            content_str = self.encrypter.decrypt_to_str(content_str)
        return content_str


class TestLocalFileSystem(TestCase):
    
    def setUp(self):
        self.setUpPyfakefs()
        self.tmp_dir = tempfile.mkdtemp()

    def touch_file(self, fn, content=''):
        with open(op.join(self.tmp_dir, fn), 'w') as fin:
            fin.write(content)

    def test_io(self):
        fs = LocalFileSystem(self.tmp_dir)
        fs.save('test.txt', 'content')
        self.assertFalse(fs.is_encrypted())
        self.assertEqual(fs.load('test.txt'), 'content')
        
    def test_encrytion(self):
        class Encrypter:
            def encrypt_str(self, s):
                return s[::-1]
            def decrypt_to_str(self, s):
                return s[::-1]
        fs = LocalFileSystem(self.tmp_dir, encrypter=Encrypter())
        fs.save('test.txt', 'content')
        self.assertTrue(fs.is_encrypted())
        self.assertEqual(fs.load('test.txt'), 'content')

            
    def test_track_new_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(adds, ['yy.cc', 'xx.cc'])
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(dels), 0)
        filesystem.accept_all_changes()
        
        self.touch_file('new.cc')
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(adds, ['new.cc'])
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(dels), 0)

        filesystem.accept_changes(additions=['new.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_track_modified_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        filesystem.accept_changes(additions=['yy.cc'])
        self.touch_file('yy.cc', 'hey')

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(mods, ['yy.cc'])
        self.assertEqual(adds, ['xx.cc'])
        self.assertEqual(len(dels), 0)

        filesystem.accept_changes(modifications=['yy.cc', 'xx.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_track_deleted_files(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        filesystem.accept_all_changes()
        os.remove(op.join(self.tmp_dir, 'yy.cc'))

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(dels, ['yy.cc'])

        filesystem.accept_changes(deletions=['yy.cc'])
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(dels), 0)

    def test_internal_tracking(self):
        self.touch_file('yy.cc')
        self.touch_file('xx.cc')
        filesystem = LocalFileSystem(self.tmp_dir, track_changes=True)
        filesystem.accept_all_changes()
        filesystem.remove('xx.cc')

        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

        filesystem.save('gg.cc', 'yep')
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

        filesystem.save('yy.cc', 'yep', overwrite=True)
        mods, adds, dels = filesystem.external_changes()
        self.assertEqual(len(mods), 0)
        self.assertEqual(len(adds), 0)
        self.assertEqual(len(adds), 0)

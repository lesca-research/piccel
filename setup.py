#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import sys
import os
import os.path as op
from glob import glob
from setuptools import setup, find_packages
import subprocess

version = {}
with open("piccel/version.py") as fp:
    exec(fp.read(), version)

here = op.abspath(op.dirname(__file__))

short_description = 'Collaborative data collection tool'
long_description = short_description

def replace_in_file(fn, s, repl):
    with open(fn) as fin:
        content = fin.read()
    content = content.replace(s, repl)
    with open(fn, 'w') as fout:
        fout.write(content)

def make_resources():
    print('Make resources before setup')
    ui_module_path = op.join('piccel', 'ui', 'generated')
    if not op.exists(ui_module_path):
        os.makedirs(ui_module_path)
        with open(op.join(ui_module_path, '__init__.py'), 'w') as fout:
            fout.write('')
    try:
        dest_py_fn = op.join(ui_module_path, 'resources_rc.py')
        rsrc_module_name = op.splitext(op.basename(dest_py_fn))[0]
        cmd = ['pyrcc5', op.join('resources', 'resources.qrc'), '-o',
               dest_py_fn]
        subprocess.run(cmd)

        for ui_fn in glob(op.join('resources', '*.ui')):
            dest_py_fn = op.join(ui_module_path,
                                 '%s_ui.py' % op.splitext(op.basename(ui_fn))[0 ])
            cmd = ['pyuic5',  '-x', ui_fn, '-o', dest_py_fn]
            subprocess.run(cmd)
            replace_in_file(dest_py_fn,
                            'import %s' % rsrc_module_name,
                            'from .%s import *' % rsrc_module_name)
    except FileNotFoundError:
        print('pyrcc5 command (PyQT5) not found')
        sys.exit(1)

make_resources()

setup(name='piccel', version=version['__version__'],
      description=short_description,
      long_description=long_description,
      author='Thomas Vincent', license='MIT',
      classifiers=['Development Status :: 3 - Alpha',
                   'Intended Audience :: Science/Research',
                   'Intended Audience :: Information Technology',
                   'Intended Audience :: End Users/Desktop',
                   'License :: OSI Approved :: MIT License',
                   'Environment :: X11 Applications :: Qt'
                   'Natural Language :: English',
                   'Natural Language :: French',
                   'Operating System :: POSIX :: Linux',
                   'Operating System :: MacOS',
                   'Operating System :: Microsoft :: Windows',
                   'Topic :: Office/Business :: Groupware',
                   'Topic :: Database',
                   'Programming Language :: Python :: 3.8',],
      keywords='piccel spreadsheet form data capture encryption cloud',
      packages=find_packages(exclude=['test']),
      python_requires='>=3',
      install_requires=['packaging', 'numpy', 'pandas<1.0.6', 'cryptography', 'appdirs',
                        'beautifulsoup4', 'bcrypt', 'html5lib'],
      extras_require={"PDF":  ['weasyprint', 'PyPDF2']},
      entry_points={
          'console_scripts': [
              'piccel = piccel.commands.piccel:main',
              'piccel_extract_logic = piccel.commands.piccel_extract_logic:main',
              'piccel_convert_gform = piccel.commands.piccel_convert_gform:main',
              'piccel_import_logic = piccel.commands.piccel_import_logic:main',
              'piccel_form_edit = piccel.commands.piccel_form_edit:main',
              'piccel_decrypt = piccel.commands.piccel_crypt:decrypt_cmd',
              'piccel_encrypt = piccel.commands.piccel_crypt:encrypt_cmd',
              'piccel_test_widget = piccel.commands.piccel_test_widget:main',
              'piccel_dump_access_key = piccel.commands.piccel_dump_access_key:main'
          ],
      })

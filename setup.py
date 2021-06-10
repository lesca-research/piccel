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

def make_resources():
    ui_module_path = op.join('piccel', 'ui', 'generated')
    if not op.exists(ui_module_path):
        os.makedirs(ui_module_path)
    try:
        for ui_fn in glob(op.join('resources', '*.ui')):
            dest_py_fn = op.join(ui_module_path,
                                 '%s_ui.py' % op.splitext(op.basename(ui_fn))[0])
            cmd = ['pyuic5', '-x', ui_fn, '-o', dest_py_fn]
            subprocess.run(cmd)
        dest_py_fn = op.join(ui_module_path, 'resources.py')
        cmd = ['pyrcc5', op.join('resources', 'resources.qrc'), '-o', dest_py_fn]
        subprocess.run(cmd)
    except FileNotFoundError:
        print('PyQT5 not found')
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
                   'Environment :: Console',
                   'Natural Language :: English',
                   'Operating System :: OS Independent',
                   'Programming Language :: Python :: 3.8',],
      keywords='piccel spreadsheet data collection encryption',
      packages=find_packages(exclude=['test']),
      python_requires='>=3',
      install_requires=['numpy', 'pandas', 'cryptography', 'appdirs',
                        'beautifulsoup4', 'bcrypt'],
      extras_require={"PDF":  ['weasyprint', 'PyPDF2']},
      entry_points={
          'console_scripts': [
              'piccel = piccel.commands.piccel:main',
              'piccel_extract_logic = piccel.commands.piccel_extract_logic:main',
              'piccel_import_logic = piccel.commands.piccel_import_logic:main',
              'piccel_decrypt = piccel.commands.piccel_crypt:decrypt_cmd',
              'piccel_encrypt = piccel.commands.piccel_crypt:encrypt_cmd',
              'piccel_dump_access_key = piccel.commands.piccel_dump_access_key:main'
          ],
      })

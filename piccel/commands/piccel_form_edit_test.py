#!/usr/bin/env python3
import sys
from PyQt5.QtWidgets import QApplication

from piccel import NewPasswordDialog

def main():
    app = QApplication(sys.argv)
    print('New password:', NewPasswordDialog.ask())

    sys.exit(app.exec_())

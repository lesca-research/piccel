#!/usr/bin/env python3
import sys
import time

from PyQt5.QtCore import QRunnable, Qt, QThreadPool, pyqtSignal

from PyQt5.QtWidgets import (
    QApplication,
    QLabel,
    QMainWindow,
    QPushButton,
    QVBoxLayout,
    QWidget,
    QDialog,
    QVBoxLayout,
    QProgressBar,
    QMessageBox
)

def job(progression):

    progression('Start job...', 1)
    time.sleep(1)
    progression('In the middle of the job...', 50)
    time.sleep(1)
    progression('Job finished!', 100)

class JobWrap(QRunnable):
    progressionChanged = pyqtSignal()

    def __init__(self, job):
        super().__init__()
        self.job = job

    def run(self):
        self.job.run(progression=self.progression)

    def progression(self, message, value):
        self.progressionChanged.emit(message, value)

class ProgressBarDialog(QDialog):

    def __init__(self, title, parent=None):
        super(QDialog, self).__init__(parent)
        self.setWindowTitle(title)

        self.label = QLabel('Waiting to start...', parent=self)
        self.progress_bar = QProgressBar(parent=self)

        self.vlayout = QVBoxLayout(self)
        self.vlayout.addWidget(self.label)
        self.vlayout.addWidget(self.progress_bar)

    def progression(self):
        pass

from piccel import DictStrEditorWidget


class MainWindow(QMainWindow):

    closed = pyqtSignal()

    def __init__(self):
        super().__init__()
        adict = {'k1' : 'value',
                 'is_bueno' : 'Yep'}
        self.editor = DictStrEditorWidget(adict)

    def closeEvent(self, event):
        if QMessageBox.question(self, 'Closing', 'Really close?') == \
           QMessageBox.Yes:
            event.accept()
            print(self.editor.get_dict())
            self.closed.emit()
        else:
            event.ignore()

    def show(self):
        super().show()
        self.editor.show()

def main():
    app = QApplication(sys.argv)

    if 0:
        progress_bar = ProgressBarDialog()
        job_thread = JobWrap(partial(job, progress_bar_dialog))
        pool = QThreadPool.globalInstance()
        pool.start(job_thread)
    win = MainWindow()
    win.show()
    sys.exit(app.exec_())

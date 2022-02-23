#!/usr/bin/env python3
import sys
import time

from PyQt5.QtCore import QRunnable, Qt, QThreadPool, pyqtSignal

#import PyQt5.QtWidgets as qtws
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
    QMessageBox,
    QTextEdit
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


class DictEditorMainWindow(QMainWindow):

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


content_html = \
"""<!DOCTYPE html>
<html>
<head>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
body {
  margin: 0;
  font-family: Arial, Helvetica, sans-serif;
}

.top-container {
  background-color: #f1f1f1;
  padding: 30px;
  text-align: center;
}

.header {
  padding: 10px 16px;
  background: #ed1b29;
  color: #ffffff;
  position: fixed;
  top: 0;
  width: 100%;
}

th {
  padding-top: 5px;
}

.content {
  padding-top: 100px;
}

</style>
</head>
<body>

<div class="header" id="subject_header">
  <h2 id="participant_title">CE0001</h2>
</div>

<div class="content" id="content">
<div class="progress_note_entry" id="progress_note_entry_template">
  <p>
<table>
  <tr>
    <th align="left">Context:</th>
  </tr>
  <tr>
    <td id="context" align="left">eval</td>
  </tr>
</table>
<table>
  <tr>
    <th align="left">Timestamp:</th>
  </tr>
  <tr>
    <td id="timestamp" align="left">20 octobre 2020 &agrave; 10h00</td>
  </tr>
</table>
  </p>
</div>
</div>
</body>
</html>
"""
from piccel.ui.main_qss import progress_note_report_style

content_html = \
"<style>%s</style>" % progress_note_report_style + \
"""
<p>
 <table>
  <tr class="report_odd_row">
   <th align="left" >Context</th>
   <td align="left">eval</td>
  </tr>
  <tr>
  <th align="left">Timestamp</th>
    <td id="timestamp" align="left">20 octobre 2020 &agrave; 10h00</td>
  </tr>
  <tr class="report_odd_row">
  <th align="left">Staff</th>
    <td id="timestamp" align="left">Jean Bon</td>
  </tr>
 </table>
</p>
"""

from piccel import ReportWidget
from piccel import ui
from piccel.plugin_tools import ProgressNoteEntry, ParticipantProgressNotes
from datetime import datetime

def main():
    app = QApplication(sys.argv)

    if 0:
        progress_bar = ProgressBarDialog()
        job_thread = JobWrap(partial(job, progress_bar_dialog))
        pool = QThreadPool.globalInstance()
        pool.start(job_thread)
    elif 0:
        win = DictEditorMainWindow()
        win.show()

    app.setStyle('Fusion')
    app.setStyleSheet(ui.main_qss.main_style)

    pns = ParticipantProgressNotes('CE0001', '2022/02/22')
    pns.add(ProgressNoteEntry(datetime.now(),
                              'me',
                              'General',
                              {'Consent' : 'Ok', 'Tech_Tuto' : 'Yep'},
                              [('Details 1', 'looooon details........'),
                               ('Review', 'It was fine in the end')]))

    pns.add(ProgressNoteEntry(datetime.now(),
                              'me',
                              'PreScreening',
                              {'Available' : 'Yes', 'Eligible' : 'Yep'},
                              [('Details', 'Sooo looooon prescr details........')]))

    report = pns.to_report('Project Common - {Participant_ID}')

    print(report.content)
    report = ReportWidget(report.content, report.header, report.footer)
    report.show()
    sys.exit(app.exec_())

from PyQt5 import QtCore, QtGui, QtWidgets

def show_critical_message_box(msg, detailed_text=None):
    message_box = QtWidgets.QMessageBox()
    message_box.setIcon(QtWidgets.QMessageBox.Critical)
    message_box.setText(msg)
    if detailed_text is not None:
        message_box.setDetailedText(detailed_text)
    message_box.exec_()

def show_info_message_box(msg):
    message_box = QtWidgets.QMessageBox()
    message_box.setText(msg)
    message_box.exec_()

class TextBoxDialog(QtWidgets.QDialog):
    def __init__(self, text, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)
        QBtn = QtWidgets.QDialogButtonBox.Ok
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)

        self.message_widget = QtWidgets.QTextEdit(text)
        self.message_widget.setReadOnly(True)

        self.layout = QtWidgets.QVBoxLayout()
        self.layout.addWidget(self.message_widget)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

def show_text_box(msg):
    TextBoxDialog(msg).exec_()

class ListSelectDialog(QtWidgets.QDialog):
    def __init__(self, choices, title=None, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)

        self.setWindowTitle(title if title is not None else "Select")

        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        self.listWidget = QtWidgets.QListWidget()
        for choice in choices:
            self.listWidget.addItem(QtWidgets.QListWidgetItem(choice))

        self.layout = QtWidgets.QVBoxLayout()
        self.layout.addWidget(self.listWidget)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

    def get_choice(self):
        selection = self.listWidget.selectedItems()
        if len(selection) > 0:
            return selection[0].text()
        else:
            return None

class FocusTextEdit(QtWidgets.QPlainTextEdit):
    """
    A TextEdit editor that sends editingFinished events
    when the text was changed and focus is lost.
    source: https://gist.github.com/hahastudio/4345418
    """

    editingFinished = QtCore.pyqtSignal()
    receivedFocus = QtCore.pyqtSignal()

    def __init__(self, parent):
        super(FocusTextEdit, self).__init__(parent)
        self._changed = False
        self.setTabChangesFocus( True )
        self.textChanged.connect( self._handle_text_changed )

    def focusInEvent(self, event):
        super(FocusTextEdit, self).focusInEvent( event )
        self.receivedFocus.emit()

    def focusOutEvent(self, event):
        if self._changed:
            self.editingFinished.emit()
        super(FocusTextEdit, self).focusOutEvent( event )

    def _handle_text_changed(self):
        self._changed = True

    def setTextChanged(self, state=True):
        self._changed = state


class PasswordEdit(QtWidgets.QLineEdit):

    def __init__(self, parent=None):
        super(PasswordEdit, self).__init__(parent=parent)

        self.visible_icon = QtGui.QIcon(':/icons/visible_icon')
        self.non_visible_icon = QtGui.QIcon(':/icons/non_visible_icon')

        self.setEchoMode(QtWidgets.QLineEdit.Password)
        self.toggle_action = self.addAction(self.visible_icon,
                                            QtWidgets.QLineEdit.TrailingPosition)
        self.toggle_action.triggered.connect(self.on_toggle)
        self.password_shown = False

    def on_toggle(self):
        if not self.password_shown:
            self.setEchoMode(QtWidgets.QLineEdit.Normal)
            self.password_shown = True
            self.toggle_action.setIcon(self.non_visible_icon)
        else:
            self.setEchoMode(QtWidgets.QLineEdit.Password)
            self.password_shown = False
            self.toggle_action.setIcon(self.visible_icon)

#############################################################################
##
## Copyright (C) 2017 Hans-Peter Jansen <hpj@urpla.net>
## Copyright (C) 2016 The Qt Company Ltd.
##
## This file is part of the examples of the Qt Toolkit.
##
## $QT_BEGIN_LICENSE:BSD$
## Commercial License Usage
## Licensees holding valid commercial Qt licenses may use this file in
## accordance with the commercial license agreement provided with the
## Software or, alternatively, in accordance with the terms contained in
## a written agreement between you and The Qt Company. For licensing terms
## and conditions see https:#www.qt.io/terms-conditions. For further
## information use the contact form at https:#www.qt.io/contact-us.
##
## BSD License Usage
## Alternatively, you may use self file under the terms of the BSD license
## as follows:
##
## "Redistribution and use in source and binary forms, with or without
## modification, are permitted provided that the following conditions are
## met:
##   * Redistributions of source code must retain the above copyright
##     notice, self list of conditions and the following disclaimer.
##   * Redistributions in binary form must reproduce the above copyright
##     notice, self list of conditions and the following disclaimer in
##     the documentation and/or other materials provided with the
##     distribution.
##   * Neither the name of The Qt Company Ltd nor the names of its
##     contributors may be used to endorse or promote products derived
##     from self software without specific prior written permission.
##
##
## THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
## "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
## LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
## A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
## OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
## SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
## LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
## DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
## THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
## (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
## OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."
##
## $QT_END_LICENSE$
##
#############################################################################


from PyQt5.QtCore import QFile, QFileInfo, Qt
from PyQt5.QtGui import QStandardItem, QStandardItemModel
from PyQt5.QtWidgets import QApplication, QHeaderView, QTableView


import logging
logger = logging.getLogger('piccel')

class FreezeTableWidget(QTableView):
    def __init__(self, parent):
        super(FreezeTableWidget, self).__init__(parent)
        self.frozenTableView = QTableView(self)
        self.init()
        self.horizontalHeader().sectionResized.connect(self.updateSectionWidth)
        self.verticalHeader().sectionResized.connect(self.updateSectionHeight)
        self.frozenTableView.verticalScrollBar().valueChanged.connect(
            self.verticalScrollBar().setValue)
        self.verticalScrollBar().valueChanged.connect(
            self.frozenTableView.verticalScrollBar().setValue)

    def setModel(self, model):
        super(FreezeTableWidget, self).setModel(model)
        self.frozenTableView.setModel(model)
        self.model = model
        model.layoutChanged.connect(self.hide_columns)
        self.hide_columns()
        self.frozenTableView.setSelectionModel(self.selectionModel())

    def hide_columns(self):
        for col in range(1, self.model.columnCount()):
            self.frozenTableView.setColumnHidden(col, True)

    def init(self):
        self.verticalHeader().setMaximumSectionSize(40)
        self.verticalHeader().setMinimumSectionSize(40)
        self.frozenTableView.verticalHeader().setMaximumSectionSize(40)
        self.frozenTableView.verticalHeader().setMinimumSectionSize(40)

        self.frozenTableView.setFocusPolicy(Qt.NoFocus)
        self.frozenTableView.verticalHeader().hide()
        self.frozenTableView.horizontalHeader().setSectionResizeMode(
                QHeaderView.Fixed)
        self.viewport().stackUnder(self.frozenTableView)

        # self.frozenTableView.setStyleSheet('''
        #     QTableView { border: none;
        #                  background-color: #8EDE21;
        #                  selection-background-color: #999;
        #     }''') # for demo purposes

        self.frozenTableView.setColumnWidth(0, self.columnWidth(0))
        self.frozenTableView.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.frozenTableView.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.frozenTableView.show()
        self.updateFrozenTableGeometry()
        self.setHorizontalScrollMode(self.ScrollPerPixel)
        self.setVerticalScrollMode(self.ScrollPerPixel)
        self.frozenTableView.setVerticalScrollMode(self.ScrollPerPixel)

    def updateSectionWidth(self, logicalIndex, oldSize, newSize):
        if logicalIndex == 0:
            self.frozenTableView.setColumnWidth(0, newSize)
            self.updateFrozenTableGeometry()

    def updateSectionHeight(self, logicalIndex, oldSize, newSize):
        self.frozenTableView.setRowHeight(logicalIndex, newSize)
        self.updateFrozenTableGeometry()

    def resizeEvent(self, event):
        super(FreezeTableWidget, self).resizeEvent(event)
        self.updateFrozenTableGeometry()

    def resizeColumnsToContents(self):
        super(FreezeTableWidget, self).resizeColumnsToContents()
        self.updateFrozenTableGeometry()

    def moveCursor(self, cursorAction, modifiers):
        current = super(FreezeTableWidget, self).moveCursor(cursorAction,
                                                            modifiers)
        if (cursorAction == self.MoveLeft and current.column() > 0 and
            self.visualRect(current).topLeft().x() <
            self.frozenTableView.columnWidth(0)):
            newValue = (self.horizontalScrollBar().value() +
                        self.visualRect(current).topLeft().x() -
                        self.frozenTableView.columnWidth(0))
            self.horizontalScrollBar().setValue(newValue)
        return current

    def scrollTo(self, index, hint):
        if index.column() > 0:
            super(FreezeTableWidget, self).scrollTo(index, hint)

    def setAlternatingRowColors(self, state):
        super(FreezeTableWidget, self).setAlternatingRowColors(state)
        self.frozenTableView.setAlternatingRowColors(state)

    def updateFrozenTableGeometry(self):
        self.frozenTableView.setGeometry(
            self.verticalHeader().width() + self.frameWidth() - 2,
            self.frameWidth()-1, self.columnWidth(0)+2,
            self.viewport().height() + self.horizontalHeader().height())


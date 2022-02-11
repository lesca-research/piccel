from PyQt5 import QtGui

style_defs = {
    'default_bg_color' : (255, 248, 240)
}

main_style = """
QLabel {{
   font-family: "Verdana";
   font-size : 12pt;
   color: black;
}}

QWidget {{
    background-color: rgb{default_bg_color};
}}

QLabel[title=True] {{
   color: white;
   font-size : 14pt;
   background-color: rgb(73, 88, 103);
}}
QFrame[title=True] {{
   background-color: rgb(73, 88, 103);
}}

QPushButton {{
    background-color:  rgb(12,80,122);
    border-color: rgb(12,80,122);
    border-style: solid;
    border-width: 1px;
    border-top-left-radius: 5px;
    border-bottom-left-radius: 5px;
    border-top-right-radius: 5px;
    border-bottom-right-radius: 5px;
    padding: 6px;
    color: white;
    font-family: "Verdana";
    font-size : 12pt;
}}

QPushButton:pressed {{
    background-color: rgb(15, 97, 149);
    border-color: rgb(15, 97, 149);
}}

QPushButton:disabled {{
    background-color: gray;
    border-color: gray;
    color:lightgray;
}}


QPushButton#button_previous {{
    border-top-left-radius: 15px;
    border-bottom-left-radius: 15px;
}}

QPushButton#button_next {{
    border-top-right-radius: 15px;
    border-bottom-right-radius: 15px;
}}

QMenu {{ background-color: rgb(247, 252, 255); }}

QComboBox#comboBox_view::drop-down {{
    image: url(:/icons/view_icon);
}}

QComboBox::item:selected {{
    border: 1px solid;
    background: transparent;
}}

QMenu QAbstractItemView  {{
    selection-background-color: rgba(0, 0, 0, 0);
    selection-color: rgb(210, 210, 210);
}}

QMenu {{
    border-width: 1px;
    border-style: solid;
    border-color: rgb(182, 177, 171);
}}

QMenu::item:selected {{
    border: 1px solid;
    background: transparent;
}}

""".format(**style_defs)

error_color = QtGui.QColor('#9C0006')
default_bg_qcolor = QtGui.QColor(*style_defs['default_bg_color'])
table_cell_even_row_darker_factor = 105

# table_cell_darker_qcolor = default_bg_qcolor.darker(110)
"""
QTableView::item
{
  border: 0px;
  padding-top: 10px;
  padding-bottom: 10px;
  padding-left: 5px;
  padding-right: 5px;
}
"""

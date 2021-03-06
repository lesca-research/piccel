from PyQt5 import QtGui

section_bg_color_rgb = (78, 147, 122)
section_fg_color_rgb = (255, 255, 255)

default_bg_color_rgb = (255, 248, 240)
default_bg_qcolor = QtGui.QColor(*default_bg_color_rgb)

section_bg_color = QtGui.QColor(*section_bg_color_rgb)
section_fg_color = QtGui.QColor(*section_fg_color_rgb)

form_bg_color = section_bg_color.darker(105)
form_bg_color_rgb = form_bg_color.getRgb()[:3]
form_fg_color_rgb = section_fg_color_rgb

item_bg_color = section_bg_color.lighter(110)
item_bg_color_rgb = item_bg_color.getRgb()[:3]
item_fg_color_rgb = section_fg_color_rgb

form_item_invalid_bg_color = QtGui.QColor(162, 37, 34) # some red
form_item_invalid_fg_color = QtGui.QColor(255, 255, 255)

form_item_warning_bg_color = QtGui.QColor(224, 142, 69) # some orange
form_item_warning_fg_color = QtGui.QColor(255, 255, 255)

style_defs = {
    'default_bg_color' : default_bg_color_rgb,
    'form_fg_color_rgb' : form_fg_color_rgb,
    'form_bg_color_rgb' : form_bg_color_rgb,
    'section_fg_color_rgb' : section_fg_color_rgb,
    'section_bg_color_rgb' : section_bg_color_rgb,
    'item_fg_color_rgb' : item_fg_color_rgb,
    'item_bg_color_rgb' : item_bg_color_rgb,
    'progress_note_header_bg_color' : section_bg_color_rgb,
    'progress_note_header_fg_color' : section_fg_color_rgb,
}


main_style = """
QWidget {{
    background-color: rgb{default_bg_color};
}}

QLabel {{
   font-family: "Verdana";
   font-size : 12pt;
   color: black;
   background-color: rgba(255, 255, 255, 0);
}}

QTextEdit#textBrowser {{
   font-family: "Courier";
   font-size : 14pt;
   color: black;
}}


QLabel#report_header_label {{
   color: rgb{progress_note_header_fg_color};
   font-size : 14pt;
   background-color: rgb{progress_note_header_bg_color};
   padding: 10px;
}}

QLabel#report_footer_label {{
   color : rgb{progress_note_header_fg_color};
   font-size : 12pt;
   font-style : italic;
   background-color: rgb{progress_note_header_bg_color};
   padding: 5px;
}}

QTextEdit#report_content {{
   font-family: "Verdana";
   font-size : 12pt;
   color: black;
}}

QFrame#frame_form_title {{
   color: rgb{form_fg_color_rgb};
   background-color: rgb{form_bg_color_rgb};
}}

QLabel#form_title {{
   color: rgb{form_fg_color_rgb};
   font-size : 14pt;
   font-style : bold;
}}

QFrame#frame_section_title {{
   color: rgb{section_fg_color_rgb};
   background-color: rgb{section_bg_color_rgb};
}}

QLabel#section_title {{
   color: rgb{section_fg_color_rgb};
   font-size : 14pt;
}}

QFrame#frame_item_title {{
   color: rgb{item_fg_color_rgb};
   background-color: rgb{item_bg_color_rgb};
   border-top-left-radius: 15px;
   border-top-right-radius: 15px;
   border-bottom-left-radius: 0px;
   border-bottom-right-radius: 0px;
}}

QLabel#item_title {{
   color: rgb{item_fg_color_rgb};
   font-size : 12pt;
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

language_radio_style = \
"""
color: rgb{item_fg_color_rgb};
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

progress_note_report_style = \
"""
td {
   padding: 4px;
   text-align: left;
}
th {
   padding: 4px;
   text-align: left;
}
.report_odd_row {
   padding: 4px;
   background-color: #CAE2DA;
}
"""

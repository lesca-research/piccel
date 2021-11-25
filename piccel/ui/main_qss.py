main_style = """
QLabel {
   font-family: "Verdana";
   font-size : 12pt;
   color: black;
}

QWidget {
    background-color: rgb(255, 248, 240);
}

QLabel[title=True] {
   color: white;
   font-size : 14pt;
   background-color: rgb(73, 88, 103);
}
QFrame[title=True] {
   background-color: rgb(73, 88, 103);
}

QPushButton {
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
}

QPushButton:pressed {
    background-color: rgb(15, 97, 149);
    border-color: rgb(15, 97, 149);
}

QPushButton:disabled {
    background-color: gray;
    border-color: gray;
}


QPushButton#button_previous {
    border-top-left-radius: 15px;
    border-bottom-left-radius: 15px;
}

QPushButton#button_next {
    border-top-right-radius: 15px;
    border-bottom-right-radius: 15px;
}
"""


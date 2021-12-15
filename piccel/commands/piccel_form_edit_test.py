#!/usr/bin/env python3
import sys
from PyQt5.QtWidgets import QApplication

from piccel.form import Form, FormEditor

def main():

    form_def = {
        'label' : 'Participant_Info',
        'title' : {'French' : 'Un formulaire'},
        'default_language' : 'French',
        'supported_languages' : {'French'},
        'sections' : {
            'section1' : {
                'title' : {'French' : 'Titre de la section 1'},
                'items' : [
                    {'keys' : {'Participant_ID' :
                               {'French':'Code Participant'}},
                     'unique' : True,
                     'freeze_on_update' : True,
                    },
                    {'keys' : {'Name' : {'French':'Nom'}}},
                    {'keys' : {'Status' : {'French':"Statut d'inclusion"}},
                     'choices' : {'included' : {'French' : 'Inclus.e'},
                                  'not_included' : {'French' : 'NON inclus.e'}}
                    }
                ]
            },
            'section2' : {
                'items' : [
                    {'keys' : {'Var1' : None},
                     'vtype' : 'int64'
                    },
                    {'keys' : {'Check1' : None,
                               'Check2' : None},
                     'vtype' : 'boolean'
                    },
                ]
            },
            'section3' : {
                'items' : [
                    {'keys' : {'Var1' : None},
                     'vtype' : 'int64'
                    },
                ],
            }
        }
    }

    app = QApplication(sys.argv)
    # FormEditor.from_file('form.form')
    # FormEditor(on_save=sheet.set_form_master,
    #            frozen_key_types={'Participant_ID' : 'text'})
    # tmp_dir = tempfile.mkdtemp()
    # form_fn = op.join(tmp_dir, 'test.form')
    # with open(form_fn, 'w') as fout:
    #     fout.write(.to_json())

    form_editor = FormEditor(Form.from_dict(form_def).to_dict())
    form_editor.show()
    sys.exit(app.exec_())

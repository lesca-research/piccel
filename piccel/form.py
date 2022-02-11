# -*- coding: utf-8 -*-

from datetime import date, datetime, timedelta, time
import logging
import tempfile
import os
import os.path as op
import shutil
import unittest
from collections import OrderedDict, defaultdict, namedtuple
import re
from pprint import pformat, pprint
from uuid import uuid1, uuid4
from time import sleep
from copy import copy
from traceback import format_stack, format_exc

import json
import numpy as np
import pandas as pd

from .logging import logger
from .core import (UserRole, Notifier, LazyFunc, nexts, if_none, refresh_text,
                   text_connect, get_set_connect, language_abbrev, if_none_or_empty)
from .core import (FormEditionBlockedByPendingLiveForm, FormEditionLocked,
                   FormEditionNotOpen, FormEditionLockedType,
                   FormEditionOrphanError, FormEditionCancelled)

from . import ui
from .ui.widgets import ListSelectDialog, show_critical_message_box

from PyQt5 import QtCore, QtGui, QtWidgets

class InvalidFormItemType(Exception): pass
class InvalidFormItemKey(Exception): pass
class InvalidFormItemInput(Exception): pass
class InvalidFormSection(Exception): pass
class FormDataInconsitency(Exception): pass
class NotEditableError(Exception): pass
class IndexNotFound(Exception): pass
class InconsistentIndex(Exception): pass
class InvalidIndexValue(Exception): pass
class InvalidValue(Exception): pass
class InvalidForm(Exception): pass
class InvalidSection(Exception): pass
class SectionNotFound(Exception): pass
class InvalidSectionMove(Exception): pass
class BadLabelFormat(Exception): pass


class FormSelector(QtWidgets.QDialog):
    def __init__(self, form, selection_mode, parent=None):
        super(QtWidgets.QDialog, self).__init__(parent)

        # assert(selection_mode in ['section', 'item'])
        assert(selection_mode == 'section')

        self.setWindowTitle('Import %s' % {'section' : 'Section(s)',
                                           'item' : 'Item(s)'}[selection_mode])


        QBtn = QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel
        self.buttonBox = QtWidgets.QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)
        self.buttonBox.rejected.connect(self.reject)

        self.form_selector = FormEditor(form, selection_mode=selection_mode)

        self.layout = QtWidgets.QVBoxLayout()
        self.layout.addWidget(self.form_selector)
        self.layout.addWidget(self.buttonBox)
        self.setLayout(self.layout)

    def get_selection(self):
        return (self.form_selector.selection_mode,
                self.form_selector.get_selection())

class FormJsonHook:
    def __init__(self):
        pass
    def __call__(self, obj):
        parsed_dict = {}
        for k,v in obj.items():
            if isinstance(k, str):
                if k == 'false':
                    k = False
                elif k == 'true':
                    k = True
            parsed_dict[k] = v
        return parsed_dict

class InconsistentForms(Exception): pass

class Form:
    """

Google App script to export a google form to json:

// Steven Schmatz
// Humanitas Labs
// 13 October, 2016.


// Sample URL. Note that this must be authenticated with the current user.
var URL = "https://docs.google.com/forms/d/1vNhQN-wM534q-lsNJXkAci2KuRh7xZpdClOyEFJAeWY/edit";

/**
 * Converts the given form URL into a JSON object.
 */
function main() {

  var form = FormApp.openByUrl(URL);
  var items = form.getItems();

  var result = {
    "metadata": getFormMetadata(form),
    "items": items.map(itemToObject),
    "count": items.length
  };

  Logger.log(JSON.stringify(result));
}

/**
 * Returns the form metadata object for the given Form object.
 * @param form: Form
 * @returns (Object) object of form metadata.
 */
function getFormMetadata(form) {
  return {
    "title": form.getTitle(),
    "id": form.getId(),
    "description": form.getDescription(),
    "publishedUrl": form.getPublishedUrl(),
    "editorEmails": form.getEditors().map(function(user) {return user.getEmail()}),
    "count": form.getItems().length,
    "confirmationMessage": form.getConfirmationMessage(),
    "customClosedFormMessage": form.getCustomClosedFormMessage()
  };
}

/**
 * Returns an Object for a given Item.
 * @param item: Item
 * @returns (Object) object for the given item.
 */
function itemToObject(item) {
  var data = {};

  data.type = item.getType().toString();
  data.title = item.getTitle();
  data.description = item.getHelpText();

  // Downcast items to access type-specific properties

  var type_str = item.getType().toString();
  Logger.log(type_str);
  if(type_str == "DATETIME") {
    type_str = "DATE_TIME";
  }
  var itemTypeConstructorName = snakeCaseToCamelCase("AS_" + type_str + "_ITEM");
  var item_constructor = item[itemTypeConstructorName];
  var typedItem = item_constructor();

  // Keys with a prefix of "get" have "get" stripped

  var getKeysRaw = Object.keys(typedItem).filter(function(s) {return s.indexOf("get") == 0});

  getKeysRaw.map(function(getKey) {
    var propName = getKey[3].toLowerCase() + getKey.substr(4);

    // Image data, choices, and type come in the form of objects / enums
    if (["image", "choices", "type", "alignment"].indexOf(propName) != -1) {return};

    // Skip feedback-related keys
    if ("getFeedbackForIncorrect".equals(getKey) || "getFeedbackForCorrect".equals(getKey)
      || "getGeneralFeedback".equals(getKey)) {return};

    var propValue = typedItem[getKey]();

    data[propName] = propValue;
  });

  // Bool keys are included as-is

  var boolKeys = Object.keys(typedItem).filter(function(s) {
    return (s.indexOf("is") == 0) || (s.indexOf("has") == 0) || (s.indexOf("includes") == 0);
  });

  boolKeys.map(function(boolKey) {
    var propName = boolKey;
    var propValue = typedItem[boolKey]();
    data[propName] = propValue;
  });

  // Handle image data and list choices

  switch (item.getType()) {
    case FormApp.ItemType.LIST:
    case FormApp.ItemType.CHECKBOX:
    case FormApp.ItemType.MULTIPLE_CHOICE:
      data.choices = typedItem.getChoices().map(function(choice) {
        return choice.getValue();
      });
      break;

    case FormApp.ItemType.IMAGE:
      data.alignment = typedItem.getAlignment().toString();

      if (item.getType() == FormApp.ItemType.VIDEO) {
        return;
      }

      var imageBlob = typedItem.getImage();

      data.imageBlob = {
        "dataAsString": imageBlob.getDataAsString(),
        "name": imageBlob.getName(),
        "isGoogleType": imageBlob.isGoogleType()
      };

      break;

    case FormApp.ItemType.PAGE_BREAK:
      data.pageNavigationType = typedItem.getPageNavigationType().toString();
      break;

    default:
      break;
  }

  // Have to do this because for some reason Google Scripts API doesn't have a
  // native VIDEO type
  if (item.getType().toString() === "VIDEO") {
    data.alignment = typedItem.getAlignment().toString();
  }

  return data;
}

/**
 * Converts a SNAKE_CASE string to a camelCase string.
 * @param s: string in snake_case
 * @returns (string) the camelCase version of that string
 */
function snakeCaseToCamelCase(s) {
  return s.toLowerCase().replace(/(\_\w)/g, function(m) {return m[1].toUpperCase();});
}
  """

    def __init__(self, sections=None, default_language=None,
                 supported_languages=None, title='', label='Form',
                 watchers=None):
        """
        - sections:
          IMPORTANT:
            if no next_section_definition is given, then use the next section
            in order. If section is last then consider that the form can be
            submitted afterwards.
        """
        self.label = label
        self.notifier = Notifier(watchers)

        default_language = if_none(default_language, 'English')
        supported_languages = if_none(supported_languages, [default_language])
        self.tr = Translator(default_language=default_language,
                             supported_languages=supported_languages)
        self.tr.register('title', title)
        self.unique_keys = set()

        self.datetime_keys = set()
        self.date_keys = set()
        self.int_keys = set()
        self.user_items = []
        self.float_keys = set()
        self.text_keys = set()
        self.boolean_keys = set()
        self.to_freeze_on_update = set()

        self.key_to_items = defaultdict(list)

        sections = if_none(sections, {})
        section_names = list(sections.keys())
        for i_section, (section_name, section) in enumerate(sections.items()):
            if section.tr.supported_languages != self.tr.supported_languages:
                raise UnsupportedLanguage('Supported languages in Form %s (%s)'\
                                          ' != those of section %s (%s)' % \
                                          (self, self.tr.supported_languages,
                                           section_name,
                                           section.tr.supported_languages))
            section.notifier.add_watcher('section_valid',
                                         LazyFunc(self.on_section_is_valid,
                                                  section_name, section))
            section.notifier.add_watcher('section_invalid',
                                         LazyFunc(self.on_section_is_invalid,
                                                  section_name, section))
            if section.next_section_definition is None:
                next_section = (section_names[i_section+1]
                                if i_section+1 < len(section_names)
                                else '__submit__')
                logger.debug2('Set default next section of %s to %s',
                             section_name, next_section)
                section.set_next_section_definition(next_section)
            else:
                logger.debug2('Kept next section definition for %s: %s',
                             section_name, section.next_section_definition)

            for item in section.items:
                if item.unique:
                    assert(len(item.keys)==1) # no multiple unique constraint yet
                if item.freeze_on_update:
                    self.to_freeze_on_update.add(item)
                if item.vtype == 'user_name':
                    self.user_items.append(item)

                for key in item.keys:
                    self.key_to_items[key].append(item)

                    if item.unique:
                        self.unique_keys.add(key)

                    if item.vtype == 'date':
                        self.date_keys.add(key)
                    elif item.vtype == 'datetime':
                        self.datetime_keys.add(key)
                    elif item.vtype == 'int':
                        self.int_keys.add(key)
                    elif item.vtype == 'float':
                        self.float_keys.add(key)
                    elif item.vtype == 'text':
                        self.text_keys.add(key)
                    elif item.vtype == 'boolean':
                        self.boolean_keys.add(key)

        self.sheet = None

        self.sections = sections
        self.current_section = None
        self.current_section_name = None
        self.section_path = []
        self.validity = None
        self.on_submission = None
        self.on_cancel = None
        self.set_language(default_language)
        self.to_next_section()

    def is_empty(self):
        return len(self.sections) == 0

    def add_item(self, section_name, item):
        self[section_name].add_item(item)
        self._register_item(item)

    def _register_item(self, item):
        if item.keys is not None:
            for key in item.keys.keys():
                self.key_to_items[key].append(item)
            if item.vtype == 'date':
                self.date_keys.add(key)
            elif item.vtype == 'datetime':
                self.datetime_keys.add(key)

    def remove_item(self, section_name, item):
        self[section_name].remove_item(item)
        self._unregister_item(item)

    def _unregister_item(self, item):
        if item.keys is not None:
            for key in item.keys.keys():
                self.key_to_items[key].remove(item)
            if item.vtype == 'date':
                self.date_keys.remove(key)
            elif item.vtype == 'datetime':
                self.datetime_keys.remove(key)

    def set_supported_languages(self, languages):
        self.tr.set_supported_languages(languages)
        for section in self.sections.values():
            section.set_supported_languages(languages)

    def set_unique_validator(self, validator):
        for section in self.sections.values():
            for item in section.items:
                if item.unique:
                    item.set_unique_validator(validator)

    def set_language(self, language):
        if language != self.tr.language:
            self.tr.set_language(language)
            self.notifier.notify('language_changed')
            for section in self.sections.values():
                section.set_language(language)

    def get_dtypes(self):
        return {k:its[0].dtype_pd for k,its in self.key_to_items.items()
                if len(its)>0}

    def get_vtypes(self):
        return {k:its[0].vtype for k,its in self.key_to_items.items()
                if len(its)>0}

    def get_vchoices(self):
        return {k:its[0].choices for k,its in self.key_to_items.items()
                if len(its)>0}

    def has_key(self, key):
        return key in self.key_to_items

    def set_user(self, user):
        for item in self.user_items:
            item.set_user(user)

    def format(self, key, value):
        return self.key_to_items[key][0].format(value)

    def unformat(self, key, value):
        return self.key_to_items[key][0].unformat(value)

    def add_translations(self, other_form):
        self.tr.add_translations(other_form.tr)
        differing_sections = (set(self.sections.keys())
                              .symmetric_difference(other_form.sections))

        if len(differing_sections) != 0:
            raise InconsistentForms('Differing sections: %s' % \
                                    differing_sections)
        for (section_name, section), (other_section_name, other_section) \
            in zip(self.sections.items(), other_form.sections.items()):
            if section_name != other_section_name:
                raise InconsistentForms('Differing section names: %s / %s' %\
                                        section_name, other_section_name)
            try:
                section.add_translations(other_section)
            except InconsistentSections:
                raise InconsistentForms('Content of sections differ: %s / %s'%\
                                        section_name, other_section_name)

    def __eq__(self, other):
        sd = self.to_dict()
        od = other.to_dict()
        result = isinstance(other, Form) and sd == od
        if not result:
            logger.debug('Forms not equal:')
            logger.debug(' - form: %s', pformat(sd))
            logger.debug(' - other form: %s', pformat(od))
        return isinstance(other, Form) and self.to_dict()==other.to_dict()

    def set_transitions(self, next_section_definitions):
        for section_name, section_transitions in next_section_definitions.items():
            logger.debug('Set transitions of section %s', section_name)
            if section_transitions is not None:
                if isinstance(section_transitions, str) or section_transitions is None:
                    section_transitions = [section_transitions]
                for section_transition in section_transitions:
                    logger.debug('Check transition definition: %s', section_transition)
                    if isinstance(section_transition, str) or section_transition is None:
                        next_section_label = section_transition
                    else:
                        _, next_section_label = section_transition
                    assert( (next_section_label is None)
                            or (next_section_label=='__submit__')
                            or (next_section_label in self.sections))
            self[section_name].set_next_section_definition(section_transitions)

    def first_section(self):
        return next(iter(self.sections))

    def _prepend(self, key, value, vtype, access_level=UserRole.ADMIN,
                 editable=False):
        section0 = next(iter(self.sections.values()))
        item = FormItem({key:None}, section0.tr.language,
                        section0.tr.supported_languages, vtype=vtype,
                        access_level=access_level, editable=editable,
                        init_values={key:value})
        section0.add_item(item, position=0, watch_validity=False)
        self._register_item(item)

    @staticmethod
    def from_dict(d, watchers=None):
        def make_section(sd):
            if 'default_language' not in sd:
                sd['default_language'] = d['default_language']
            if 'supported_languages' not in sd:
                sd['supported_languages'] = d['supported_languages']
            return FormSection.from_dict(sd)

        sections = {sec_name:make_section(sec_d) \
                    for sec_name, sec_d in d['sections'].items()}
        return Form(sections, d['default_language'],
                    d['supported_languages'], d.get('title', ''),
                    label=d.get('label', 'Form'), watchers=watchers)

    @staticmethod
    def from_gform_json_file(json_fn, language, use_item_title_as_key=True,
                             paragraph_nb_lines=5, watchers=None):
        GTYPES = {
            'SECTION_HEADER' : 'text',
            'TEXT' : 'text',
            'PARAGRAPH_TEXT' : 'text',
            'MULTIPLE_CHOICE' : 'text',
            'LIST' : 'text',
            'CHECKBOX' : 'boolean',
            'DATE' : 'date',
            'DATETIME' : 'datetime',
        }
        var_gen_label = IndexedPattern('var%d') \
            if not use_item_title_as_key else None
        section_gen_label = IndexedPattern('section%d') \
            if not use_item_title_as_key else None

        def protect_label(label):
            protected_label = label
            for repl in [(' ', '_'), (':','_'), (',', '_'), ('-', '_'),
                         ('é', 'e'), ('é', 'e'), ('è', 'e'), ('à', 'a')]:
                protected_label = protected_label.replace(*repl)
            if not protected_label.isidentifier():
                raise BadLabelFormat(label)
            return protected_label

        def get_label(label, gen_default=None, protect=True):
            sep = '::'
            key_split = label.split(sep)
            if len(key_split) > 1:
                label = key_split[0].strip()
                title = sep.join(key_split[1:]).strip()
            else:
                if gen_default is not None:
                    title = label
                    label = gen_default()
                else:
                    title = label

            if protect:
                try:
                    label = protect_label(label)
                except BadLabelFormat:
                    label = None

            return label, title

        with open(json_fn, 'r') as fin:
            gform_dict = json.load(fin)
        if 0:
            print('gform_dict:')
            pprint(gform_dict)

        section_label = '__section_0__'
        section_dict = {'items' : [],
                        'default_language' : language,
                        'supported_languages' : {language}}
        sections = {section_label : section_dict}
        if len(gform_dict.get('metadata', {}).get('description', '')) > 0:
            description_tr = {language : gform_dict['metadata']['description']}
            section_dict['items'].append({'keys' : None,
                                          'vtype' : 'text',
                                          'title' : {language :
                                                     'Section description'},
                                          'choices' : None,
                                          'default_language' : language,
                                          'supported_languages':{language},
                                          'description': description_tr,
                                          'allow_empty' : True,
                                          'nb_lines' : 1,
                                          'other_choice_label' : None})
        var_count, sec_count = 1, 1
        for item_gdict in gform_dict['items']:
            # print('Convert gform item %s' % pformat(item_gdict))
            if item_gdict['type'] == 'PAGE_BREAK':
                slabel, stitle = get_label(item_gdict['title'], section_gen_label)
                if slabel is None:
                    slabel = '_section_%d' % sec_count
                    sec_count += 1
                section_dict = {'title' : {language: stitle},
                                'default_language' : language,
                                'supported_languages' : {language},
                                'items' : []}
                sections[slabel] = section_dict
                if len(item_gdict.get('description', '')) > 0:
                    item_description = {language : item_gdict['description']}
                    section_dict['items'].append({'keys' : None,
                                                  'vtype' : 'text',
                                                  'title' : {language :
                                                             'Section description'},
                                                  'choices' : None,
                                                  'default_language' : language,
                                                  'supported_languages':{language},
                                                  'description': item_description,
                                                  'allow_empty' : True,
                                                  'nb_lines' : 1,
                                                  'other_choice_label' : None})
            else:
                item_title = item_gdict['title']
                item_choices = None
                other_choice_label = None
                if item_gdict['type'] == 'SECTION_HEADER':
                    item_keys = None
                elif item_gdict['type'] != 'CHECKBOX':
                    key_label, item_title = get_label(item_gdict['title'],
                                                      var_gen_label)
                    if key_label is None:
                        key_label = 'Var_%s' % var_count
                        var_count += 1
                    item_keys = {key_label : {language : item_title}}
                    if item_gdict['type'] in ['MULTIPLE_CHOICE', 'LIST']:
                        item_choices = {}
                        for ichoice, c in enumerate(item_gdict['choices']):
                            clabel, ctitle = get_label(c, protect=False)
                            clabel = if_none(clabel, 'choice_%d' % ichoice)
                            item_choices[clabel] = {language : ctitle}
                        if item_gdict.get('allow_other_choice', False):
                            other_label = {'English' : 'Other',
                                           'French' : 'Autre'}.get(language,
                                                                   'Other')
                            other_choice_label = {language : other_label}
                else:
                    item_keys = {}
                    for ichoice, c in enumerate(item_gdict['choices']):
                        clabel, ctitle = get_label(c)
                        clabel = if_none(clabel, 'choice_%d' % ichoice)
                        item_keys[clabel] = {language : ctitle}
                item_type = GTYPES[item_gdict['type']]
                item_description = {language : item_gdict.get('description', '')}
                item_required = item_gdict.get('required', False)
                item_title = {language : item_title}
                nb_lines = 1
                if item_gdict['type'] == 'PARAGRAPH_TEXT':
                    nb_lines = paragraph_nb_lines

                section_dict['items'].append({'keys':item_keys,
                                              'vtype' : item_type,
                                              'title' : item_title,
                                              'choices' : item_choices,
                                              'default_language' : language,
                                              'supported_languages' : {language},
                                              'description': item_description,
                                              'allow_empty' : not item_required,
                                              'nb_lines' : nb_lines,
                                              'other_choice_label' : \
                                              other_choice_label})

        return Form({sn : FormSection.from_dict(sd) \
                     for sn,sd in sections.items()},
                    language, {language},
                    {language: gform_dict['metadata']['title']},
                    watchers=watchers)

    def set_on_submission(self, func):
        """ func(entry_dict) """
        self.on_submission = func

    def set_on_cancel(self,func):
        self.on_cancel = func

    def to_dict(self):
        return {'title': self.tr.trs['title'],
                'label' : self.label,
                'sections' : {sn:s.to_dict() for sn,s in self.sections.items()},
                'default_language' : self.tr.language,
                'supported_languages' : list(self.tr.supported_languages)}

    def to_json(self):
        return json.dumps(self.to_dict(), indent=4)

    def set_input_callback(self, callback):
        """ callback(form_section, item_key, input_str) """
        for section_label, section in self.sections.items():
            for item in section.items:
                item_callback = LazyFunc(callback, form_section=section_label)
                item.set_input_callback(item_callback)

    def to_next_section(self):
        if len(self.sections) == 0:
            return

        if self.current_section == None:
            self.current_section_name, self.current_section = \
                next(iter(self.sections.items())) # TODO: handle no sections
            self.section_path.append(self.current_section_name)
            self.notifier.notify('previous_section_not_available')
        else:
            if not self.current_section.is_valid():
                logger.debug('Current section "%s" is invalid, ' \
                             'cannot go to next one.', self.section_path[-1])
                raise InvalidSection(self.section_path[-1])
            next_section_name = self.current_section.next()
            if next_section_name is not None:
                self.section_path.append(next_section_name)
                self.current_section = self[next_section_name]
                self.current_section_name = next_section_name
                logger.debug('Going to next section "%s"', next_section_name)
            else:
                logger.error('No more section to switch to')
                raise InvalidSectionMove()

        if self.current_section.is_valid():
            self.on_section_is_valid(self.current_section_name,
                                     self.current_section)
        else:
            self.on_section_is_invalid(self.current_section_name,
                                       self.current_section)
        self.current_section.set_language(self.tr.language)
        return self.current_section

    def next_section(self):
        return self.current_section.next()

    def to_previous_section(self):
        if len(self.section_path)>1:
            self.section_path.pop()
            logger.debug('Returning to previous section "%s"',
                         self.section_path[-1])
            self.current_section_name = self.section_path[-1]
            self.current_section = self[self.section_path[-1]]
        else:
            logger.debug('No previous section to return to')
        self.validate()

        self.current_section.set_language(self.tr.language)
        return self.current_section

    def __str__(self):
        return 'Form{%s}' % self.tr['title']

    def on_section_is_valid(self, section_name, section):
        logger.debug2('%s is notified that section %s is valid',
                     self, section_name)
        self.validate()

    def on_section_is_invalid(self, section_name, section):
        logger.debug2('%s is notified that section %s is invalid',
                     self, section_name)
        self.validate()

    def validate(self):
        next_section = self.current_section.next()
        current_section_is_final =  next_section == '__submit__'
        validity = current_section_is_final and \
            all(self[s].is_valid() for s in self.section_path)
        logger.debug2('%s: validity is %s (ccurrent_section=%s, is_final=%s, '\
                     'section_path=%s)', self, validity,
                     self.current_section_name, current_section_is_final,
                     ', '.join(self.section_path))
        signal = ['not_ready_to_submit', 'ready_to_submit'][validity]
        logger.debug2('%s notifies %s', self, signal)
        self.notifier.notify(signal)

        if current_section_is_final or not self.current_section.is_valid() or \
           next_section is None:
            signal = 'next_section_not_available'
        else:
            signal = 'next_section_available'
        logger.debug2('%s notifies %s', self, signal)
        self.notifier.notify(signal)

        if self.previous_section() is None:
            signal = 'previous_section_not_available'
        else:
            signal = 'previous_section_available'
        logger.debug2('%s notifies %s', self, signal)
        self.notifier.notify(signal)

        self.validity = validity

    def previous_section(self):
        return self.section_path[-2] if len(self.section_path)>1 else None

    @staticmethod
    def from_json(json_str):
        return Form.from_dict(json.loads(json_str)) # object_hook=FormJsonHook()

    @staticmethod
    def from_json_file(form_fn):
        def _load(encoding):
            with open(form_fn, 'r', encoding=encoding) as fin:
                return Form.from_json(fin.read())
        try:
            return _load('utf-8')
        except ValueError:
            return _load('latin-1')

    def save_to_json_file(self, form_fn):
        with open(form_fn, 'w', encoding='utf-8') as fout:
            fout.write(self.to_json())

    def __getitem__(self, k):
        return self.sections[k]

    def new(self, entry_dict=None, watchers=None):
        form = Form.from_dict(self.to_dict(), watchers=watchers)
        if entry_dict is not None:
            form.set_values_from_entry(entry_dict)
            # TODO clarify entry overwriting versus append new entry from existing
            # form.entry_udpate(entry_dict)
            # form.freeze_items()
            # item.freezable
            # item.frozen -> if true, do not check unique, make it non-editablte

            # form.entry_overwrite(entry_dict)
            # check for unique but ignore previous value because it will be replaced
        # if self.sheet is not None:
        #     form.attach_sheet(self.sheet)
        # else:
        #     logger.warning('Create new form from "%s" without attached sheet',
        #                    self.tr['title'])
        return form

    def set_values_from_entry(self, entry_dict):
        logger.debug('Filling values of form "%s" from entry with keys %s',
                     self.tr['title'], entry_dict.keys())
        for key,value in entry_dict.items():
            self.set_value_for_key(key, value)

    def set_value_for_key(self, key, value):
        for section in self.sections.values():
            section.set_value_for_key(key, value)

    def reset(self):
        # logger.debug('Reset form "%s"', self.tr['title'])
        for section in self.sections.values():
            section.reset()

    def cancel(self):
        if self.on_cancel is None:
            logger.warning('No cancel function set for form %s', self)
        else:
            logger.debug('Call on_cancel from form %s', self)
            self.on_cancel()

    def submit(self):
        """
        Section path is evaluated again because a value may change during
        submission (eg timestamp_submission) so transitions may differ
        """
        # TODO: utest form submitted twice and item with unique constraint !!
        if not self.is_valid():
            invalid_sections = []
            for section_name in self.section_path:
                if not self[section_name].is_valid():
                    invalid_items = self[section_name].get_invalid_items()
                    invalid_sections.append((section_name, invalid_items))
            raise InvalidForm('\n'.join('%s: %s' %(s,', '.join('%s'%i for i in its)) \
                                        for s,its in invalid_sections))
        logger.debug('Collecting values in form "%s" for submission',
                     self.tr['title'])
        current_section_name, current_section = next(iter(self.sections.items()))
        entry = {}
        while current_section_name != '__submit__':
            section_items = current_section.submit()
            for k,v in section_items.items():
                if k in entry:
                    logger.warning('Duplicate input for key %s while submitting '\
                                   'form %s', k, self.tr['title'])
                entry[k] = v
            if logger.level >= logging.DEBUG:
                logger.debug('Collected values from section "%s" for keys: %s',
                             current_section_name, ', '.join(section_items))
            next_section_name = current_section.next()
            if next_section_name == '__submit__':
                current_section_name = '__submit__'
                current_section = None
            else:
                if next_section_name is not None and  \
                   next_section_name not in self.sections:
                    raise SectionNotFound(next_section_name)
                current_section = self.sections.get(next_section_name, None)
                if current_section is None:
                    raise InvalidForm('No next section defined for section %s' % \
                                      current_section_name)
                current_section_name = next_section_name
        if self.on_submission is None:
            logger.warning('No submission function set for form %s', self)
        else:
            logger.debug('Call on_submission from form %s', self)
            self.on_submission(entry_dict=entry)
        return entry

    def is_valid(self):
        # invalid_items = []
        for section_name in self.section_path:
            if not self[section_name].is_valid():
                return False
                    # invalid_items.append('%s.[%s]' % \
                    #                      (section_name, ','.join(item.keys)))
        return True

    def ready_to_submit(self):
        try:
            return self.next_section() == '__submit__' and self.is_valid()
        except InvalidValue:
            return False

class InvalidPredicateResult(Exception): pass

class Predicate:

    def __init__(self, code):
        self.code = code

    def ___str__(self):
        return self.code

    def __call__(self, key_values):
        result = eval(self.code, {}, key_values)
        if not isinstance(result, bool):
            raise InvalidPredicateResult('Result "%s" (type:%s) is not bool' % \
                                         (result, type(result)))
        return result

class DateTimeCollector:
    def __init__(self, callback_date_str, qdate=None,
                 hours=None, minutes=None):
        self.date, self.hours, self.minutes = None, None, None
        self.callback = None
        self.set_date(qdate)
        self.set_hours(hours)
        self.set_minutes(minutes)
        self.callback = callback_date_str

    def set_date(self, qdate):
        if qdate is not None and not qdate.isNull():
            self.date = qdate.toPyDate()
            self.check_completion()
        else:
            self.date = None

    def set_hours(self, hours):
        self.hours = hours if hours is not None else None
        self.check_completion()

    def set_minutes(self, minutes):
        self.minutes = minutes if minutes is not None else None
        self.check_completion()

    def clear(self):
        """
        """
        self.date, self.hours, self.minutes = None, None, None
        self.callback('')

    def check_completion(self):
        if self.callback is not None:
            date_str = ''
            if self.date is not None and self.minutes is not None and \
               self.hours is not None:
                dt = datetime.combine(self.date, time(self.hours, self.minutes))
                date_str = dt.strftime(FormItem.DATETIME_FORMAT)
            print('collected datetime: ', date_str)
            self.callback(date_str)

class TestDateTimeCollector(unittest.TestCase):

    def setUp(self):
        self.date_str = 'start'
        self.set_date_str_nb_calls = 0

    def set_date_str(self, sdate):
        self.set_date_str_nb_calls += 1
        self.date_str = sdate

    def test_null(self):
        dt_collector = DateTimeCollector(self.set_date_str)
        dt_collector.set_date(QtCore.QDate())
        self.assertEqual(self.set_date_str_nb_calls, 0)
        self.assertEqual(self.date_str, 'start')

    def test_no_callback_at_init(self):
        DateTimeCollector(self.set_date_str, QtCore.QDate(2020,1,1),
                          11, 13)
        self.assertEqual(self.set_date_str_nb_calls, 0)
        self.assertEqual(self.date_str, 'start')

    def test_setdate_no_hours(self):
        dt_collector = DateTimeCollector(self.set_date_str)
        dt_collector.set_date(QtCore.QDate(2020,1,1))
        self.assertEqual(self.set_date_str_nb_calls, 1)
        self.assertEqual(self.date_str, '')

    def test_set_full_date(self):
        dt_collector = DateTimeCollector(self.set_date_str)
        dt_collector.set_date(QtCore.QDate(2020,1,1))
        dt_collector.set_hours(12)
        self.assertEqual(self.set_date_str_nb_calls, 2)
        self.assertEqual(self.date_str, '')
        dt_collector.set_minutes(13)
        self.assertEqual(self.set_date_str_nb_calls, 3)
        self.assertEqual(self.date_str,
                         (datetime(2020,1,1,12,13)
                          .strftime(FormItem.DATETIME_FORMAT)))

    def test_clear(self):
        dt_collector = DateTimeCollector(self.set_date_str)
        dt_collector.set_date(QtCore.QDate(2020,1,1))
        dt_collector.set_hours(12)
        dt_collector.set_minutes(13)
        self.assertEqual(self.set_date_str_nb_calls, 3)
        dt_collector.clear()
        self.assertEqual(self.set_date_str_nb_calls, 4)
        self.assertEqual(self.date_str, '')

class TestPredicate(unittest.TestCase):

    def test_normal_call(self):
        pred = Predicate('Participant_ID.startswith("CE9")')
        self.assertFalse(pred({'Participant_ID':'CE0004'}))
        self.assertTrue(pred({'Participant_ID':'CE9004'}))

    def test_result_not_bool(self):
        self.assertRaises(InvalidPredicateResult,
                          Predicate('Participant_ID[-1]'),
                          {'Participant_ID':'CE9004'})

class InconsistentSections(Exception): pass

class FormSection:

    def __init__(self, items, default_language, supported_languages,
                 title='', next_section_definition=None, watchers=None):
        """
        - next_section_definition:
            Type: None | str | list(None | str | tuple(str, str, None | str)
            Define how to get the next section as a list of criterions, whose
            first matching one is used. If nothing matches, then there is no
            next section and the form cannot be submitted.
            * None: No next section and form cannot be submitted
            * str: The label of the next section or '__submit__' to indicate submission.
            * tuple(str, '__submit__' | str):
                  tuple(predicate_code, '__submit__' | section_label)
                  Define a criterion depending on actual values, associated with
                  a section_label or '__submit__'.
                  A predicate code is evaluated by eval(predicate_code, key_vals_dict)
                  and must return a boolean.
            By default, next_section_definition is None, meaning that a section cannot
            be submitted (safer to explicitely indicate when submission is ready).
        """
        self.notifier = Notifier(watchers if watchers is not None else {})
        self.validity = None

        # Not currently used:
        self.nb_valid_items = sum(item.is_valid() for item in items)

        self.key_to_items = {}
        self.items = []
        for item in items:
            self.add_item(item)

        self.tr = Translator(default_language=default_language,
                             supported_languages=supported_languages)
        self.tr.register('title', title)

        self.set_next_section_definition(next_section_definition)

        self.check_validity()

    def set_value_for_key(self, key, value, force=False):
        for item in self.items:
            if key in item.keys:
                item.set_value(key, value, force=force)

    def add_item(self, item, position=None, watch_validity=True):
        for key in item.keys:
            assert(key not in self.key_to_items)
            self.key_to_items[key] = item
        if watch_validity:
            item.notifier.add_watchers({'item_valid' :
                                        [LazyFunc(self.on_item_valid)],
                                        'item_invalid':
                                        [LazyFunc(self.on_item_invalid)]})
        self.items.insert(position if position is not None else len(self.items),
                          item)

    def remove_item(self, item):
        if item.keys is not None:
            for key in item.keys.keys():
                self.key_to_items.pop(key)
        self.items.remove(item)

    def has_key(self, key):
        return any(key in item.keys for item in self.items)

    def add_translations(self, other_section):
        self.tr.add_translations(other_section.tr)
        if len(self.items) != len(other_section.items):
            raise InconsistentSections()
        for item, other_item in zip(self.items, other_section.items):
            if len(item.keys) != len(other_item.keys) or \
               any(k != ok for k,ok in zip(item.keys.keys(),
                                           other_item.keys.keys())):
                raise InconsistentSections()
            item.tr.add_translations(other_item.tr)

    def set_supported_languages(self, languages):
        self.tr.set_supported_languages(languages)
        for item in self.items:
            item.set_supported_languages(languages)

    def set_next_section_definition(self, next_section_definition):
        self.next_section_definition = next_section_definition
        self.next_section_predicates = []
        predicate_always_true = Predicate('True')
        if next_section_definition is None or \
           isinstance(next_section_definition, str):
            self.next_section_predicates.append((next_section_definition,
                                                 predicate_always_true))
        else:
            for criterion in self.next_section_definition:
                if criterion is None or isinstance(criterion, str):
                    self.next_section_predicates.append((criterion,
                                                         predicate_always_true))
                else:
                    predicate_code, next_section = criterion
                    (self.next_section_predicates
                     .append((next_section, Predicate(predicate_code))))

    @staticmethod
    def from_dict(d):
        def make_item(sd):
            if 'default_language' not in sd:
                sd['default_language'] = d['default_language']
            if 'supported_languages' not in sd:
                sd['supported_languages'] = d['supported_languages']
            return FormItem(**sd)

        items = [make_item(sd) for sd in d['items']]
        return FormSection(items, d['default_language'],
                           d['supported_languages'], d.get('title', ''),
                           d.get('next_section_definition', None))

    def on_item_valid(self):
        self.nb_valid_items = min(len(self.items), self.nb_valid_items+1)
        self.check_validity()

    def on_item_invalid(self):
        # TODO: find proper to just count valid items
        self.nb_valid_items = max(0, self.nb_valid_items-1)
        self.check_validity()

    def __str__(self):
        return 'Section(%s)[%s]' % (self.tr['title'],
                                    ', '.join('%s'%i for i in self.items))

    def check_validity(self):
        # self.validity = self.nb_valid_items==len(self.items)
        self.validity = all(i.is_valid() for i in self.items)
        logger.debug2('%s - validity:  %s', self, self.validity)
        if not self.validity:
            for i in self.items:
                if not i.is_valid():
                    logger.debug2('item %s is invalid', i)
        signal = ['section_invalid', 'section_valid'][self.validity]
        logger.debug('%s notifies %s', self, signal)
        self.notifier.notify(signal)

    def to_dict(self):
        return {'title': copy(self.tr.trs['title']),
                'items' : [i.to_dict() for i in self.items],
                'default_language' : self.tr.language,
                'supported_languages' : list(self.tr.supported_languages),
                'next_section_definition' : copy(self.next_section_definition)}

    def set_language(self, language):
        logger.debug2('Set %s as section language', language)
        self.tr.set_language(language)
        for item in self.items:
            item.set_language(language)
        self.notifier.notify('language_changed')

    def __getitem__(self, key):
        return self.key_to_items[key]

    def is_valid(self):
        if not self.validity:
            for i in self.get_invalid_items():
                logger.debug2('item %s is invalid', i)
        return self.validity

    def get_invalid_items(self):
        return [i for i in self.items if not i.is_valid()]

    def reset(self):
        for item in self.items:
            item.reset()

    def next(self):
        current_items = {}
        try:
            for item in self.items:
                current_items.update(item.get_items())
        except InvalidValue:
            logger.debug2('Section is invalid, no transition')
            return None

        for section_label, predicate in self.next_section_predicates:
            if predicate(current_items):
                logger.debug2('Conditional transition to %s because '\
                             '"%s" matched', section_label, predicate.code)
                return section_label
            else:
                logger.debug2('No conditional transition to %s because '\
                             '"%s" did not match', section_label, predicate.code)

        logger.debug2('No matching transition criterion')
        return None

    def submit(self):
        d = {}
        for item in self.items:
            for k,v in item.submit().items():
                d[k] = v
        return d


class UnknownTrKey(Exception): pass
class LanguageError(Exception): pass
class UnsupportedLanguage(Exception): pass
class TrKeyAlreadyRegistered(Exception) : pass

class Translator():

    def __init__(self, default_language, supported_languages):
        """
        default_language (str)
        supported_languages (iterable of str)
        """
        self.supported_languages = set(supported_languages)

        self.trs = {}
        self.set_language(default_language)

    def add_supported_language(self, language):
        if not self.is_supported(language):
            self.supported_languages.add(language)
            for tr in self.trs.values():
                tr[language] = ''

    def set_supported_languages(self, languages):
        for language in languages:
            self.add_supported_language(language)

    def is_supported(self, language):
        return language in self.supported_languages

    def add_translations(self, other_tr):
        for key, translations in other_tr.trs.items():
            self.add_key_translations(key, translations)

    def add_key_translations(self, key, translations):
        if key not in self.trs:
            raise UnknownTrKey('Unknown translation key %s' % key)
        for language in translations.keys():
            self.add_supported_language(language)

        self.check_translations(key, translations)
        self.trs[key].update(translations)

    def register(self, key, translations):
        """
        key (str)
        translations (dict langague_str:translation_str)
        """
        if key in self.trs:
            raise TrKeyAlreadyRegistered('Key %s already registered' % key)
        if translations is None:
            translations = {l:key for l in self.supported_languages}
        elif translations=='':
            translations = {l:'' for l in self.supported_languages}

        self.check_translations(key, translations)

        self.trs[key] = translations

    def unregister(self, key):
        self.trs.pop(key, None)

    def check_translations(self, key, translations):
        if not isinstance(translations, dict):
            msg = 'Translations for key %s is not a dict: %s' % \
                (key, translations)
            raise TypeError(msg)

        diff = set(translations.keys()).difference(self.supported_languages)
        if len(diff) > 0:
            msg = 'Supported languages are: %s. Languages in '\
                'translation of key %s: %s' % \
                (', '.join(self.supported_languages), key,
                 ', '.join(translations.keys()))
            raise LanguageError(msg)

    def set_language(self, language):
        if language not in self.supported_languages:
            raise UnsupportedLanguage(language)
        self.language = language

    def __getitem__(self, key):
        if key not in self.trs:
            raise UnknownTrKey('Unknown translation key %s' % key)

        if self.trs[key] in [None, '']:
            return self.trs[key]

        if self.language not in self.trs[key]:
            logger.warning('Translation for "%s" not available in %s' % \
                           (key, self.language))

        return self.trs[key][self.language]


def unformat_boolean(s):
    if s=='True':
        return True
    elif s=='False' or s=='':
        return False
    else:
        raise ValueError('Boolean string must be "True", "False" or '\
                         'empty (%s given)'%s)

import html5lib
import html

def is_valid_html(html):
    from bs4 import BeautifulSoup # TODO: add dep
    html_ok = True
    html5parser = html5lib.HTMLParser(strict=True)
    try:
        html5parser.parse(html)
    except html5lib.html5parser.ParseError as e:
        soup = BeautifulSoup(html, 'html5lib')
        if len(soup('iframe')) > 0:
            for iframe in soup('iframe'):
                iframe.decompose()
            logger.warning('Ignored some faulty iframe during html check')
            try:
                html5parser.parse(soup.prettify())
            except Exception as e:
                logger.error('Invalid html: %s', e)
                html_ok = False
        else:
            html_ok = False
    return html_ok

class FormItem:
    """
    Validate and process and input entries, all having the same type.
    The basic validation is done directly on the input value
    (eg regexp, number interval...).
    """
    DATE_FORMAT = '%Y-%m-%d'
    QDATE_FORMAT = 'yyyy-MM-dd'
    DATETIME_FORMAT = '%Y-%m-%d %H:%M:%S.%f'

    VTYPES = {
        'text' : {
            'dtype_pd' : 'string',
            'unformat' : lambda s : s,
            'format' : lambda v : v,
            'message invalid format' : 'Enter a text',
            'validate value type' : lambda v : isinstance(v, str),
            },
        'html' : {
            'dtype_pd' : 'string',
            'unformat' : lambda s : s,
            'format' : lambda v : v,
            'message invalid format' : 'Enter a text',
            'validate value type' : is_valid_html,
            },
        'user_name' : {
            'dtype_pd' : 'string',
            'unformat' : lambda s : s,
            'format' : lambda v : v,
            'message invalid format' : 'Enter a user name',
            'validate value type' : lambda v : isinstance(v, str),
        },
         'int' : {
             'dtype_pd' : 'int',
             'unformat' : lambda s : int(s),
             'format' : lambda i : '%d' % i,
             'message invalid format' : 'Enter an integer',
             'validate value type' : lambda v : isinstance(v, int),
         },
        'int64' : {
             'dtype_pd' : 'int64',
             'unformat' : lambda s : np.int64(s),
             'format' : lambda i : '%d' % i,
             'message invalid format' : 'Enter an integer',
             'validate value type' : lambda v : isinstance(v, np.int64),
         },
         'boolean' : {
             'dtype_pd' : 'boolean',
             'unformat' : unformat_boolean,
             'format' : lambda b : str(b),
             'message invalid format' : 'Enter a boolean',
             'validate' : lambda v : isinstance(v, bool),
         },
        'number' : {
            'dtype_pd' : 'float',
            'unformat' : lambda s : float(s),
            'format' : lambda n : '%f' % n,
            'message invalid format' : ('Enter a number using a dot ' +\
                                        'as decimal separator if needed.'),
            'validate' : lambda v : isinstance(v, float),
         },
         'date' : {
             'dtype_pd' : 'datetime64[ns]',
             'unformat' : lambda s : date.fromisoformat(s),
             'format' : lambda d : d.strftime(FormItem.DATE_FORMAT),
             'message invalid format' : 'Enter a date as "YYYY-MM-DD"',
             'validate' : lambda v : isinstance(v, datetime.date),
         },
         'datetime' : {
             'dtype_pd' : 'datetime64[ns]',
             'unformat' : \
             lambda s : datetime.strptime(s, FormItem.DATETIME_FORMAT),
             'format' : \
             lambda d : d.strftime(FormItem.DATETIME_FORMAT),
             'message invalid format' : ('Enter date and time as ' \
                                         '"YYYY-MM-DD hh:mm:ss"'),
             'validate' : lambda v : isinstance(v, datetime.date),
         }
    }

    GENERATORS = {
        'uuid4' : lambda ii: uuid4().hex,
        'uuid1' : lambda ii: uuid1().hex,
        None : lambda ii: '',
        'timestamp_creation' : \
        lambda ii: FormItem.VTYPES['datetime']['format'](ii.creation_date),
        'timestamp_submission' : \
        lambda ii: FormItem.VTYPES['datetime']['format'](datetime.now()),
    }

    def __init__(self, keys, default_language, supported_languages,
                 label=None, vtype='text', title=None, description='',
                 init_values=None, regexp='[\s\S]*',
                 regexp_invalid_message='',
                 allow_empty=True, choices=None, other_choice_label=None,
                 unique=False, unique_view=None, generator=None,
                 hidden=None, access_level=UserRole.VIEWER,
                 editable=True, freeze_on_update=False,
                 number_interval=None, nb_lines=1, watchers=None):
        """
        watchers : dict(event : [callables])
        number_interval : args pass to pandas.Interval
        choices : dict(key:dict(language:showntext))
        """
        # TODO: remove unique_view
        logger.debug2('Create FormItem with keys: %s, title: %s', keys, title)
        self.notifier = Notifier(watchers if watchers is not None else {})

        self.keys = keys if keys is not None else {}

        self.label = ('%s' % label if label is not None else
                      ' | '.join(self.keys.keys()))

        self.tr = Translator(default_language=default_language,
                             supported_languages=supported_languages)

        for key, key_tr in self.keys.items():
            FormItem.validate_key(key)
            self.tr.register(key, key_tr)

        if title is None and len(self.keys)==1 and self.keys is not None:
            key, key_tr = next(iter(self.keys.items()))
            if key_tr is not None:
                title = key_tr
            else:
                title = {l:key for l in supported_languages}
        self.tr.register('title', title)
        self.tr.register('description', description)

        if vtype not in FormItem.VTYPES:
            raise TypeError(vtype)
        self.vtype = vtype
        vtype_tools = FormItem.VTYPES[self.vtype]
        self.unformat = vtype_tools['unformat']
        self.format = vtype_tools['format']
        self.invalid_vtype_format_message = vtype_tools['message invalid format']
        self.dtype_pd = vtype_tools['dtype_pd']

        self.set_regexp(regexp, regexp_invalid_message)

        self.choices = None
        self.set_choices(choices, other_choice_label)

        self.unique = unique
        self.unique_validator = None

        self.number_interval_param = number_interval
        if number_interval is not None:
            assert(vtype == 'int' or vtype == 'number')
        else:
            number_interval = {'closed' : 'neither'}
        for side in ['left', 'right']:
            if side not in number_interval:
                number_interval[side] = [-np.inf, np.inf][side=='right']
        self.number_interval = pd.Interval(**number_interval)

        self.allow_None = allow_empty

        self.freeze_on_update = freeze_on_update
        self.set_editable(editable)

        self.access_level = (access_level if isinstance(access_level, UserRole) \
                             else UserRole[access_level])
        if hidden is not None:
            logger.warning('hidden parameter of FormItem is deprecated.'
                           'Use access_level=UserRole instead.')
            if hidden:
                self.access_level = UserRole.MANAGER
            else:
                self.access_level = UserRole.VIEWER

        self.nb_lines = nb_lines

        self.set_init_values(init_values)
        self.values_str = {}
        self.generator = generator

        self.input_callback = None

        self.validity = None

        self.user = None

        self.creation_date = datetime.now()
        self.reset(force=True)

    def set_supported_languages(self, languages):
        self.tr.set_supported_languages(languages)

    def set_init_values(self, init_values):
        if init_values is not None:
            assert(isinstance(init_values, dict))
            assert(all(k1==k2 for k1,k2 in zip(init_values.keys(),
                                               self.keys.keys())))
        self.init_values = init_values

    def set_regexp(self, regexp_str, regexp_invalid_message=''):
        self.regexp = re.compile(regexp_str)
        self.regexp_invalid_message = regexp_invalid_message \
            if len(regexp_invalid_message)>0 else \
            'Invalid format, must verify regexp "%s"' % regexp_str

    @staticmethod
    def validate_key(key):
        if not key.isidentifier() and \
           key not in ('__entry_id__', '__submission__', '__origin_id__',
                       '__update_idx__'):
            raise InvalidKey('Invalid key label "%s". It must a valid python '\
                             'identifier and not be "__entry_id__", '\
                             '"__submission__" or "__origin_id__"' % key)

    def set_choices(self, choices, other_choice_label=None):
        # TODO: test choices validity! use set_input_str(choice) and check validity
        if self.choices is not None:
            assert(len(self.choices)>0) # TODO insure this
            for value,label in self.choices.items():
                self.tr.unregister(value) # TODO
        self.tr.unregister('other_choice')

        self.allow_other_choice = False
        logger.debug2('Set choice -- other_choice_label: %s',
                      other_choice_label)
        if isinstance(other_choice_label, dict) and \
           all(len(tr)==0 for tr in other_choice_label.values()):
            other_choice_label = None
        if choices is not None:
            for value,translation in choices.items():
                self.tr.register(value, translation)
            if other_choice_label is not None and len(other_choice_label)>0:
                 self.allow_other_choice = True
                 self.tr.register('other_choice', other_choice_label)
            else:
                self.tr.register('other_choice', '')
        else:
            self.tr.register('other_choice', '')

        self.choices = choices

    def set_unique_validator(self, validator):
        assert(self.unique)
        self.unique_validator = validator
        for key in self.keys:
            try:
                self.validate_unique(key, self.get_value(key))
            except InvalidValue:
                pass

    def validate_unique(self, key, value):
        if self.unique:
            if self.unique_validator is None:
                logger.debug2('Cannot check uniqueness of %s (no validator set)',
                             key)
                return True
            else:
                logger.debug2('Check uniqueness of %s', key)
                if not self.unique_validator(key=key, value=value):
                    self._set_validity(False, 'Duplicate entry', key)
                    return False
        return True

    def to_dict(self):
        def _tr(k):
            return {language : k for language in self.tr.supported_languages}
        return {'keys' : copy(self.keys),
                'label' : self.label,
                'default_language' : self.tr.language,
                'supported_languages' : list(self.tr.supported_languages),
                'vtype' : self.vtype,
                'title' : copy(self.tr.trs.get('title', None)),
                'description' : copy(self.tr.trs.get('description', None)),
                'regexp' : self.regexp.pattern,
                'regexp_invalid_message' : self.regexp_invalid_message,
                'allow_empty' : self.allow_None,
                'choices' : ({k : if_none(copy(v), _tr(k))
                              for k,v in self.choices.items()}
                             if self.choices is not None else None),
                'other_choice_label' : copy(self.tr.trs.get('other_choice', None)),
                'init_values' : copy(self.init_values),
                'unique' : self.unique,
                'generator' : self.generator,
                'access_level' : self.access_level.name,
                'editable' : self.editable,
                'freeze_on_update' : self.freeze_on_update,
                # TODO: resolve from number_interval:
                'number_interval' : copy(self.number_interval_param),
                'nb_lines' : self.nb_lines}

    def set_editable(self, flag):
        self.editable = flag

    def reset(self, force=False):
        logger.debug2('Reset %s (force=%s)', self, force)

        if len(self.keys) == 0:
            self.validity = True
            return

        if self.editable or force:
            for key in self.keys:
                if self.generator is not None and \
                   not self.generator.endswith('submission'):
                    logger.debug2('%s: Use generator %s for key %s',
                                 self, self.generator, key)
                    self.set_input_str(FormItem.GENERATORS[self.generator](self),
                                       key, force=force)
                    # TODO utest that value is generated even if
                    # init value is given
                elif self.init_values is not None:
                    self.set_value(key, self.init_values[key], force=force)
                #     # logger.debug('%s: Use init value for key %s', self, key)
                #     if self.choices is not None and \
                #        (not self.allow_other_choice or \
                #         str(self.init_values[key]) in self.choices):
                #         self.set_input_str(self.tr[str(self.init_values[key])],
                #                            force=force)
                #     else:
                #         self.set_input_str(self.format(self.init_values[key]),
                #                            force=force)
                # elif self.choices is not None:
                #     self.set_input_str(self.tr[next(iter(self.choices))],
                #                        force=force)
                else:
                    # empty string maps to None
                    # logger.debug('%s: Set empty string for key %s', self, key)
                    self.set_input_str('', key, force=force)
        else:
            for key in self.keys:
                self.validate(key)

    def __str__(self):
        return 'item(%s)' % ','.join(self.keys)

    def set_language(self, language):
        logger.debug2('Set %s as language for %s', language, self)
        values = self.get_items(error_when_invalid=False)
        self.tr.set_language(language)
        for k,v in values.items():
            self.set_value(k, v, force=True)
        self.notifier.notify('language_changed')

    def _set_validity(self, validity, message, key=None):

        if not validity:
            logger.debug(message + (' for key: '+key \
                                    if key is not None else ''))
        # logger.debug('%s - validity: %s', self, validity)

        self.validity = validity
        self.validity_message = message

        signal = ['item_invalid', 'item_valid'][validity]
        logger.debug2('%s notifies %s', self, signal)
        self.notifier.notify(signal)

    def validate(self, key):
        assert(key in self.keys)

        value_str = self.values_str[key]
        if (self.generator is not None and \
            self.generator.endswith('submission')) or \
            (self.vtype == 'user_name') or \
            (len(value_str)==0 and self.allow_None):
            self._set_validity(True, '', key)
            return

        if self.choices is not None :
            current_choices = {self.tr[k]:k for k in self.choices}
            if value_str not in current_choices and not self.allow_other_choice:
                choices_str = ', '.join(["'%s'" %c for c in current_choices])
                logger.debug2('Value of %s not in choices (%s)', self,
                             choices_str)
                # from IPython import embed; embed()
                self._set_validity(False, 'Value must be one of "%s"' % \
                                   choices_str, key)
                return
            else:
                value_str = (current_choices[value_str]
                             if value_str in current_choices
                             else value_str)

        if len(value_str)==0 and not self.allow_None:
            logger.debug('%s cannot be empty', self)
            self._set_validity(False, 'A value is required', key)
            return

        if not(len(value_str)==0 and self.allow_None):
            if  self.regexp.match(value_str) is None:
                logger.warning('Regexp not verified for %s', self)
                self._set_validity(False, self.regexp_invalid_message, key)
                return

        try:
            value = self.unformat(value_str)
            logger.debug2('Unformated value for %s: %s', self, value)
        except ValueError:
            self._set_validity(False, self.invalid_vtype_format_message, key)
            return

        if self.vtype == 'number' or self.vtype == 'int':
            if value not in self.number_interval:
                self._set_validity(False, 'Value must be in %s' % \
                                   self.number_interval, key)
                return

        if not self.validate_unique(key, value): # validity msg is set there
            return

        self._set_validity(True, '', key)


    def get_validity_message(self):
        return self.validity_message

    def value_to_str(self, key=None):
        if key is None:
            assert(len(self.keys)==1)
            key = next(iter(self.keys))

        if self.values_str[key] is None:
            return ''

        value_str = self.values_str[key]
        if self.choices is not None:
            current_choices = {self.tr[k]:k for k in self.choices}
            value_str = current_choices.get(value_str, value_str)

        return self.format(self.unformat(value_str))

    def set_value(self, key, value, force=False):
        if self.choices is not None and \
           str(value) in self.choices:
            value_str = self.tr[str(value)]
        else:
            value_str = (self.format(value) \
                         if (value is not None and not pd.isna(value)) \
                         else '')
        self.set_input_str(value_str, key, force=force)

    def get_value(self, key=None, error_when_invalid=True):
        """ Return the current value, without using submission generator """
        if len(self.keys) == 0:
            return None

        if key is None:
            assert(len(self.keys)==1)
            key = next(iter(self.keys))

        if not self.validity and error_when_invalid:
            raise InvalidValue("%s: %s" %(key,self.validity_message))

        value_str = self.values_str[key]
        if self.choices is not None:
            current_choices = {self.tr[k]:k for k in self.choices}
            value_str = current_choices.get(value_str, value_str)

        return self.unformat(value_str) if len(value_str)>0 else None

    def get_items(self, error_when_invalid=True):
        return {k : self.get_value(k, error_when_invalid) for k in self.keys}

    def split_qdatetime_str(self, key):
        vdate = None
        try:
            vdate = self.get_value(key)
        except InvalidValue:
            pass
        if vdate is None:
            return (date.today().strftime(FormItem.DATE_FORMAT),
                    FormItem.QDATE_FORMAT, None, None)
        hours, mins = 0, 0
        if self.vtype == 'datetime':
            hours = vdate.hour
            mins = vdate.minute
            vdate = vdate.date()
        return vdate.strftime(FormItem.DATE_FORMAT), FormItem.QDATE_FORMAT, \
            hours, mins

    def submit(self):
        """
        Apply submission generator if any and return all values
        as a dict of {key:value}
        """
        if self.generator is not None and \
           (self.generator.endswith('submission') or \
            self.generator == 'timestamp_creation'):
            for key in self.keys:
                self.set_input_str(FormItem.GENERATORS[self.generator](self), key)
        elif self.vtype == 'user_name':
            self.set_input_str(self.user)
        return self.get_items()

    def set_user(self, user):
        self.user = user
        if self.vtype == 'user_name':
            self.set_input_str(self.user)

    def set_input_str(self, s, key=None, use_callback=True,
                      force=False):
        logger.debug('%s: set input str of key %s', self, key)

        if key is None:
            assert(len(self.keys)==1)
            key = next(iter(self.keys))
        assert(key in self.keys)

        if not self.editable and not force:
            raise NotEditableError()

        self.values_str[key] = s
        self.validate(key)

        if use_callback and self.input_callback is not None:
            logger.debug2('Calling callback after setting input of %s', key)
            self.input_callback(item_key=key, input_str=s)

    def set_input_callback(self, callback):
        """ callback(item_key, input_str) """
        self.input_callback = callback

    def is_valid(self):
        return self.validity


class TestForm(unittest.TestCase):

    def setUp(self):
        self.label = 'TestForm'
        self.df = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0005', 'CE0006']),
            ('TODO', [True, False, False]),
            ('Age', [22, 50, 25]),
        ]))
        self.df.set_index('Participant_ID', inplace=True)

        self.df_ts = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0004', 'CE0006']),
            ('Age', [22, 50, 24]),
            ('Timestamp_Submission',
             [datetime(2020,1,2,13,37), datetime(2021,2,2,13,37),
              datetime(2020,1,5,13,37)])
        ]))

        logger.setLevel(logging.DEBUG)
        self.tmp_dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.tmp_dir)

    def test_nexts(self):
        ns = nexts(['a', 'b', 'c', 'd'])
        self.assertEqual(ns['b'], 'c')
        self.assertIsNone(ns['d'])

    def test_empty_title(self):
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'})]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'}, title='')
        self.assertEqual(form.tr['title'], '')

    def test_title(self):
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'})]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    title={'French':'Titre de formulaire'})
        self.assertEqual(form.tr['title'], 'Titre de formulaire')


    def test_reset(self):
        # TODO: test with all dtypes
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'},
                          allow_empty=False),
                 FormItem({'Age' :
                           {'French':'Age en année'}},
                          default_language='French',
                          supported_languages={'French'},
                          vtype='int')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, title='', default_language='French',
                    supported_languages={'French'})
        pid = 'CE0011'
        form['section1']['Participant_ID'].set_input_str(pid)
        form.reset()
        self.assertRaises(InvalidValue,
                          form['section1']['Participant_ID'].get_value)
        form['section1']['Participant_ID'].set_input_str(pid)
        age = 44
        form['section1']['Age'].set_input_str(str(age))
        entry = form.submit()

        self.assertEqual(entry['Participant_ID'], pid)
        self.assertEqual(entry['Age'], age)

    def test_set_values_from_entry(self):
        # TODO: check unique validation
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'}),
                 FormItem({'TODO' :
                           {'French':'Faire ou ne pas faire'}},
                          vtype='boolean',
                          default_language='French',
                          supported_languages={'French'},
                          choices={'True':{'French' : 'Le faire'},
                                   'False':{'French' : 'NE PAS Le faire'}}),
                 FormItem({'Age' :
                           {'French':'Age en année'}},
                          default_language='French',
                          supported_languages={'French'},
                          vtype='int')]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, title='', default_language='French',
                    supported_languages={'French'})
        entry_dict = self.df.loc[['CE0004']].reset_index().to_dict('records')[0]
        form.set_values_from_entry(entry_dict)
        self.assertEqual(form['section1']['Participant_ID'].get_value(),
                         'CE0004')
        self.assertEqual(form['section1']['Age'].get_value(),
                         self.df.at['CE0004','Age'])
        form['section1']['Participant_ID'].set_input_str('CE0333')
        age = 44
        form['section1']['Age'].set_input_str(str(age))
        entry = form.submit()
        self.assertEqual(entry['Age'], age)

    def test_no_submission_when_invalid(self):
        items = [FormItem({'Participant_ID' :
                           {'French':'Code Participant'}},
                          default_language='French',
                          supported_languages={'French'}),
                 FormItem({'Age' :
                           {'French':'Age en année'}},
                          default_language='French',
                          supported_languages={'French'},
                          vtype='int', allow_empty=False)]
        sections = {'section1' : FormSection(items, default_language='French',
                                             supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'})
        self.assertFalse(form.is_valid())
        self.assertRaises(InvalidForm, form.submit)

    def test_default_next_sections(self):
        items1 = [FormItem({'Participant_ID' :
                            {'French':'Code Participant'}},
                           default_language='French',
                           supported_languages={'French'},
                           allow_empty=False)]
        items2 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=False)]
        items3 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=True)]
        sections = {'section1' :
                    FormSection(items1,
                                default_language='French',
                                supported_languages={'French'}),
                    'section2' :
                    FormSection(items2, default_language='French',
                                supported_languages={'French'}),
                    'section3' :
                    FormSection(items3, default_language='French',
                                supported_languages={'French'})}
        form = Form(sections, default_language='French',
                    supported_languages={'French'})

        print("utest CP1: form['section1'].next_section_definition: ",
              form['section1'].next_section_definition)
        print("utest CP1: form['section1'].next_section_predicates: ",
              form['section1'].next_section_predicates)
        # Fill first section (section1)
        self.assertFalse(form.is_valid())
        self.assertFalse(form.ready_to_submit())
        self.assertRaises(InvalidSection, form.to_next_section)
        form['section1']['Participant_ID'].set_input_str('CE0009')
        self.assertTrue(form.is_valid())
        self.assertFalse(form.ready_to_submit())

        print("utest CP2: form['section1'].next_section_definition: ",
              form['section1'].next_section_definition)
        print("utest CP2: form['section1'].next_section_predicates: ",
              form['section1'].next_section_predicates)

        self.assertEqual(form.next_section(), 'section2')
        self.assertEqual(form.previous_section(), None)
        # Go to 2nd section
        form.to_next_section()
        self.assertFalse(form.is_valid())
        self.assertFalse(form.ready_to_submit())
        self.assertEqual(form.next_section(), None)
        self.assertEqual(form.previous_section(), 'section1')
        form['section2']['Age'].set_input_str('55')
        self.assertTrue(form.is_valid())
        self.assertEqual(form.next_section(), 'section3')
        self.assertFalse(form.ready_to_submit())
        # Go to 3rd section
        form.to_next_section()
        self.assertTrue(form.is_valid())
        self.assertEqual(form.next_section(), '__submit__')
        self.assertTrue(form.ready_to_submit())
        self.assertEqual(form.previous_section(), 'section2')
        entry = form.submit()
        self.assertEqual(entry['Participant_ID'], 'CE0009')
        self.assertEqual(entry['Age'], None)

    def test_section_conditional_transitions(self):
        """ Test transitions based on value criteria """
        items1 = [FormItem({'Participant_ID' :
                            {'French':'Code Participant'}},
                           default_language='French',
                           supported_languages={'French'},
                           allow_empty=False)]
        items2 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=False)]
        items3 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=True)]

        sections = {'section1' :
                    FormSection(items1,
                                default_language='French',
                                supported_languages={'French'},
                                next_section_definition=[
                                    ("Participant_ID is not None and "\
                                     "Participant_ID=='CE0009'", 'section_CE0009'),
                                    'section_default'
                                ]),
                    'section_CE0009' :
                    FormSection(items2, default_language='French',
                                supported_languages={'French'},
                                next_section_definition='__submit__'),
                    'section_default' :
                    FormSection(items3, default_language='French',
                                supported_languages={'French'},
                                next_section_definition='__submit__')}

        form = Form(sections, default_language='French',
                    supported_languages={'French'})
        # Fill first section (section1)
        self.assertFalse(form.is_valid())
        self.assertFalse(form.ready_to_submit())
        self.assertRaises(InvalidSection, form.to_next_section)
        form['section1']['Participant_ID'].set_input_str('CE0009')
        self.assertTrue(form.is_valid())
        self.assertFalse(form.ready_to_submit())
        self.assertEqual(form.next_section(), 'section_CE0009')
        self.assertEqual(form.previous_section(), None)
        # Go to 2nd section (section_CE0009)
        form.to_next_section()
        self.assertFalse(form.is_valid())
        self.assertFalse(form.ready_to_submit())
        self.assertEqual(form.next_section(), None)
        self.assertEqual(form.previous_section(), 'section1')
        form['section_CE0009']['Age'].set_input_str('55')
        self.assertTrue(form.is_valid())
        self.assertTrue(form.ready_to_submit())
        # Go back to 1st section (section1)
        form.to_previous_section()
        self.assertEqual(form.section_path, ['section1'])
        form['section1']['Participant_ID'].set_input_str('CE0010')
        self.assertEqual(form.next_section(), 'section_default')
        # Cannot go further back
        self.assertEqual(form.previous_section(), None)
        form.to_previous_section()
        self.assertEqual(form.section_path, ['section1'])
        # Go to 3rd section (section_default)
        form.to_next_section()
        self.assertTrue(form.is_valid())
        self.assertTrue(form.ready_to_submit())
        form['section_default']['Age'].set_input_str('77')

        entry = form.submit()
        self.assertEqual(entry['Participant_ID'], 'CE0010')
        self.assertEqual(entry['Age'], 77)

    def get_test_form(self, watchers=None):
        items1 = [FormItem({'Participant_ID' :
                            {'French':'Code Participant'}},
                           default_language='French',
                           supported_languages={'French'},
                           regexp='^CE[0-9]{4}$',
                           allow_empty=False)]
        items2 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=False)]
        items3 = [FormItem({'Age' :
                            {'French':'Age en année'}},
                           default_language='French',
                           supported_languages={'French'},
                           vtype='int', allow_empty=True)]

        sections = {'section1' :
                    FormSection(items1,
                                title={'French':'section1'},
                                default_language='French',
                                supported_languages={'French'},
                                next_section_definition=[
                                    ('Participant_ID is not None and '\
                                     'Participant_ID=="CE0009"','section_CE0009'),
                                    'section_default'
                                ]),
                    'section_CE0009' :
                    FormSection(items2, title={'French':'section_CE0009'},
                                default_language='French',
                                supported_languages={'French'},
                                next_section_definition='__submit__'),
                    'section_default' :
                    FormSection(items3, title={'French':'section_default'},
                                default_language='French',
                                supported_languages={'French'},
                                next_section_definition='__submit__')}

        form = Form(sections, default_language='French',
                    supported_languages={'French'},
                    watchers=watchers)
        logger.debug('utest: finish init of test form')
        return form

    def test_notifications(self):
        received_signals = []
        def record_signal(signal):
            received_signals.append(signal)
        watchers = {s: [LazyFunc(record_signal,s)] \
                    for s in ['previous_section_available',
                              'previous_section_not_available',
                              'next_section_available',
                              'next_section_not_available',
                              'ready_to_submit', 'not_ready_to_submit']}

        form = self.get_test_form(watchers)
        logger.debug('utest: after form init, current section is section1, '\
                     'invalid because Participant_ID==""')
        self.assertEqual(set(received_signals),
                         {'next_section_not_available',
                          'previous_section_not_available',
                          'not_ready_to_submit'})
        received_signals.clear()
        form['section1']['Participant_ID'].set_input_str('GG')
        logger.debug('utest: section1 still invalid because '\
                     'Participant_ID==GG')
        self.assertEqual(set(received_signals),
                         {'next_section_not_available',
                          'previous_section_not_available',
                          'not_ready_to_submit'})
        received_signals.clear()
        form['section1']['Participant_ID'].set_input_str('CE0001')
        logger.debug('utest: section1 became valid because '\
                     'Participant_ID==CE0001')
        self.assertEqual(set(received_signals),
                         {'next_section_available',
                          'previous_section_not_available',
                          'not_ready_to_submit'})
        logger.debug('utest: going to section_default, valid and final')
        received_signals.clear()
        form.to_next_section()
        self.assertEqual(set(received_signals),
                         {'next_section_not_available',
                          'previous_section_available',
                          'ready_to_submit'})
        logger.debug('utest: going back to section1, still valid')
        received_signals.clear()
        form.to_previous_section()
        self.assertEqual(set(received_signals),
                         {'next_section_available',
                          'previous_section_not_available',
                          'not_ready_to_submit'})
        logger.debug('utest: setting Participant_ID=CE0009 of section1, so '\
                     'that section_CE0009 is the next one')
        form['section1']['Participant_ID'].set_input_str('CE0009')
        logger.debug('utest: going to section_CE0009 that is invalid '\
                     '(empty Age), and final')
        received_signals.clear()
        form.to_next_section()
        self.assertEqual(set(received_signals),
                         {'next_section_not_available',
                          'previous_section_available',
                          'not_ready_to_submit'})
        received_signals.clear()
        logger.debug('utest: setting Age=55 in section_CE0009 so that '\
                     'form becomes valid and final')
        form['section_CE0009']['Age'].set_input_str('55')
        self.assertEqual(set(received_signals), {'ready_to_submit',
                                                 'previous_section_available',
                                                 'next_section_not_available'})



    def test_set_transitions(self):

        dlg = 'English'
        slg = {'English'}
        PARAGRAPH_NB_LINES = 10
        expected_form_def = {
            'title' : {dlg : 'Form title'},
            'description' : {dlg : 'Form description'},
            'default_language' : dlg,
            'supported_languages' : slg,
            'sections' : {
                '__section_0__' : {
                    'title' : '',
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : {'S1_Q1' :
                                      {dlg : 'section 1 question 1'}},
                            'description' : {
                                dlg : 'description of S1_Q1'
                            },
                            'choices' : {
                                'go_s2' : {dlg : 'go to section 2'},
                                'go_s3' : {dlg : 'go to section 3'}},
                            'allow_empty' : False
                        }],
                    },
                'section_2' : {
                    'title' : {dlg : 'This is section 2'},
                    'description' : {
                        dlg : 'description of section 2'
                    },
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : {'S2_Q1' :
                                      {dlg : 'section 2 question 1'}},
                            'description' : {
                                dlg : 'description of s2q1'
                            },
                        }],
                },
                'section_3' : {
                    'title' : {dlg : 'This is section 3'},
                    'description' : {
                        dlg : 'description of section 3'
                    },
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : {'S3_Q1' :
                                      {dlg : 'section 3 question 1'}},
                            'description' : {
                                dlg : 'description of s3q1'
                            },
                        }],
                } # end of section
            } # end of list of sections
        } # end of form definition
        form = Form.from_dict(expected_form_def)

        transitions_str = """
{'__section_0__' : [
    ("S1_Q1=='go_s2'", 'section_2'),
    ("S1_Q1=='go_s3'", 'section_3')
 ],
 'section_3' : '__submit__',
}""".strip()
        form.set_transitions(eval(transitions_str))
        self.assertFalse(form.ready_to_submit())
        self.assertIsNone(form.next_section())

        form['__section_0__']['S1_Q1'].set_value('S1_Q1', 'go_s3')
        self.assertEqual(form.next_section(),'section_3')

        form['__section_0__']['S1_Q1'].set_value('S1_Q1', 'go_s2')
        self.assertEqual(form.next_section(),'section_2')

        form.to_next_section()
        self.assertFalse(form.ready_to_submit())
        self.assertEqual(form.next_section(), 'section_3')

        form.to_next_section()
        self.assertTrue(form.ready_to_submit())
        self.assertEqual(form.next_section(), '__submit__')

        result = form.submit()
        self.assertEqual(result, {'S1_Q1' : 'go_s2',
                                  'S2_Q1' : None,
                                  'S3_Q1' : None,
        })

    def test_from_gform_sections(self):
        dlg = 'English'
        slg = {'English'}
        PARAGRAPH_NB_LINES = 10
        expected_form_def = {
            'title' : {dlg : 'Form title'},
            'default_language' : dlg,
            'supported_languages' : slg,
            'sections' : {
                '__section_0__' : {
                    'title' : '',
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : None,
                            'title' : {dlg : 'Section description'},
                            'description' : {dlg : 'Form description'},
                            'vtype' : 'text'
                        },
                        {
                            'keys' : {'S1_Q1' :
                                      {dlg : 'section 1 question 1'}},
                            'description' : {
                                dlg : 'description of S1_Q1'
                            },
                            'choices' : {
                                'go_s2' : {dlg : 'go to section 2'},
                                'go_s3' : {dlg : 'go to section 3'}},
                            'allow_empty' : False
                        }],
                    },
                'section_2' : {
                    'title' : {dlg : 'This is section 2'},
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : None,
                            'title' : {dlg : 'Section description'},
                            'description' : {dlg : 'description of section 2'},
                            'vtype' : 'text'
                        },
                        {
                            'keys' : {'S2_Q1' :
                                      {dlg : 'section 2 question 1'}},
                            'description' : {
                                dlg : 'description of s2q1'
                            },
                        }],
                },
                'section_3' : {
                    'title' : {dlg : 'This is section 3'},
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : None,
                            'title' : {dlg : 'Section description'},
                            'description' : {dlg : 'description of section 3'},
                            'vtype' : 'text'
                        },
                        {
                            'keys' : {'S3_Q1' :
                                      {dlg : 'section 3 question 1'}},
                            'description' : {
                                dlg : 'description of s3q1'
                            },
                        }],
                } # end of section
            } # end of list of sections
        } # end of form definition
        expected_form = Form.from_dict(expected_form_def)

        # google form: https://docs.google.com/forms/d/1MNlo_JF0-5G0RAal1R5R5agVjcIs0ohUFlzAQ2-nxg4/edit

        gform_json_fn = op.join(self.tmp_dir, 'gform.json')
        with open(gform_json_fn, 'w') as fout:
            fout.write('{"metadata":{"title":"Form title","id":"1dOsPTG7vJVv9vkBKVCsK3M1bl9k6VgggSEPxvEpuhBU","description":"Form description","publishedUrl":"https://docs.google.com/forms/d/e/1FAIpQLSfn1S_fmS9nv6yQ1eZAuFzmxlKkqkYYKVygjv_E18yWAZFqOw/viewform","editorEmails":["covepic.research@gmail.com"],"count":5,"confirmationMessage":"","customClosedFormMessage":""},"items":[{"type":"MULTIPLE_CHOICE","title":"S1_Q1:: section 1 question 1","description":"description of S1_Q1","required":true,"allow_other_choice":false,"choices":["go_s2:: go to section 2","go_s3:: go to section 3"]},{"type":"PAGE_BREAK","title":"section_2:: This is section 2","description":"description of section 2","pageNavigationType":"CONTINUE"},{"type":"TEXT","title":"S2_Q1:: section 2 question 1","description":"description of s2q1","required":false},{"type":"PAGE_BREAK","title":"section_3:: This is section 3","description":"description of section 3","pageNavigationType":"SUBMIT"},{"type":"TEXT","title":"S3_Q1:: section 3 question 1","description":"description of s3q1","required":false}],"count":5}')

        form = Form.from_gform_json_file(gform_json_fn, 'English',
                                         use_item_title_as_key=True)
        if form != expected_form:
            self.show_form_diff(form, expected_form)
        self.assertEqual(form, expected_form)

        form.set_values_from_entry({'S1_Q1' : 'go_s3'})
        self.assertTrue(form.is_valid())
        self.assertFalse(form.ready_to_submit())

        self.assertEqual(form.next_section(), 'section_2')
        form.to_next_section()
        self.assertFalse(form.ready_to_submit())

        self.assertEqual(form.next_section(), 'section_3')
        form.to_next_section()
        self.assertTrue(form.ready_to_submit())

        result = form.submit()
        self.assertEqual(result['S1_Q1'], 'go_s3')
        self.assertEqual(result['S2_Q1'], None)
        self.assertEqual(result['S3_Q1'], None)

    def test_from_gform_items(self):
        dlg = 'French'
        slg = {'French'}
        PARAGRAPH_NB_LINES = 10
        expected_form_def = {
            'title' : {dlg : 'Form title'},
            'default_language' : dlg,
            'supported_languages' : slg,
            'sections' : {
                '__section_0__' : {
                    'title' : '',
                    'default_language' : dlg,
                    'supported_languages' : slg,
                    'items' : [
                        {
                            'keys' : None,
                            'title' : {dlg : 'Section description'},
                            'description' : {dlg : 'Form description'},
                            'vtype' : 'text'
                        },
                        {
                            'keys' : {'required_short_answer' :
                                      {dlg : 'required short answer'}},
                            'description' : {
                                dlg : 'description of short answer'
                            },
                            'allow_empty' : False,
                        },
                        {'keys' : {'paragraph' : {dlg : 'paragraph'}},
                         'description' : {
                                dlg : 'description of paragraph'
                         },
                         'nb_lines' : PARAGRAPH_NB_LINES
                        },
                        {'keys' : {'multiple_choice' :
                                   {dlg : 'Choix multiple'}},
                         'description' : {
                                dlg : 'description of multiple choice'
                         },
                         'choices' : {
                             'choice 1' : {dlg : 'choice 1'},
                             'choice 2' : {dlg : 'choice 2'}
                         },
                         'other_choice_label' : {dlg : 'Autre'},
                        },
                        {
                        'keys' : {
                            'c1' : {dlg : 'check 1'},
                            'check_2' : {dlg : 'check 2'},
                        },
                        'title' : {dlg: 'à cocher'},
                        'vtype' : 'boolean',
                            'description' : {
                            dlg : 'description of checkboxes'
                            },
                        },
                        {'keys' : {'dropdown' : {dlg : 'Une liste déroulante'}},
                         'description' : {
                                dlg : 'description of dropdown'
                         },
                         'choices' : {
                             'déroulant 1' : {dlg : 'déroulant 1'},
                             'déroulant 2' : {dlg : 'déroulant 2'}},
                        },
                        {'keys' : {'interview_date' :
                                   {dlg : "Date convenue pour l'interview"}},
                         'description' : {
                                dlg : "description of date"
                         },
                         'vtype' : 'date',
                        },
                        {'keys' : {'date_and_time' : {dlg : 'date and time'}},
                         'description' : {
                                dlg : "description of date and time"
                         },
                         'vtype' : 'datetime',
                        },
                        {'keys' : None,
                         'description' : {
                             dlg : "description of title item"
                         },
                         'title' : {dlg : 'A title item'},
                        },
                    ] # end of list of items
                } # end of section
            } # end of list of sections
        } # end of form definition
        expected_form = Form.from_dict(expected_form_def)

        # google form: https://docs.google.com/forms/d/1MNlo_JF0-5G0RAal1R5R5agVjcIs0ohUFlzAQ2-nxg4/edit

        gform_json_fn = op.join(self.tmp_dir, 'gform.json')
        with open(gform_json_fn, 'w') as fout:
            fout.write('{"metadata":{"title":"Form title","id":"1MNlo_JF0-5G0RAal1R5R5agVjcIs0ohUFlzAQ2-nxg4","description":"Form description","publishedUrl":"https://docs.google.com/forms/d/e/1FAIpQLSd1sV5MVw4jLE0G2suZuiaT03-uJD0Nsz3vWPQCuslKHuB_lQ/viewform","editorEmails":["covepic.research@gmail.com"],"count":8,"confirmationMessage":"","customClosedFormMessage":""},"items":[{"type":"TEXT","title":"required short answer","description":"description of short answer","required":true},{"type":"PARAGRAPH_TEXT","title":"paragraph","description":"description of paragraph","required":false},{"type":"MULTIPLE_CHOICE","title":"multiple_choice:: Choix multiple","description":"description of multiple choice","required":false,"allow_other_choice":true,"choices":["choice 1","choice 2"]},{"type":"CHECKBOX","title":"à cocher","description":"description of checkboxes","required":false,"choices":["c1:: check 1","check 2"]},{"type":"LIST","title":"dropdown:: Une liste déroulante","description":"description of dropdown","required":false,"choices":["déroulant 1","déroulant 2"]},{"type":"DATE","title":"interview_date:: Date convenue pour l\'interview","description":"description of date","required":false},{"type":"DATETIME","title":"date and time","description":"description of date and time","required":false},{"type":"SECTION_HEADER","title":"A title item","description":"description of title item"}],"count":8}')
        form = Form.from_gform_json_file(gform_json_fn, 'French',
                                         use_item_title_as_key=True,
                                         paragraph_nb_lines=PARAGRAPH_NB_LINES)
        mc_item = form['__section_0__']['multiple_choice']
        self.assertTrue(mc_item.allow_other_choice)
        dd_item = form['__section_0__']['dropdown']
        self.assertFalse(dd_item.allow_other_choice)

        if form != expected_form:
            self.show_form_diff(form, expected_form)
        self.assertEqual(form, expected_form)


    def test_from_gform_language_merge(self):
        raise NotImplementedError()

    def show_form_diff(self, form, expected_form):
        form_fns = []
        for f, bfn in [(form, 'computed_form.json'),
                       (expected_form, 'expected_form.json')]:
            form_fn = op.join(self.tmp_dir, bfn)
            form_fns.append(form_fn)
            with open(form_fn, 'w') as fout:
                fout.write(pformat(f.to_dict()))
        import subprocess
        subprocess.run(['meld'] + form_fns)

class TestFormSection(unittest.TestCase):

    def setUp(self):
        self.label = 'TestFormSection'
        self.df = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0005', 'CE0006']),
            ('Age', [22, 50, None]),
        ]))
        logger.setLevel(logging.DEBUG)

    def test_get_item(self):
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        allow_empty=False),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              default_language='French',
                              supported_languages={'French'})
        self.assertEqual(section['Age'].get_value(), None)
        self.assertRaises(InvalidValue, section['Participant_ID'].get_value)
        self.assertRaises(KeyError, section.__getitem__, 'Other')

    def test_default_title(self):
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              default_language='French',
                              supported_languages={'French'})
        self.assertEqual(section.tr['title'], '')

    def test_title_translation(self):
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant',
                                          'English' : 'Participant code'}},
                                        title = {'French' : 'Identifiant',
                                                 'English' : 'Identifier'},
                                        default_language='French',
                                        supported_languages={'French', 'English'}),
                               FormItem({'Age' :
                                         {'French':'Age en année',
                                          'English' : 'Age in years'}},
                                        default_language='French',
                                        supported_languages={'French', 'English'},
                                        vtype='int')],
                              title={'French' : 'Le titre',
                                     'English' : 'The title'},
                              default_language='French',
                              supported_languages={'French', 'English'})
        self.assertEqual(section.tr['title'], 'Le titre')
        section.set_language('English')
        self.assertEqual(section.tr['title'], 'The title')
        self.assertEqual(section['Participant_ID'].tr['title'], 'Identifier')

    def test_default_next_None(self):
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              default_language='French',
                              supported_languages={'French'})
        self.assertIsNone(section.next())

    def test_next_section_with_transition(self):
        next_section_def = [
            ('Age is not None and Age > 60', 'section_elder'),
            ('Age is not None and Age < 50', 'section_younger')
        ]
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              next_section_definition=next_section_def,
                              default_language='French',
                              supported_languages={'French'})
        self.assertIsNone(section.next())
        section['Age'].set_input_str('19')
        self.assertEqual(section.next(), 'section_younger')
        section['Age'].set_input_str('99')
        self.assertEqual(section.next(), 'section_elder')
        section['Age'].set_input_str('55')
        self.assertIsNone(section.next(), None)

    def test_no_transition_when_invalid(self):
        next_section_def = [
            ('Age is not None and Age > 60', 'section_elder'),
            ('Age is not None and Age <= 60', 'section_younger')
        ]
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int', allow_empty=False)],
                              next_section_definition=next_section_def,
                              default_language='French',
                              supported_languages={'French'})
        self.assertFalse(section.is_valid())
        self.assertIsNone(section.next())

    def test_no_transition_when_no_matching_criterion(self):
        next_section_def = [
            ('Age is not None and Age > 60', 'section_elder'),
            ('Age is not None and Age <= 60', 'section_younger')
        ]
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              next_section_definition=next_section_def,
                              default_language='French',
                              supported_languages={'French'})
        self.assertTrue(section.is_valid())
        self.assertIsNone(section.next())

    def test_submit(self):
        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'}),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int')],
                              next_section_definition='__submit__',
                              default_language='French',
                              supported_languages={'French'})
        section['Participant_ID'].set_input_str('CE0000')
        section['Age'].set_input_str('99')
        entry = section.submit()
        self.assertEqual(entry['Participant_ID'], 'CE0000')
        self.assertEqual(entry['Age'], 99)

    def test_notification(self):
        received_signals = []
        def record_signal(signal):
            received_signals.append(signal)
        watchers = {s: [LazyFunc(record_signal,s)] \
                    for s in ['section_invalid', 'section_valid']}

        section = FormSection([FormItem({'Participant_ID' :
                                         {'French':'Code Participant'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        regexp='^CE[0-9]{4}$',
                                        allow_empty=False),
                               FormItem({'Age' :
                                         {'French':'Age en année'}},
                                        default_language='French',
                                        supported_languages={'French'},
                                        vtype='int',
                                        allow_empty=False)],
                              default_language='French',
                              supported_languages={'French'},
                              watchers=watchers)
        self.assertEqual(received_signals, ['section_invalid'])
        received_signals.clear()
        section['Age'].set_input_str('99')
        self.assertEqual(received_signals, ['section_invalid'])
        received_signals.clear()
        logger.debug('utest: set Participant_ID to CE0000')
        section['Participant_ID'].set_input_str('CE0000')
        self.assertEqual(received_signals, ['section_valid'])
        received_signals.clear()
        section['Participant_ID'].set_input_str('CE0000')
        self.assertEqual(received_signals, ['section_valid'])
        received_signals.clear()
        section['Age'].set_input_str('')
        self.assertEqual(received_signals, ['section_invalid'])
        received_signals.clear()
        section['Participant_ID'].set_input_str('??')
        self.assertEqual(received_signals, ['section_invalid'])

class TestFormItem(unittest.TestCase):

    def setUp(self):
        self.label = 'TestFromItem'
        self.df = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0005', 'CE0006']),
            ('Referencing', ['epic_member', 'epic_member', 'epic_member']),
            ('First_Name', ['John', 'Ella', '']),
            ('Last_Name', ['McLain', 'Pissai', 'Vance']),
            ('Email_Address', ['20100thomas@gmail.com',
                               '20100thomas@gmail.com',
                               '20100thomas@gmail.com']),
            ('Phone_Number', ['000-000-0000', '514-000-0000',
                              '456-123-4565#1']),
            ('Age', [44, 34, 21]),
            ('Weight_kg', [44.7, 50.2, 70]),
            ('Entry_ts', [datetime(2013,4,5,10,10),
                          datetime(2017,11,25,15,10),
                          datetime(2014,9,5,14,16)]),
            ('Comment', ['something', 'fishy', 'around here']),
            ('exclude', [False, False, False]),
            ('Secure_ID', ['aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
                           '22222222222222222222222222222222',
                           '11111111111111111111111111111111']),
            ('Agree_contact', [False, True, False]),
            ('Agree_participation', [False, True, False])
        ]))

        logger.setLevel(logging.DEBUG)

    def test_no_key(self):
        item = FormItem(None, supported_languages={'English'},
                        default_language='English')
        self.assertIsNone(item.get_value())
        self.assertEqual(item.submit(), {})

    def test_default_title_from_key(self):
        item_key = 'Participant_ID'
        item = FormItem({item_key : None}, supported_languages={'English'},
                        default_language='English')
        self.assertEqual(item.tr['title'], item_key)

    def test_default_title_from_key_translated(self):
        item_key = {'Participant_ID' : {'French' : 'Code Participant',
                                        'English' : 'Participant code'}}
        item = FormItem(item_key, supported_languages={'English', 'French'},
                        default_language='English')
        self.assertEqual(item.tr['title'], item_key['Participant_ID']['English'])
        item.set_language('French')
        self.assertEqual(item.tr['title'], item_key['Participant_ID']['French'])

    def test_empty_title(self):
        item_key = 'Participant_ID'
        item = FormItem({item_key:None}, title='',
                        supported_languages={'English'},
                        default_language='English')
        self.assertEqual(item.tr['title'], '')

    def test_title_translation(self):
        item_key = 'Participant_ID'
        item = FormItem({item_key:None},
                        title={'English' : 'Participant code',
                               'French' : 'Code participant'},
                        supported_languages={'English', 'French'},
                        default_language='English')

        self.assertEqual(item.tr['title'], 'Participant code')
        item.set_language('French')
        self.assertEqual(item.tr['title'], 'Code participant')

    def test_form_item_badtype(self):
        self.assertRaises(TypeError, FormItem, {'Participant_ID':None},
                          vtype='bad_type', supported_languages={'English'},
                          default_language='English')

    def test_constraint_not_empty(self):
        item = FormItem({'Participant_ID':None}, allow_empty=False,
                        supported_languages={'English'},
                        default_language='English')
        self.assertFalse(item.is_valid())
        item.set_input_str('CE9999')
        self.assertTrue(item.is_valid())
        item.set_input_str('')
        self.assertFalse(item.is_valid())

    def test_unique(self):
        item = FormItem({'Participant_ID':None}, unique=True,
                        supported_languages={'English'},
                        default_language='English')
        def check_uniqueness(key, value):
            return value not in {'CE0005', 'CE0004'}
        item.set_unique_validator(check_uniqueness)
        self.assertTrue(item.is_valid())
        item.set_input_str('CE9999')
        self.assertTrue(item.is_valid())
        item.set_input_str('CE0005')
        self.assertFalse(item.is_valid())

    def test_constraint_regexp(self):
        item = FormItem({'Participant_ID':None},
                        regexp='^CE[0-9]{4}$', supported_languages={'English'},
                        default_language='English')
        self.assertTrue(item.is_valid()) # empty allowed
        item.set_input_str('CE9999')
        self.assertTrue(item.is_valid())
        item.set_input_str('CE005')
        self.assertFalse(item.is_valid())


    def test_init_default_value(self):
        item = FormItem({'exclude':None},
                        vtype='boolean',
                        choices={'False':{'English':'Nope'},
                                 'True':{'English':'Yep'}},
                        supported_languages={'English'},
                        default_language='English',
                        init_values={'exclude' : False})
        self.assertEqual(item.get_value(), False)
        item = FormItem(**item.to_dict())
        self.assertEqual(item.get_value(), False)

        item = FormItem({'Status':None},
                        supported_languages={'English'},
                        default_language='English',
                        init_values={'Status' : 'ongoing'})
        self.assertEqual(item.get_value(), 'ongoing')
        item = FormItem(**item.to_dict())
        self.assertEqual(item.get_value(), 'ongoing')

        item = FormItem({'a_choice':None},
                        supported_languages={'English'},
                        default_language='English',
                        choices={'c1':{'English':'Choice 1'},
                                 'c2':{'English':'Choice 2'}},
                        init_values={'a_choice' : 'c2'})
        self.assertEqual(item.get_value(), 'c2')
        item = FormItem(**item.to_dict())
        self.assertEqual(item.get_value(), 'c2')

    def test_get_value_error_when_invalid(self):
        item = FormItem({'Participant_ID':None},
                        regexp='^CE[0-9]{4}$', supported_languages={'English'},
                        default_language='English')
        item.get_value() # no error, because can be empty
        item.set_input_str('CE005')
        self.assertRaises(InvalidValue, item.get_value)

    def test_integer_unformat(self):
        item = FormItem({'Age':None}, vtype='int',
                        supported_languages={'English'},
                        default_language='English')
        int_str = '-43'
        item.set_input_str(int_str)
        self.assertEqual(item.get_value(), int(int_str))

    def test_invalid_integer(self):
        item = FormItem({'Age':None}, vtype='int',
                        supported_languages={'English'},
                        default_language='English')
        int_str = '-43.3'
        item.set_input_str(int_str)
        self.assertFalse(item.is_valid())

    def test_number_unformat(self):
        item = FormItem({'Weight_kg':None},
                        vtype='number', supported_languages={'English'},
                        default_language='English')
        number_str = '77.5'
        item.set_input_str(number_str)
        self.assertEqual(item.get_value(), float(number_str))

    def test_number_greater(self):
        item = FormItem({'Weight_kg':None},
                        vtype='number',
                        number_interval={'left':0, 'closed':'neither'},
                        supported_languages={'English'},
                        default_language='English')
        number_str = '0'
        item.set_input_str(number_str)
        self.assertFalse(item.is_valid())
        number_str = '0.1'
        item.set_input_str(number_str)
        self.assertEqual(item.get_value(), float(number_str))

    def test_number_greater_or_equal(self):
        item = FormItem({'Weight_kg':None},
                        vtype='number',
                        number_interval={'left':0, 'closed':'left'},
                        supported_languages={'English'},
                        default_language='English')
        number_str = '0'
        item.set_input_str(number_str)
        self.assertEqual(item.get_value(), float(number_str))
        item.set_input_str('-1.1')
        self.assertFalse(item.is_valid())

    def test_number_less(self):
        item = FormItem({'Weight_kg':None},
                        vtype='number',
                        number_interval={'right':0, 'closed':'neither'},
                        supported_languages={'English'},
                        default_language='English')
        number_str = '0'
        item.set_input_str(number_str)
        self.assertFalse(item.is_valid())
        number_str = '-0.1'
        item.set_input_str(number_str)
        self.assertEqual(item.get_value(), float(number_str))

    def test_number_less_or_equal(self):
        item = FormItem({'Weight_kg':None},
                        vtype='number',
                        number_interval={'right':0, 'closed':'right'},
                        supported_languages={'English'},
                        default_language='English')
        number_str = '0'
        item.set_input_str(number_str)
        self.assertEqual(item.get_value(), float(number_str))
        item.set_input_str('1.1')
        self.assertFalse(item.is_valid())

    def test_date(self):
        item = FormItem({'Inclusion_date':None},
                        vtype='date', supported_languages={'English'},
                        default_language='English')

        vdate = date(2020, 4, 24)
        DATE_FORMAT = '%Y-%m-%d'
        date_str = vdate.strftime(DATE_FORMAT)
        item.set_input_str(date_str)
        self.assertEqual(item.get_value(), vdate)
        item.set_input_str('2020--9/1')
        self.assertFalse(item.is_valid())

    def test_datetime(self):
        item = FormItem({'Entry_ts':None},
                        vtype='datetime', supported_languages={'English'},
                        default_language='English')
        date = datetime(2020, 4, 24, 13, 37)
        DATETIME_FORMAT = '%Y-%m-%d %H:%M:%S.%f'
        date_str = date.strftime(DATETIME_FORMAT)
        item.set_input_str(date_str)
        self.assertEqual(item.get_value(), date)
        item.set_input_str('2020--9/1 13:50')
        self.assertFalse(item.is_valid())

    def test_boolean_2_choices(self):
        item = FormItem({'exclude':None},
                        vtype='boolean',
                        choices={'False':{'English':'Nope'},
                                 'True':{'English':'Yep'}},
                        supported_languages={'English'},
                        default_language='English')
        item.set_input_str('Falsed')
        self.assertFalse(item.is_valid())
        item.set_input_str('Yep')
        self.assertTrue(item.is_valid())
        self.assertEqual(item.get_value(), True)
        item.set_input_str('Nope')
        self.assertEqual(item.get_value(), False)

    def test_boolean(self):
        item = FormItem({'exclude':None},
                        vtype='boolean', supported_languages={'English'},
                        default_language='English')
        item.set_input_str('True')
        self.assertEqual(item.get_value(), True)
        item.set_input_str('False')
        self.assertEqual(item.get_value(), False)
        item.set_input_str('Da')
        self.assertFalse(item.is_valid())

    def test_boolean_group(self):
        item = FormItem(keys={'Agree_contact':
                              {'French' :'Accepte contact'},
                              'Agree_participation':
                              {'French' :'Accepte de participer'}},
                        vtype='boolean', supported_languages={'French'},
                        default_language='French')
        item.set_input_str('True', key='Agree_participation')
        self.assertTrue(item.is_valid())
        self.assertEqual(item.get_items(), {'Agree_contact' : None,
                                            'Agree_participation' : True})
        item.set_input_str('Dummy', key='Agree_participation')
        self.assertFalse(item.is_valid())

    def test_text_with_choices(self):
        choices = {'epic_member' : {'French' : 'Membre EPIC'},
                   'cardiac_rehab' : {'French' : 'Clinique de réhabilitation'},
                   'community' : {'French' : 'Communauté'}}
        item = FormItem(keys={'Referencing':None},
                        vtype='text', choices=choices,
                        supported_languages={'French'},
                        default_language='French')
        item.set_input_str('Membre EPIC')
        self.assertTrue(item.is_valid())
        self.assertEqual(item.get_value(), 'epic_member')
        item.set_input_str('Dummy')
        self.assertFalse(item.is_valid())


    def test_text_with_choices_and_other(self):
        choices = {'epic_member' : {'French' : 'Membre EPIC'},
                   'cardiac_rehab' : {'French' : 'Clinique de réhabilitation'},
                   'community' : {'French' : 'Communauté'}}
        item = FormItem(keys={'Referencing':None},
                        vtype='text', choices=choices,
                        other_choice_label={'French' : 'Autre'},
                        supported_languages={'French'},
                        default_language='French')
        item.set_input_str('Membre EPIC')
        self.assertTrue(item.is_valid())
        self.assertEqual(item.get_value(), 'epic_member')
        item.set_input_str('Dummy')
        self.assertEqual(item.get_value(), 'Dummy')
        self.assertTrue(item.is_valid())

    def test_uuid_generation(self):
        item = FormItem(keys={'Referencing':None},
                        vtype='text', generator='uuid4',
                        supported_languages={'English'},
                        default_language='English')
        uuid4hex = re.compile('[0-9a-f]{32}\Z', re.I)
        self.assertTrue(uuid4hex.match(item.get_value()) is not None)

    def test_form_item_ts_creation(self):
        start = datetime.now()
        item = FormItem(keys={'Entry_ts':None},
                        vtype='datetime', generator='timestamp_creation',
                        supported_languages={'English'},
                        default_language='English')
        ts_after_init = datetime.now()
        sleep_time_sec = 0.1
        sleep(sleep_time_sec)
        result = next(iter(item.submit().values()))
        self.assertGreaterEqual(result, start)
        self.assertLess(result, ts_after_init+timedelta(seconds=sleep_time_sec/2))

    def test_form_item_ts_submission(self):
        item = FormItem(keys={'Entry_ts':None},
                        vtype='datetime', generator='timestamp_submission',
                        supported_languages={'English'},
                        default_language='English')
        ts_after_init = datetime.now()
        sleep_time_sec = 0.1
        sleep(sleep_time_sec)
        result = next(iter(item.submit().values()))
        end_submit = datetime.now()
        self.assertGreater(result, ts_after_init+timedelta(seconds=sleep_time_sec/2))
        self.assertGreater(end_submit, result-timedelta(milliseconds=0.1))

    def test_notifications(self):

        received_signals = []
        def record_signal(signal):
            received_signals.append(signal)
        watchers = {s: [LazyFunc(record_signal,s)] \
                    for s in ['item_invalid', 'item_valid']}

        item = FormItem({'Participant_ID' :
                         {'French':'Code Participant'}},
                        default_language='French',
                        supported_languages={'French'},
                        regexp='^CE[0-9]{4}$',
                        allow_empty=False,
                        watchers=watchers)
        self.assertEqual(received_signals, ['item_invalid'])
        logger.debug('utest: set Participant_ID=""')
        received_signals.clear()
        item.set_input_str('', 'Participant_ID')
        self.assertEqual(received_signals, ['item_invalid'])
        logger.debug('utest: set Participant_ID=CE0000')
        received_signals.clear()
        item.set_input_str('CE0000', 'Participant_ID')
        self.assertEqual(received_signals, ['item_valid'])
        received_signals.clear()
        logger.debug('utest: set Participant_ID=CE0001')
        item.set_input_str('CE0001', 'Participant_ID')
        self.assertEqual(received_signals, ['item_valid'])
        logger.debug('utest: set Participant_ID=!!')
        received_signals.clear()
        item.set_input_str('!!', 'Participant_ID')
        self.assertEqual(received_signals, ['item_invalid'])
        received_signals.clear()
        logger.debug('utest: set Participant_ID=??')
        item.set_input_str('??', 'Participant_ID')
        self.assertEqual(received_signals, ['item_invalid'])

    #TODO: entry highlight color as catching regexp
    #TODO: cell highlight color as catching regexp
    #TODO: table rendering: use color darkening for one-over-two row coloring
    #TODO: cannot use from_existing_entry and index with timestamp types
    #TODO: default value from cfg_dict + check invalid default value

class TestTranslator(unittest.TestCase):

    def test_translation(self):
        tr = Translator(default_language='English',
                        supported_languages={'French','English'})
        trad = {'French' : 'un mot',
                'English' : 'a word'}
        tr.register('keyword1', trad)
        self.assertEqual(tr['keyword1'], trad['English'])
        tr.set_language('French')
        self.assertEqual(tr['keyword1'], trad['French'])

    def test_key_not_found(self):
        tr = Translator(default_language='English',
                        supported_languages={'French','English'})
        tr.register('keyword1', None)
        self.assertRaises(UnknownTrKey, tr.__getitem__, 'keyword2')

    def test_None(self):
        tr = Translator(default_language='English',
                        supported_languages={'French','English'})
        tr.register('keyword1', None)
        self.assertEqual(tr['keyword1'], 'keyword1')
        tr.set_language('French')
        self.assertEqual(tr['keyword1'], 'keyword1')

    def test_empty(self):
        tr = Translator(default_language='English',
                        supported_languages={'French','English'})
        tr.register('keyword1', '')
        self.assertEqual(tr['keyword1'], '')

    def test_already_registered(self):
        tr = Translator(default_language='English',
                        supported_languages={'French','English'})
        tr.register('keyword1', '')
        self.assertRaises(TrKeyAlreadyRegistered,
                          tr.register, 'keyword1', '')

    def test_unsupported_language_register(self):
        tr = Translator(default_language='English',
                        supported_languages={'English'})
        tr.register('keyword1', '')
        self.assertRaises(LanguageError, tr.register, 'keyword2',
                          {'French' : 'un mot'})

    def test_extra_translation(self):
        tr = Translator(default_language='English',
                        supported_languages={'English'})
        self.assertRaises(LanguageError, tr.register, 'keyword1',
                          {'English': 'a word', 'French' : 'un mot'})

    def test_unsupported_language(self):
        tr = Translator(default_language='English',
                        supported_languages={'English'})
        tr.register('keyword1', '')
        self.assertRaises(UnsupportedLanguage, tr.set_language, 'French')


def compose(*funcs):
    def _call():
        r = funcs[0]()
        for f in funcs[1:]:
            r = f(r)
        return r
    return _call

def set_dval(d, k, v):
    d[k] = v

class TestCompose(unittest.TestCase):
    def test_compose(self):
        d = {}
        def get_txt_val():
            return '4'
        compose(get_txt_val, int, partial(d.__setitem__, 'res'))()
        self.assertEqual(d, {'res' : 4})

def link_line_edit(line_edit, dest_dict, dest_key, empty_str_is_None=False,
                   read_only=False):
    try:
        line_edit.editingFinished.disconnect()
    except TypeError:
        pass

    text = dest_dict[dest_key]
    line_edit.setText(if_none(text, ''))

    if not read_only:
        line_edit.setReadOnly(False)
        if empty_str_is_None:
            f_store_in_dict = partial(dict_set_none_if_empty, dest_dict, dest_key)
        else:
            f_store_in_dict = partial(dest_dict.__setitem__, dest_key)

        line_edit.editingFinished.connect(compose(line_edit.text, f_store_in_dict))
    else:
        line_edit.setReadOnly(True)

def link_text_edit(text_edit, dest_dict, dest_key, empty_str_is_None=False,
                   read_only=False):
    try:
        text_edit.editingFinished.disconnect()
    except TypeError:
        pass

    text = dest_dict[dest_key]
    text_edit.setPlainText(if_none(text, ''))

    if not read_only:
        text_edit.setReadOnly(False)
        if empty_str_is_None:
            f_store_in_dict = partial(dict_set_none_if_empty, dest_dict, dest_key)
        else:
            f_store_in_dict = partial(dest_dict.__setitem__, dest_key)
        callback = compose(text_edit.toPlainText, f_store_in_dict)
        text_edit.editingFinished.connect(callback)
    else:
        text_edit.setReadOnly(True)

def dict_set_none_if_empty(d, k, s):
    if v == '':
        v = None
    d[k] = v

def link_combo_box(combox_box, dest_dict, dest_key, choices=None, editable=True,
                   empty_str_is_None=False):
    try:
        combox_box.currentTextChanged.disconnect()
    except TypeError:
        pass
    if choices is not None:
        combox_box.clear()
        combox_box.addItems(choices)

    text = dest_dict[dest_key]
    combox_box.setCurrentText(if_none(text, ''))

    if editable:
        combox_box.setEnabled(True)
        if empty_str_is_None:
            f_store_in_dict = partial(dict_set_none_if_empty, dest_dict, dest_key)
        else:
            f_store_in_dict = partial(dest_dict.__setitem__, dest_key)
        combox_box.currentTextChanged.connect(f_store_in_dict)
    else:
        combox_box.setEnabled(False)

def link_check_box(check_box, dest_dict, dest_key, read_only=False):
    try:
        check_box.stateChanged.disconnect()
    except TypeError:
        pass
    check_box.setChecked(dest_dict[dest_key])
    if not read_only:
        check_box.setEnabled(True)
        def store_state_to_dict(qstate):
            dest_dict[dest_key] = (qstate == Qt.Checked)
        check_box.stateChanged.connect(store_state_to_dict)
    else:
        check_box.setEnabled(False)

def link_spin_box(spin_box, dest_dict, dest_key, read_only=False):
    try:
        spin_box.valueChanged.disconnect()
    except TypeError:
        pass
    spin_box.setValue(dest_dict[dest_key])
    if read_only:
        spin_box.setEnabled(True)
        spin_box.valueChanged.connect(partial(dest_dict.__setitem__, dest_key))
    else:
        spin_box.setEnabled(False)

class FormPropertyEditor(QtWidgets.QWidget,
                         ui.form_edit_ui.Ui_FormPropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.read_only = read_only

    def attach(self, form_node):
        for field, language in [(self.title_field_french, 'French'),
                                (self.title_field_english, 'English')]:
            link_line_edit(field, form_node.pdict['title'], language,
                           read_only=self.read_only)

class SectionPropertyEditor(QtWidgets.QWidget,
                            ui.section_edit_ui.Ui_SectionPropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.read_only = read_only

    def attach(self, section_node):
        for field, language in [(self.title_field_french, 'French'),
                                (self.title_field_english, 'English')]:
            link_line_edit(field, section_node.pdict['title'], language,
                           read_only=self.read_only)

class ItemPropertyEditor(QtWidgets.QWidget,
                         ui.item_edit_ui.Ui_ItemPropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.typeComboBox.addItems(list(sorted(FormItem.VTYPES.keys())))
        generators = [''] + sorted([g for g in FormItem.GENERATORS
                                    if g is not None])
        self.generatorComboBox.addItems(generators)
        self.read_only = read_only

    def attach(self, item_node):
        for field, dest_dict, key in [(self.title_field_french,
                                       item_node.pdict['title'], 'French'),
                                      (self.title_field_english,
                                       item_node.pdict['title'], 'English'),
                                      (self.regExprLineEdit, item_node.pdict,
                                       'regexp'),
                                      (self.regExprInvalidHintLineEdit,
                                       item_node.pdict,
                                       'regexp_invalid_message')]:
            link_line_edit(field, dest_dict, key, read_only=self.read_only)

        for field, dest_dict, key in [(self.description_field_french,
                                       item_node.pdict['description'],
                                       'French'),
                                      (self.description_field_english,
                                       item_node.pdict['description'],
                                       'English')]:
            link_text_edit(field, dest_dict, key, read_only=self.read_only)

        link_combo_box(self.typeComboBox, item_node.pdict, 'vtype',
                       editable=(not item_node.pdict['type_locked'] and
                                 not self.read_only))
        link_check_box(self.uniqueCheckBox, item_node.pdict, 'unique',
                       read_only=self.read_only)
        link_check_box(self.allowEmptyCheckBox, item_node.pdict, 'allow_empty',
                       read_only=self.read_only)
        link_combo_box(self.accessLevelComboBox, item_node.pdict, 'access_level',
                       editable=not self.read_only)
        link_spin_box(self.textNbLinesSpinBox, item_node.pdict, 'nb_lines',
                      read_only=self.read_only)
        link_combo_box(self.generatorComboBox, item_node.pdict, 'generator',
                       editable=not self.read_only)

        if item_node.node_type == 'item_single_var':
            self.initialValueLineEdit.show()
            self.initialValueLabel.show()
            try:
                self.initialValueLineEdit.editingFinished.disconnect()
            except TypeError:
                pass
            #TODO: handle format/unformat
            if item_node.pdict['init_value'] is None:
                text = ''
            else:
                text = str(item_node.pdict['init_value'])
            self.initialValueLineEdit.setText(text)

            if not self.read_only:
                self.initialValueLineEdit.setReadOnly(False)
                def store_init_value():
                    # TODO: handle format/unformat
                    item_node.pdict['init_value'] = \
                        if_none_or_empty(self.initialValueLineEdit.text(), None)
                self.initialValueLineEdit.editingFinished.connect(store_init_value)
            else:
                self.initialValueLineEdit.setReadOnly(True)
        else:
            self.initialValueLineEdit.hide()
            self.initialValueLabel.hide()

class ChoicePropertyEditor(QtWidgets.QWidget,
                           ui.choice_edit_ui.Ui_ChoicePropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.read_only = read_only

    def attach(self, choice_node):
        for field, language in [(self.choice_field_french, 'French'),
                                (self.choice_field_english, 'English')]:
            link_line_edit(field, choice_node.pdict, language,
                           read_only=self.read_only)

class VariablePropertyEditor(QtWidgets.QWidget,
                             ui.variable_edit_ui.Ui_VariablePropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.read_only = read_only

    def attach(self, var_node):
        for field, dest_dict, key in [(self.variable_field_french,
                                       var_node.pdict['key_tr'], 'French'),
                                      (self.variable_field_english,
                                       var_node.pdict['key_tr'], 'English'),
                                      (self.initValueLineEdit,
                                       var_node.pdict, 'init_value')]:
            logger.debug('link line edit for %s', key)
            link_line_edit(field, dest_dict, key, read_only=self.read_only)

class SectionTransitionPropertyEditor(QtWidgets.QWidget,
                                      ui.section_transition_edit_ui.Ui_SectionTransitionPropertyEditor):
    def __init__(self, read_only=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.read_only = read_only

    def attach(self, transition_node):
        link_line_edit(self.criterionLineEdit, transition_node.pdict, 'predicate',
                       read_only=self.read_only)
        next_section_choices = ['__submit__'] + \
                                [s for s in (transition_node.parent().parent()
                                             .parent().child_labels())
                                 if s != transition_node.parent().parent().label]
        link_combo_box(self.nextSectionComboBox, transition_node.pdict,
                       'next_section', choices=next_section_choices,
                       editable=not self.read_only)

import traceback, sys

class PendingChangesTracker:
    def __init__(self, process_pending_changes, callback_pending,
                 callback_not_pending):
        self.process_pending_changes = process_pending_changes
        self.callback_pending = callback_pending
        self.callback_not_pending = callback_not_pending
        self.pending_changes = False

        self.set_pending_change_state(False)

    def on_change(self):
        self.set_pending_change_state(True)

    def set_pending_change_state(self, state):
        if state:
            self.callback_pending()
            self.pending_changes = True
        else:
            self.callback_not_pending()
            self.pending_changes = False

    def process_pending(self):
        if self.pending_changes:
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Question)
            message_box.setText('There are unsaved modification. Save them?')
            message_box.addButton(QtWidgets.QMessageBox.Discard)
            message_box.addButton(QtWidgets.QMessageBox.Cancel)
            message_box.addButton(QtWidgets.QMessageBox.Save)
            result = message_box.exec_()
            if result == QtWidgets.QMessageBox.Discard:
                self.set_pending_change_state(False)
                return True
            elif result == QtWidgets.QMessageBox.Cancel:
                return False
            elif result == QtWidgets.QMessageBox.Save:
                if self.process_pending_changes():
                    self.set_pending_change_state(False)
                return True
            else:
                return False
        return True

class FormSheetEditor(QtWidgets.QWidget, ui.form_editor_sheet_ui.Ui_Form):
    def __init__(self, sheet, close_callback=None, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.button_load.clicked.connect(self.on_load)
        self.button_save.clicked.connect(self.on_save)
        self.button_export.clicked.connect(self.on_export)
        self.button_close.clicked.connect(self.on_close)
        self.button_close.setIcon(QtGui.QIcon(':/icons/close_icon'))

        self.unsaved_icon = QtGui.QIcon(':/icons/alert_icon')

        self.sheet = sheet
        self.current_tmp_form_fn = None
        self.close_callback = (close_callback if close_callback is not None
                               else lambda: None)

        error_message = None
        try:
            self.current_tmp_form_fn = self.sheet.get_alternate_form_fn()
            form = self.sheet.get_form_for_edition()
        except FormEditionBlockedByPendingLiveForm as e:
            error_message = ('Cannot modify form because of unsubmitted live '\
                             'forms of user(s): %s' % e)
            self.sheet.close_form_edition()
        except FormEditionLocked as e:
            error_message = 'Form is being edited by %s' % e
            if self.sheet.user_role >= UserRole.ADMIN:
                message_box = QtWidgets.QMessageBox()
                message_box.setIcon(QtWidgets.QMessageBox.Question)
                message_box.setText('%s. Click discard to force unlock. ' \
                                    'OK to keep lock and open in ' \
                                    'read-only mode' % error_message)
                message_box.addButton(QtWidgets.QMessageBox.Discard)
                message_box.addButton(QtWidgets.QMessageBox.Cancel)
                message_box.addButton(QtWidgets.QMessageBox.Ok)
                result = message_box.exec_()
                if result == QtWidgets.QMessageBox.Discard:
                    self.sheet.close_form_edition()
                    form = self.sheet.get_form_for_edition()
                    error_message = None
                elif result == QtWidgets.QMessageBox.Cancel:
                    raise FormEditionCancelled()
                # else Ok -> keep error and form will be open read-only
        except Exception as e:
            error_message = 'Error while requesting form edition: %s' % e
            logger.error(traceback.format_exception(*sys.exc_info()))
            self.sheet.close_form_edition()

        self.read_only = False
        if error_message is not None:
            show_critical_message_box('The form is read-only. Reason:\n%s' %\
                                      error_message)
            self.button_save.setEnabled(False)
            form = self.sheet.form_master.new()
            self.read_only = True

        on_pending = partial(self.button_save.setIcon, self.unsaved_icon)
        on_not_pending = partial(self.button_save.setIcon, QtGui.QIcon())
        if not self.read_only:
            on_save = self.save_current
        else:
            on_save = self.on_export

        self.pending_changes_tracker = \
            PendingChangesTracker(on_save, callback_pending=on_pending,
                                  callback_not_pending=on_not_pending)

        # Form widget
        self.form_editor = FormEditor(form, self._locked_variable_types(),
                                      parent=self)
        self.form_editor.formChanged.connect(self.pending_changes_tracker
                                             .on_change)

        self.verticalLayout_2.addWidget(self.form_editor)

    def _locked_variable_types(self):
        if self.sheet.form_master is not None and \
           self.sheet.df is not None and self.sheet.df.shape[0] > 0:
            locked_vars = self.sheet.form_master.get_vtypes().copy()
        else:
            locked_vars = {}
        return locked_vars

    def on_load(self):
        if self.pending_changes_tracker.process_pending():
            form_to_load = self.ask_open_alternate_form()
            if form_to_load is not None:
                self.form_editor.set_form(form_to_load,
                                          self._locked_variable_types())
                self.pending_changes_tracker.set_pending_change_state(False)

    def on_save(self):
        if self.save_current():
            self.pending_changes_tracker.set_pending_change_state(False)

    def save_current(self):
        try:
            self.sheet.set_form_master(self.form_editor.get_form(),
                                       save=True, overwrite=True)
        except Exception as e:
            show_critical_message_box('Error while saving form of sheet '\
                                      '%s:\n%s' % (self.sheet.label, repr(e)))
            logger.error(format_exc())
            return False
        return True

    def on_export(self):
        proposed_fn = '%s.form' % self.sheet.label
        form_fn, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Save Form",
                                                           proposed_fn,
                                                           "Piccel Form Files "\
                                                           "(*.form)")
        if form_fn is not None and form_fn != '':
            self.form_editor.get_form().save_to_json_file(form_fn)

    def ask_open_alternate_form(self):
        form_master_alternates = self.sheet.get_alternate_master_forms()
        if len(form_master_alternates) > 0:
            selector = ListSelectDialog(reversed(sorted(form_master_alternates)),
                                        'Select form')
            if selector.exec_():
                selected_form_fn = selector.get_choice()
                if selected_form_fn is not None:
                    full_fn = op.join('master_form_alternates', selected_form_fn)
                    self.current_tmp_form = self.sheet.get_alternate_form_fn()
                    content = self.sheet.filesystem.load(full_fn)
                    return Form.from_json(content)
        else:
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Information)
            message_box.setText('No alternate form master available')
            message_box.exec_()

        return None

    def save_temporary_form(self, form):
        if not self.read_only and self.current_tmp_form_fn is not None:
            self.sheet.save_alternate_master_form(self.current_tmp_form_fn, form)

    def on_close(self):
        if self.pending_changes_tracker.process_pending():
            if not self.read_only:
                self.sheet.close_form_edition()
            self.close_callback()

import os

def make_item_input_widget(item_widget, item, key, key_label,
                           item_is_single=False):
    input_widget = QtWidgets.QWidget(item_widget)
    init_value = item.values_str[key]
    _input_ui = None
    if (item.vtype == 'text' and item.choices is None and \
        item.nb_lines<=1) or item.vtype == 'int' or \
        item.vtype == 'number' or item.vtype == 'int64':
        # Single line input field
        _input_ui = ui.item_single_line_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        if not item_is_single:
            item.notifier.add_watcher('language_changed', refresh_label_key)
        #_input_ui.label_key.setText(item.tr[key])
        _input_ui.value_field.setText(init_value)
        callback = text_connect(_input_ui.value_field.text, item.set_input_str)
        _input_ui.value_field.editingFinished.connect(callback)
    elif item.vtype == 'text' and item.choices is None and \
         item.nb_lines>1:
        # Multi line input field
        _input_ui = ui.item_text_multi_line_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        _input_ui.value_field.setPlainText(init_value)
        callback = text_connect(_input_ui.value_field.toPlainText,
                                item.set_input_str)
        _input_ui.value_field.editingFinished.connect(callback)
    elif (item.vtype == 'boolean' and not item_is_single):
        _input_ui = ui.item_boolean_checkboxes_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.check_box)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        _input_ui.check_box.toggled.connect(lambda b: item.set_input_str('%s'%b))
        if init_value != '':
            _input_ui.check_box.setChecked(item.get_value())
    elif (item.vtype == 'text' and item.choices is not None) or\
         (item.vtype == 'boolean' and item_is_single):
        # Radio buttons
        _input_ui = ui.item_choice_radio_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        if not item_is_single:
            item.notifier.add_watcher('language_changed', refresh_label_key)

        radio_group = QtWidgets.QButtonGroup(input_widget)
        for idx, choice in enumerate(item.choices.keys()):
            frame = _input_ui.radio_frame
            radio_button = QtWidgets.QRadioButton(frame)
            refresh_radio_text = refresh_text(item, choice, radio_button)
            refresh_radio_text()
            item.notifier.add_watcher('language_changed', refresh_radio_text)
            radio_button.setObjectName("radio_button_"+choice)
            _input_ui.radio_layout.addWidget(radio_button, idx)
            radio_group.addButton(radio_button, idx)
            class ChoiceProcess:
                def __init__(self, item, choice_button):
                    self.item = item
                    self.choice_button = choice_button
                def __call__(self, state):
                    if state:
                        self.item.set_input_str(self.choice_button.text())
            radio_button.toggled.connect(ChoiceProcess(item, radio_button))
            # if item.vtype == 'boolean':
            #     from IPython import embed; embed()
            if item.is_valid() and item.value_to_str() == choice:
                radio_group.button(idx).setChecked(True)
        if item.allow_other_choice:
            radio_group.addButton(_input_ui.radio_button_other, idx+1)

            def toggle_other_field(flag):
                # flag = _input_ui.radio_button_other.ischecked()
                _input_ui.other_field.setEnabled(flag)
            _input_ui.radio_button_other.toggled.connect(toggle_other_field)

            callback = text_connect(_input_ui.other_field.text, item.set_input_str)
            _input_ui.other_field.editingFinished.connect(callback)
        else:
            _input_ui.radio_button_other_frame.hide()

    elif item.vtype == 'date' or item.vtype == 'datetime':
        # Date/Time input
        _input_ui = ui.item_datetime_ui.Ui_Form()
        _input_ui.setupUi(input_widget)
        refresh_label_key = refresh_text(item, key, _input_ui.label_key)
        refresh_label_key()
        item.notifier.add_watcher('language_changed', refresh_label_key)
        date_str, date_fmt, hour, mins = item.split_qdatetime_str(key)

        if date_str is not None:
            qdate = QtCore.QDate.fromString(date_str, date_fmt)
        else:
            qdate = QtCore.QDate()
        logger.debug2("Init date field with %s -> qdate=%s", date_str, qdate)
        date_collector = DateTimeCollector(item.set_input_str, qdate, hour, mins)

        _input_ui.datetime_field.setDate(qdate)
        _input_ui.datetime_field.dateChanged.connect(date_collector.set_date)
        if hour is not None:
            _input_ui.hour_field.setValue(hour)
        else:
            _input_ui.hour_field.clear()
        callback = get_set_connect(_input_ui.hour_field.value,
                                   date_collector.set_hours)
        _input_ui.hour_field.editingFinished.connect(callback)

        if mins is not None:
            _input_ui.minute_field.setValue(mins)
        else:
            _input_ui.minute_field.clear()
        callback = get_set_connect(_input_ui.minute_field.value,
                                   date_collector.set_minutes)
        _input_ui.minute_field.editingFinished.connect(callback)

        if item.vtype == 'date':
            _input_ui.frame_hour.hide()
    else:
        logger.error('Cannot make UI for item %s (vtype: %s)', item, item.vtype)

    if _input_ui is not None and item_is_single:
        _input_ui.label_key.hide()

    return input_widget

def make_item_widget(section_widget, item):
    item_widget = QtWidgets.QWidget(section_widget)
    _item_ui = ui.form_item_ui.Ui_Form()
    _item_ui.setupUi(item_widget)

    refresh_title = refresh_text(item, 'title', _item_ui.title)
    refresh_title()
    item.notifier.add_watcher('language_changed', refresh_title)

    refresh_description = refresh_text(item, 'description',
                                       _item_ui.description,
                                       hide_on_empty=True)
    refresh_description()
    item.notifier.add_watcher('language_changed', refresh_description)

    _item_ui.label_invalid_message.hide()
    if isinstance(item, FormItem):
        invalidity_callback = text_connect(item.get_validity_message,
                                           _item_ui.label_invalid_message.setText)
        item.notifier.add_watcher('item_invalid', invalidity_callback)
        item.notifier.add_watcher('item_invalid',
                                  _item_ui.label_invalid_message.show)
        item.notifier.add_watcher('item_valid', _item_ui.label_invalid_message.hide)
        if item.allow_None:
            _item_ui.required_label.hide()
        for key, key_label in item.keys.items():
            input_widget = make_item_input_widget(item_widget, item, key,
                                                  key_label,
                                                  item_is_single=len(item.keys)==1)
            _item_ui.input_layout.addWidget(input_widget)
            if not item.editable:
                input_widget.setEnabled(False)
    return item_widget

class FormWidget(QtWidgets.QWidget, ui.form_ui.Ui_Form):
    def __init__(self, form, origin_sheet_label=None, close_callback=None,
                 user_role=UserRole.EDITOR, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)
        self.origin_sheet_label = origin_sheet_label

        close_callback = if_none(close_callback, lambda w: None)

        # Enable form buttons based on form notifications
        watchers = {
            'previous_section_available':
            [lambda: self.button_previous.setEnabled(True)],
            'previous_section_not_available' :
            [lambda: self.button_previous.setEnabled(False)],
            'next_section_available' :
            [lambda: self.button_next.setEnabled(True)],
            'next_section_not_available' :
            [lambda: self.button_next.setEnabled(False)],
            'ready_to_submit' :
            [lambda: self.button_submit.setEnabled(True)],
            'not_ready_to_submit' :
            [lambda: self.button_submit.setEnabled(False)],
        }
        logger.info('Make UI of live form "%s"', form.label)
        form.notifier.add_watchers(watchers)
        form.validate()

        section_widgets = {}
        self.item_labels = []
        def make_section_widget(section_label, section):
            section_widget = QtWidgets.QWidget(self)
            section_widget.setObjectName("section_widget_" + section_label + \
                                         section.tr.language)
            _section_ui = ui.section_ui.Ui_Form()
            _section_ui.setupUi(section_widget)
            refresh_title = refresh_text(section, 'title',
                                         _section_ui.title_label,
                                         hide_on_empty=True)
            refresh_title()
            section.notifier.add_watcher('language_changed', refresh_title)

            for item in section.items:
                if user_role >= item.access_level:
                    item_widget = make_item_widget(section_widget, item)
                    _section_ui.verticalLayout.addWidget(item_widget)
            return section_widget

        def set_section_ui(section_label, section):
            #if self.current_section_widget is not None:
            #    self.current_section_widget.hide()
            logger.debug2('Set section widget for %s, language: %s',
                          section_label, section.tr.language)
            if section_label not in section_widgets:
                section_widget = make_section_widget(section_label, section)
                section_widgets[section_label] = section_widget
                self.scroll_section_content_layout.addWidget(section_widget,
                                                             0,
                                                             QtCore.Qt.AlignTop)
            else:
                section_widget = section_widgets[section_label]
            logger.debug('set_section_ui, show widget of %s, ',
                         section_label)
            section_widget.show()
            # End of def set_section_ui

        set_section_ui(form.current_section_name, form.current_section)
        self.title_label.setText(form.tr['title'])

        refresh_title = refresh_text(form, 'title', self.title_label,
                                     hide_on_empty=True)
        refresh_title()
        form.notifier.add_watcher('language_changed', refresh_title)

        radio_language_group = QtWidgets.QButtonGroup(self)
        frame = self.frame_language_select
        for idx,language in enumerate(sorted(form.tr.supported_languages)):
            radio_button = QtWidgets.QRadioButton(language_abbrev(language),
                                                  frame)
            radio_button.setObjectName("radio_button_" + language)
            self.language_select_layout.addWidget(radio_button, idx)
            radio_language_group.addButton(radio_button, idx)
            logger.debug('Set radio button for switching language '\
                         'of section %s to %s', form.current_section_name,
                         language)
            class ChoiceProcess:
                def __init__(self, language):
                    self.language = language
                def __call__(self, state):
                    if state:
                        logger.debug('Process language toggle to %s, '\
                                     'current section: %s ', self.language,
                                     form.current_section_name)
                        form.set_language(self.language)
            radio_button.toggled.connect(ChoiceProcess(language))
            if language == form.current_section.tr.language:
                radio_language_group.button(idx).setChecked(True)
        # Set button actions
        def prev_sec():
            # gen_section = lambda : set_section_ui(form.previous_section(),
            #                                       form.to_previous_section())
            # self.section_widget = \
            #     dict_lazy_setdefault(sections, form.previous_section(),
            #                          gen_section)
            logger.debug('Prev_sec, hide widget of %s, ',
                         form.current_section_name)
            section_widgets[form.current_section_name].hide()
            set_section_ui(form.previous_section(),
                           form.to_previous_section())
            self.scroll_section.ensureVisible(0, 0)
        self.button_previous.clicked.connect(prev_sec)

        def next_sec():
            # def gen_section():
            #     gen_section = lambda : set_section_ui(form.next_section(),
            #                                       form.to_next_section())
            # self.section_widget = \
            #     dict_lazy_setdefault(sections, form.next_section(),
            #                          gen_section)
            logger.debug('Next_sec, hide widget of %s',
                         form.current_section_name)
            section_widgets[form.current_section_name].hide()
            set_section_ui(form.next_section(),
                           form.to_next_section())
            self.scroll_section.ensureVisible(0, 0)

        self.button_next.clicked.connect(next_sec)

        def cancel():
            # TODO: adapt question if form is empty
            # TODO: see if init value are actually saved or only user-input?
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Question)
            message_box.setText('The current form entries can be saved '\
                                'for later or discarded. Click on "Cancel" '\
                                'to resume filling the form.')
            message_box.addButton(QtWidgets.QMessageBox.Discard)
            message_box.addButton(QtWidgets.QMessageBox.Cancel)
            message_box.addButton(QtWidgets.QMessageBox.Save)
            result = message_box.exec_()
            if result == QtWidgets.QMessageBox.Discard:
                form.cancel()
            if result != QtWidgets.QMessageBox.Cancel:
                close_callback(self)

        self.button_cancel.clicked.connect(cancel)
        cancel_shortcut = QtWidgets.QShortcut(QtGui.QKeySequence("Escape"),
                                              self)
        cancel_shortcut.activated.connect(cancel)

        def submit():
            #.setEnabled(False)
            self.button_submit.setFocus()
            try:
                form.submit()
            except Exception as e:
                msg = 'Error occured while submitting:\n%s' % repr(e)
                logger.error(msg)
                show_critical_message_box(msg)
                # from IPython import embed; embed()
            close_callback(self)

        self.button_submit.clicked.connect(submit)

# class FormTester(QtWidgets.QDialog):
#     def __init__(self, form, parent=None):
#         super(QtWidgets.QDialog, self).__init__(parent)

#         self.form_widget = FormWidget(form, parent=self)
#         self.layout = QtWidgets.QVBoxLayout()
#         self.layout.addWidget(self.form_widget)
#         self.setLayout(self.layout)

class FormFileEditor(QtWidgets.QWidget, ui.form_editor_file_ui.Ui_Form):
    def __init__(self, form_fn=None, selection_mode=False, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.button_open.clicked.connect(self.on_open)
        self.button_save.clicked.connect(self.on_save)
        self.button_save_as.clicked.connect(self.on_save_as)

        self.unsaved_icon = QtGui.QIcon(':/icons/form_unsaved_icon')

        save_current = lambda : self.save_form(self.form_editor.get_form())
        on_pending = partial(self.button_save.setIcon, self.unsaved_icon)
        on_not_pending = partial(self.button_save.setIcon, QtGui.QIcon())
        self.pending_changes_tracker = \
            PendingChangesTracker(save_current, callback_pending=on_pending,
                                  callback_not_pending=on_not_pending)

        # Form widget
        self.form_editor = FormEditor(parent=self)
        self.form_editor.formChanged.connect(self.pending_changes_tracker
                                             .on_change)

        self.current_tmp_form_fn = None

        if form_fn is not None:
            self.load_form(form_fn)

        self.verticalLayout_2.addWidget(self.form_editor)

    def test_form(self):
        self.form_editor.test_form()
        self.show()

    def load_form(self, form_fn):
        if form_fn is None:
            return

        try:
            self.form_editor.set_form(Form.from_json_file(form_fn))
        except Exception as e:
            show_critical_message_box('Error while opening %s:\n%s' % \
                                      (form_fn, repr(e)))
            logger.error(format_exc())

        self._end_tmp_form_session()
        self.current_form_fn = form_fn
        self._start_tmp_form_session()

    def _start_tmp_form_session(self):
        ftmp, tmp_fn = tempfile.mkstemp(prefix='%s.bak' % \
                                        op.basename(self.current_form_fn),
                                        dir=op.dirname(self.current_form_fn))
        os.close(ftmp)
        self.current_tmp_form_fn = tmp_fn

    def _end_tmp_form_session(self):
        if self.current_tmp_form_fn is not None:
            os.remove(self.current_tmp_form_fn)
            self.current_tmp_form_fn = None

    def on_close(self):
        if self.pending_changes_tracker.process_pending_changes():
            self._end_tmp_form_session()

    def on_save(self):
        self.save_form(self.form_editor.get_form(), ask_as=False)

    def on_save_as(self):
        self.save_form(self.form_editor.get_form(), ask_as=True)

    def on_open(self):
        if self.pending_changes_tracker.process_pending():
            self.load_form(self.ask_open_form_fn())

    def ask_open_form_fn(self):
        open_dir = (op.dirname(self.current_form_fn)
                    if self.current_form_fn is not None else '')
        form_fn, _ = (QtWidgets.QFileDialog
                      .getOpenFileName(self, "Load Form", open_dir,
                                       "Piccel Form Files (*.form)"))
        return form_fn if form_fn != '' else None

    def save_form(self, form, ask_as=False):
        if ask_as:
            form_fn, _ = (QtWidgets.QFileDialog
                          .getSaveFileName(self, "Save Form",
                                           self.current_form_fn,
                                           "Piccel Form Files (*.form)"))
        else:
            form_fn = self.current_form_fn

        if form_fn is not None and form_fn != '':
            form.save_to_json_file(form_fn)
            logger.info('Form %s saved to %s', form.label, form_fn)
            if form_fn != self.current_form_fn:
                self._end_tmp_form_session()
                self.current_form_fn = form_fn
                self._start_tmp_form_session()
            self.pending_changes_tracker.set_pending_change_state(False)
            return True
        else:
            return False

    def save_temporary_form(self, form):
        # TODO show some message in status bar!
        form.save_to_json_file(form_fn, self.current_tmp_form_fn)

from PyQt5.QtCore import pyqtSignal

class FormEditor(QtWidgets.QWidget, ui.form_editor_widget_ui.Ui_FormEditor):

    formChanged = pyqtSignal()

    def __init__(self, form=None, locked_variable_types=None,
                 selection_mode=None, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.selection_mode = selection_mode

        self.locked_variable_types = (locked_variable_types
                                      if locked_variable_types is not None
                                      else {})

        self.tree_view.setContextMenuPolicy(QtCore.Qt.CustomContextMenu)
        self.tree_view.customContextMenuRequested.connect(self.open_menu)

        self.tree_view.doubleClicked.connect(self.on_view_double_click)
        self.tree_view.clicked.connect(self.on_view_click)

        self.tree_view.setSelectionMode(QtWidgets.QAbstractItemView.SingleSelection)
        self.tree_view.setDragDropMode(QtWidgets.QAbstractItemView.DragDrop);

        self.tree_view.setDragEnabled(True);
        self.tree_view.setAcceptDrops(True);
        self.tree_view.setDropIndicatorShown(True);

        read_only_props = self.selection_mode is not None
        self.form_property_editor = FormPropertyEditor(read_only=read_only_props,
                                                       parent=self)
        self.verticalLayout.addWidget(self.form_property_editor)

        self.section_property_editor = \
            SectionPropertyEditor(read_only=read_only_props, parent=self)
        self.verticalLayout.addWidget(self.section_property_editor)

        self.section_transition_property_editor = \
            SectionTransitionPropertyEditor(read_only=read_only_props,
                                            parent=self)
        self.verticalLayout.addWidget(self.section_transition_property_editor)

        self.item_property_editor = ItemPropertyEditor(read_only=read_only_props,
                                                       parent=self)
        self.verticalLayout.addWidget(self.item_property_editor)

        self.choice_property_editor = \
            ChoicePropertyEditor(read_only=read_only_props)
        self.verticalLayout.addWidget(self.choice_property_editor)

        self.variable_property_editor = \
            VariablePropertyEditor(read_only=read_only_props)
        self.verticalLayout.addWidget(self.variable_property_editor)

        form = if_none(form, Form(default_language='French',
                                  supported_languages=['English', 'French']))
        logger.debug('Edit form %s in selection_mode: %s', form.label,
                     self.selection_mode)
        self.set_form(form, self.locked_variable_types)

        def on_preview_mode_change(state):
            pass
        self.button_preview_mode.toggled.connect(on_preview_mode_change)
        button_preview_mode_icon = QtGui.QIcon()
        button_preview_mode_icon.addPixmap(QtGui.QPixmap(':/icons/on_icon'),
                                           QtGui.QIcon.Normal,
                                           QtGui.QIcon.Off);
        button_preview_mode_icon.addPixmap(QtGui.QPixmap(':/icons/off_icon'),
                                           QtGui.QIcon.Normal,
                                           QtGui.QIcon.On);
        self.button_preview_mode.setIcon(button_preview_mode_icon)

        self.hide_property_editors()

        self.import_icon = QtGui.QIcon(':/icons/form_import_icon')
        self.delete_icon = QtGui.QIcon(':/icons/form_delete_icon')
        self.choices_icon = QtGui.QIcon(':/icons/form_choices_icon')
        self.multi_variable_icon = QtGui.QIcon(':/icons/form_multi_variable_icon')
        self.text_item_icon = QtGui.QIcon(':/icons/text_icon')

    def get_selection(self):
        if self.selection_mode is None or len(self.model.root.childItems) == 0:
            return []

        form_node = self.model.root.childItems[0]
        if self.selection_mode == 'section':
            selection = {}
            for section_node in form_node.childItems:
                if section_node.state == 'sel_checked':
                    selection[section_node.label] = \
                        section_node.to_dict(selected_only=True)
        elif self.selection_mode == 'item':
            sub_form_dict = form_node.to_dict(selected_only=True)
            selection = []
            for section_dict in sub_form_dict['sections'].values():
                for item in section_dict['items']:
                    selection.append(item)

        return selection

    def on_change(self):
        self.formChanged.emit()

    def set_form(self, form, lock_variable_types=None):
        lock_variable_types = if_none(lock_variable_types, {})
        if form is not None:
            form.set_supported_languages(['French', 'English'])
            print('set_form, lock_variable_types:')
            print(lock_variable_types)
            self.model = TreeModel(form.to_dict(), lock_variable_types,
                                   selection_mode=self.selection_mode)
            self.tree_view.setModel(self.model)
            self.tree_view.expandAll()
            self.tree_view.resizeColumnToContents(1)

    def hide_property_editors(self):
        self.form_property_editor.hide()
        self.section_property_editor.hide()
        self.item_property_editor.hide()
        self.choice_property_editor.hide()
        self.variable_property_editor.hide()
        self.section_transition_property_editor.hide()

    def on_view_click(self, model_index):
        self.hide_property_editors()
        model_item = self.model.getItem(model_index)
        logger.debug('Clicked: %s (state: %s)',
                     model_item.label, model_item.state)

        self.model.toggle_node_selection(model_index)
        if self.selection_mode is not None:
            return

        if model_item.node_type == 'form':
            self.show_form_editor(model_item)
        elif model_item.node_type == 'section':
            self.show_section_editor(model_item)
        elif model_item.node_type.startswith('item'):
            self.show_item_editor(model_item)
        elif model_item.node_type == 'choice':
            self.show_choice_editor(model_item)
        elif model_item.node_type == 'variable':
            self.show_variable_editor(model_item)
        elif model_item.node_type == 'transition_rule':
            self.show_section_transition_editor(model_item)

    def show_variable_editor(self, var_node):
        self.variable_property_editor.attach(var_node)
        self.variable_property_editor.show()

    def show_section_transition_editor(self, transition_node):
        self.section_transition_property_editor.attach(transition_node)
        self.section_transition_property_editor.show()

    def show_choice_editor(self, choice_node):
        self.choice_property_editor.attach(choice_node)
        self.choice_property_editor.show()

    def show_form_editor(self, form_node):
        self.form_property_editor.attach(form_node)
        self.form_property_editor.show()

    def show_section_editor(self, section_node):
        self.section_property_editor.attach(section_node)
        self.section_property_editor.show()

    def show_item_editor(self, item_node):
        self.item_property_editor.attach(item_node)
        self.item_property_editor.show()

    def on_view_double_click(self, model_index):
        self.hide_property_editors()
        node = self.model.getItem(model_index)
        parent_index = model_index.parent()
        self.on_change()
        if node.node_type == 'add_button' and \
           self.model.new_child(parent_index):
            self.tree_view.expand(model_index.parent())

    def insert_new_before(self, model_index):
        current_item = self.model.getItem(model_index)
        current_row = current_item.childNumber()
        # print('Insert new before %s, at row %d' \
        #       %(current_item.label, current_row))
        self.model.insertRows(current_row, 1, model_index.parent())

    def ___add_sub_variables(self, item_model_index):
        self.model.add_sub_variables(item_model_index)
        self.tree_view.expandRecursively(item_model_index)

    def add_choices_to_item(self, item_model_index):
        self.model.new_child(self.model.add_choices_node(item_model_index))
        self.tree_view.expandRecursively(item_model_index)

    def add_other_choice_node_to_choices_node(self, item_model_index):
        self.model.add_other_choice_node_to_choices_node(item_model_index)
        self.tree_view.expandRecursively(item_model_index)

    def get_form(self):
        return Form.from_dict(self.model.root.childItems[0].to_dict())

    # def closeEvent(self, event):
    #     if self.process_pending_changes():
    #         self.form_io.close_form_edition()
    #         event.accept()
    #         return True
    #     else:
    #         event.ignore()
    #         return False

    def test_form(self, role=UserRole.VIEWER):
        form = self.get_form()
        logger.debug('Test form: %s', pformat(form.to_dict()))
        FormWidget(form, user_role=role, parent=None).show()

    def ask_import_sections(self, form_index):
        self._ask_import(form_index, 'section')

    def ask_import_items(self, section_index):
        self._ask_import(section_index, 'item')

    def on_form_selector_finished(self, parent_index, selector, result):
        logger.debug('Process form importation with result %s', result)
        self.show()
        if result:
            selection_mode, selection = selector.get_selection()
            logger.debug('Selected %d elements for importation (mode %s)',
                         len(selection), selection_mode)
            logger.debug2('Imported dict: %s', selection)
            if selection_mode == 'section':
                # ASSUME: parent_index is form
                for section_label, section_dict in selection.items():
                    self.model.insert_section(section_label, section_dict,
                                              parent_index)
            elif selection_mode == 'item':
                # ASSUME: parent_index is section
                for item_dict in selection:
                    self.model.insert_item(section_label, section_dict,
                                           parent_index)
            self.tree_view.expandRecursively(parent_index, depth=2)
        self.selector = None

    def _ask_import(self, parent_index, selection_mode):

        fn_format = 'Piccel form file (*.form)'
        form_fn, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Open file',
                                                           '', fn_format)
        if form_fn is not None and form_fn != '':
            logger.debug('Import from %s, mode: %s', form_fn, selection_mode)
            self.selector = FormSelector(Form.from_json_file(form_fn),
                                         selection_mode)
            self.selector.setWindowModality(QtCore.Qt.ApplicationModal)
            self.finished_callback = partial(self.on_form_selector_finished,
                                             parent_index, self.selector)
            self.selector.finished.connect(self.finished_callback)
            self.selector.open()

    def variable_is_locked(self, node):
        if node.node_type in ['item_single_var', 'variable']:
            var_name = node.label
        else:
            return False
    def open_menu(self, position):
        # indexes = self.sender().selectedIndexes()
        model_index = self.tree_view.indexAt(position)
        if self.selection_mode is not None or not model_index.isValid():
            return

        self.hide_property_editors()

        model_item = self.model.getItem(model_index)
        right_click_menu = QtWidgets.QMenu()

        if model_item.node_type == 'item_single_var':
            action = right_click_menu.addAction(self.multi_variable_icon,
                                                self.tr("To group of variables"))
            f = partial(self.model.convert_item_to_multi_var, model_index)
            action.triggered.connect(f)

        if model_item.node_type in ['item_single_var', 'item']:
            action = right_click_menu.addAction(self.text_item_icon,
                                                self.tr("To text-only"))
            f = partial(self.model.convert_item_to_text_only, model_index)
            action.triggered.connect(f)

            if len(model_item.childItems) == 0 or \
               model_item.childItems[0].node_type != 'choices':
                action = right_click_menu.addAction(self.choices_icon,
                                                    self.tr("Add choices"))
                f = partial(self.add_choices_to_item, model_index)
                action.triggered.connect(f)

        if isinstance(model_item, ChoicesNode) and \
           model_item.other_choice_node() is None:
            action = right_click_menu.addAction(self.choices_icon,
                                                self.tr("Add Other choice"))
            f = partial(self.add_other_choice_node_to_choices_node, model_index)
            action.triggered.connect(f)

        if model_item.node_type == 'form':

            test_menu = right_click_menu.addMenu(self.tr('Test'))
            for role in UserRole:
                act_test = test_menu.addAction(self.tr('As %s') % role.name)
                act_test.triggered.connect(partial(self.test_form, role))

            act_test = right_click_menu.addAction(self.import_icon,
                                                  self.tr('Import'))
            act_test.triggered.connect(partial(self.ask_import_sections,
                                               model_index))

        # if model_item.node_type == 'section':
        #     act_test = right_click_menu.addAction(self.tr('Import item(s)'))
        #     act_test.triggered.connect(partial(self.ask_import_items,
        #                                        model_index))

        if model_item.node_type not in ['add_button', 'form', 'transition_rules']\
            and (model_item.node_type not in ['item_single_var', 'variable'] or \
                 model_item.label not in self.locked_variable_types):
            act_del = right_click_menu.addAction(self.delete_icon,
                                                 self.tr("Delete"))
            act_del.triggered.connect(partial(self.model.removeRow,
                                              model_index.row(),
                                              model_index.parent()))

        right_click_menu.exec_(self.sender().viewport().mapToGlobal(position))


    # def delete_tree_item(self, index):
    #     print('delete_tree_item: %s' % index)
    #     self.model.removeRow(index.row(), index.parent())

    # def insertChild(self, index=None):
    #     index = (index if index is not None
    #              else self.tree_view.selectionModel().currentIndex())
    #     model = self.tree_view.model()

    #     if model.columnCount(index) == 0:
    #         if not model.insertColumn(0, index):
    #             return

    #     if not model.insertRow(0, index):
    #         return

    #     (self.tree_view.selectionModel()
    #      .setCurrentIndex(model.index(0, 0, index),
    #                       QItemSelectionModel.ClearAndSelect))
    #     self.updateActions()

    # def insertColumn(self):
    #     model = self.tree_view.model()
    #     column = self.tree_view.selectionModel().currentIndex().column()

    #     changed = model.insertColumn(column + 1)
    #     if changed:
    #         model.setHeaderData(column + 1, Qt.Horizontal, "[No header]",
    #                             Qt.EditRole)

    #     self.updateActions()

    #     return changed

    # def insertRow(self):
    #     index = self.tree_view.selectionModel().currentIndex()
    #     model = self.tree_view.model()

    #     if not model.insertRow(index.row()+1, index.parent()):
    #         return

    #     self.updateActions()

    # def removeRow(self):
    #     index = self.tree_view.selectionModel().currentIndex()
    #     model = self.tree_view.model()

    #     if (model.removeRow(index.row(), index.parent())):
    #         self.updateActions()

    # def updateActions(self):
    #     hasSelection = not self.tree_view.selectionModel().selection().isEmpty()
    #     self.removeRowAction.setEnabled(hasSelection)

    #     hasCurrent = self.tree_view.selectionModel().currentIndex().isValid()
    #     self.insertRowAction.setEnabled(hasCurrent)

    #     if hasCurrent:
    #         self.tree_view.closePersistentEditor(self.tree_view.selectionModel().currentIndex())

    #         row = self.tree_view.selectionModel().currentIndex().row()
    #         column = self.tree_view.selectionModel().currentIndex().column()
    #         if self.tree_view.selectionModel().currentIndex().parent().isValid():
    #             self.statusBar().showMessage("Position: (%d,%d)" % (row, column))
    #         else:
    #             self.statusBar().showMessage("Position: (%d,%d) in top level" % (row, column))


from functools import partial
from PyQt5.QtCore import (QAbstractItemModel, QFile, QIODevice,
                          QItemSelectionModel, QModelIndex, Qt)

class Node(object):

    NEXT_SEL_STATE = {'sel_unchecked' : 'sel_checked',
                      'sel_checked' : 'sel_unchecked'}

    def __init__(self, label, node_type, pdict=None, is_container=False,
                 parent=None, child_type=None, state='base'):
        self.parentItem = parent
        self.label = label
        self.node_type = node_type
        self.is_container = is_container
        self.child_type = child_type
        self.childItems = []
        self.state = state
        self.pdict = if_none(pdict, {})

    def to_json(self):
        exported_dict = self.to_dict()
        exported_dict['parent_label'] = self.parent().label
        exported_dict['origin_node_type'] = self.node_type
        return json.dumps(exported_dict)

    def child_labels(self):
        return [c.label for c in self.childItems
                if c.node_type == self.child_type]

    def to_dict(self, selected_only=False):
        pdict_copy = self.pdict.copy()
        if self.node_type == 'form':
            return {
                **pdict_copy,
                **{'label' : self.label,
                   'sections':{s.label:s.to_dict() for s in self.childItems
                               if (s.node_type == self.child_type and \
                                   (not selected_only or s.state=='sel_checked'))}
                }
            }

        elif self.node_type == 'section':
            return {
                **pdict_copy,
                **self.childItems[0].to_dict(),
                **{'label' : self.label,
                   'items' : [i.to_dict() for i in self.childItems
                              if (i.node_type == self.child_type and \
                                  (not selected_only or i.state=='sel_checked'))]}
            }
        elif self.node_type == 'transition_rules':
            return {
                'next_section_definition' : [
                    (child.pdict['predicate'], child.pdict['next_section'])
                    for child in self.childItems
                    if child.node_type == self.child_type
                ]
            }

        elif self.node_type.startswith('item'):
            var_dict = {'keys' : {}, 'init_values' : None}
            if self.node_type == 'item':
                init_values = {child.label : child.pdict['init_value']
                               for child in self.childItems
                               if (child.node_type == self.child_type and
                                   child.node_type == 'variable')}
                if all(value is None for value in init_values):
                    init_values = None
                var_dict = {
                    'keys' : {
                        child.label : child.pdict['key_tr']
                        for child in self.childItems
                        if (child.node_type == self.child_type and
                            (not selected_only or i.state=='sel_checked'))
                    },
                    'init_values' : init_values
                }
            elif self.node_type == 'item_text':
                var_dict['keys'] = None
                var_dict['init_values'] = None
            elif self.node_type == 'item_single_var':
                var_dict['keys'][self.label] = pdict_copy.pop('key_tr')
                if pdict_copy['init_value'] is not None:
                    var_dict['init_values'] = {self.label :
                                               pdict_copy.pop('init_value')}
                else:
                    pdict_copy.pop('init_value', None)
                    var_dict['init_values'] = None
            else:
                raise Exception('Unhandled item node type %s' % self.node_type)

            choices_node, other_choice_node = None, None
            if len(self.childItems) > 0 and \
               self.childItems[0].node_type == 'choices':
                choices_node = self.childItems[0]
                # TODO handle other choice

            pdict_copy.pop('type_locked')
            logger.debug('Keys in pdict of %s before conversion to Form dict: %s',
                         self.label, ", ".join(pdict_copy.keys()))
            return {
                **pdict_copy,
                **var_dict,
                **{'label' : self.label,
                   'choices' : (choices_node.to_dict()
                                if choices_node is not None else None),
                   'other_choice_label' : (other_choice_node.choice_tr.copy()
                                           if other_choice_node is not None
                                           else None)}
            }

        elif self.node_type == 'choices':
            return {child.label : child.pdict.copy()
                    for child in self.childItems
                    if child.node_type == self.child_type}
        elif self.node_type == 'choice':
            return {self.label : pdict_copy}
        elif self.node_type == 'variable':
            raise Exception('Should not be called?')
            return {
                'keys' : {self.label : pdict_copy['key_tr']},
                'init_values' : {self.label : pdict_copy['init_value']}
            }
        else:
            raise Exception('Unhandled node type %s' % self.node_type)

    def child(self, row):
        if row < 0 or row >= len(self.childItems):
            return None
        return self.childItems[row]

    def childCount(self):
        return len(self.childItems)

    def childNumber(self):
        if self.parentItem != None:
            return self.parentItem.childItems.index(self)
        return 0

    def columnCount(self):
        return 1

    def data(self, column):
        if column != 0:
            return None
        return self.label

    # def __insertChildren(self, position, count):
    #     return False

    # def insertColumns(self, position, columns):
    #     return False

    def parent(self):
        return self.parentItem

    def removeChildren(self, position=0, count=None):
        count = count if count is not None else len(self.childItems) - position

        if position < 0 or position + count > len(self.childItems):
            return False

        for row in reversed(range(count)):
            # Remove all children's children recursively
            print('Remove pos %d + row %d from %d children of %s' % \
                  (position, row, len(self.childItems), self.label))
            self.childItems.pop(position + row).removeChildren()

        # TODO emit signal here??

        return True

    def removeColumns(self, position, columns):
        return False

    def setData(self, column, value):
        if column != 0:
            return False

        self.label = value
        return True

class ___RootNode(Node):

    def __init__(self, lock_variable_types, parent=None):
        super(RootNode, self).__init__('', parent)
        self.lock_variable_types = lock_variable_types

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems) or \
           len(self.childItems) > 0: # allow only one child
            return False

        self.childItems[position:position+nb_children-1] = \
            [self._new_form_node() for i in range(nb_children)]

        return True

    def _new_form_node(self):
        return FormNode(Form({}, 'English', ['English', 'French']).to_dict(),
                        self.lock_variable_types, parent=self)

class ___FormNode(Node):
    def __init__(self, form_dict, lock_variable_types, parent=None):
        super(FormNode, self).__init__(form_dict.pop('label'), parent)
        self.form_dict = form_dict.copy()
        self.lock_variable_types = lock_variable_types
        # sections = self.form_dict.pop('sections')

        # children are sections
        # self.childItems = [SectionNode(section_name, section, lock_variable_types,
        #                               parent=self)
        #                   for section_name, section in sections.items()]
        # self.childItems.append(AddSectionNode(self))

    def set_pdict(self, pdict):
        self.pdict = pdict.copy()

    def section_labels(self):
        return [s.label for s in self.childItems
                if s.node_type == self.child_type]

    def section_after(self, section_node):
        i_section = section_node.childNumber()
        return (self.childItems[i_section+1].label if i_section < self.childCount()-1
                else None)

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:(position+nb_children-1)] = \
            [self._new_section_node() for i in range(nb_children)]

        return True

    def section_labels(self):
        return set(s.label for s in self.childItems)

    def new_child_label(self, label_pat='section_%d', label=None):
        set_names = self.section_labels()

        if label is not None and label not in set_names:
            return label

        i_section = len(self.childItems)
        while label_pat % i_section in set_names:
            i_section += 1
        section_name = label_pat % i_section

    def _new_section_node(self):
        section_name = self.new_child_label()
        new_section_cfg = (FormSection([], self.form_dict['default_language'],
                                       self.form_dict['supported_languages'])
                           .to_dict())
        return SectionNode(section_name, new_section_cfg,
                           self.lock_variable_types, parent=self)

    def to_dict(self):
        return {
            **self.form_dict,
            **{'label' : self.label,
               'sections' : {s.label : s.to_dict() for s in self.childItems[:-1]}
            }
        }


class ___SectionNode(Node):
    def __init__(self, section_name, section_dict, lock_variable_types,
                 parent=None):
        super(SectionNode, self).__init__(section_name, parent)
        self.section_dict = section_dict
        #self.section_name = section_name
        self.lock_variable_types = lock_variable_types
        self.state = 'base'

        #transitions_cfg = self.section_dict.pop('next_section_definition')
        #transitions_node = SectionTransitionsNode(transitions_cfg, parent=self)
        #self.childItems.append(transitions_node)

        #self.childItems.extend(ItemNode(item['label'], item, lock_variable_types,
        #                                parent=self) for item in
        #                      self.section_dict.pop('items'))
        #self.childItems.append(AddItemNode(self))

    def set_pdict(self, pdict):
        self.section_dict = pdict

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:(position+nb_children-1)] = \
            [self._new_item() for i_item in range(nb_children)]
        return True

    def all_keys(self):
        set_keys = set()
        for item in self.childItems:
            if not isinstance(item, (AddItemNode, SectionTransitionsNode)):
                set_keys.update(item.all_keys())
        return set_keys


    def new_child_label(self, label_pat='Var_%d', label=None):
        used_keys = self.all_keys()

        if label is not None and label not in used_keys:
            return label

        label_idx = len(used_keys)
        while  label_pat % label_idx in used_keys:
            label_idx += 1

        return label_pat % label_idx

    def _new_item(self):
        used_keys = self.all_keys()
        label_pat = 'Var_%d'
        label_idx = len(used_keys)
        while  label_pat % label_idx in used_keys:
            label_idx += 1

        item_label = label_pat % label_idx

        new_item_dict = FormItem({item_label : {'French': 'Nom de variable',
                                                'English' : 'Variable name'}},
                                 self.section_dict['default_language'],
                                 self.section_dict['supported_languages'],
                                 label=item_label).to_dict()

        new_node = ItemNode(new_item_dict.pop('label'), self.lock_variable_types,
                            parent=self)
        new_node.set_pdict(new_item_dict)
        return new_node

    def to_dict(self):
        return {
            **self.section_dict,
            **self.childItems[0].to_dict(),
            **{'items' : [i.to_dict() for i in self.childItems[1:-1]]}
        }

    def to_json(self):
        return json.dumps({**{'label':self.label,
                              'parent_label':self.parent().label},
                           **self.to_dict()})

class SectionTransitionsNode(Node):
    def __init__(self, parent=None):
        super(SectionTransitionsNode, self).__init__('next section', parent)
        # if transitions_cfg is not None:
        #     if isinstance(transitions_cfg, str):
        #         self.childItems.append(SectionTransitionNode('transition rule 1',
        #                                                      transitions_cfg, parent=self))
        #     else:
        #         self.childItems = [SectionTransitionNode('transition rule %d' % it,
        #                                                  transition_def, parent=self)
        #                            for it, transition_def in enumerate(transitions_cfg)]

        # self.childItems.append(AddSectionTransitionNode(self))

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:(position+nb_children-1)] = \
            [self._new_transition() for i_item in range(nb_children)]
        return True

    def _new_transition(self):
        #                        .section .form
        next_section_label = self.parent().parent().section_after(self.parent())
        if next_section_label is None:
            next_section_label = '__submit__'
        return SectionTransitionNode('transition rule %d' % len(self.childItems),
                                     ('True', next_section_label), parent=self)

    def to_dict(self):
        return {
            'next_section_definition' : [child.transition_rule()
                                         for child in self.childItems[:-1]]
        }

class SectionTransitionNode(Node):
    def __init__(self, label, transition_cfg, parent=None):

        #if isinstance(transition_cfg, str):
        #    transition_cfg = ('True', transition_cfg)

        # label = ('submit' if transition_cfg[1] == '__submit__'
        #          else 'to %s' % transition_cfg[1])
        super(SectionTransitionNode, self).__init__(label, parent)

        self.cfg = {
            'predicate' : transition_cfg[0],
            'next_section' : transition_cfg[1]
        }

    def transition_rule(self):
        return (self.cfg['predicate'], self.cfg['next_section'])

class ItemNode(Node):
    def __init__(self, label, locked_variable_types=None, parent=None):
        self.locked_variable_types = (locked_variable_types
                                      if locked_variable_types is not None
                                      else {})
        super(ItemNode, self).__init__(label, parent)
        self.state = 'base'

    def set_pdict(self, item_dict):

        self.key_tr = None
        self.init_values = None

        if len(item_dict['keys']) > 0:
            self.text_only = False
            if len(item_dict['keys']) == 1:
                try:
                    self.key_tr = item_dict['keys'][self.label]
                except KeyError:
                    from IPython import embed; embed()
                init_values = item_dict.pop('init_values')
                self.init_value = (init_values[self.label]
                                   if init_values is not None else None)
        else:
            self.text_only = True
        item_dict.pop('keys')

        self.item_dict = item_dict
        self.check_locked_var_types()

    def check_locked_var_types(self):
        self.type_locked = False
        for var_name in self.all_keys():
            if var_name in self.locked_variable_types:
                self.type_locked = True
                self.item_dict['vtype'] = self.locked_variable_types[var_name]
                break

    def setData(self, column, value):
        if value not in self.parent().all_keys():
            success = super(ItemNode, self).setData(column, value)
            if self.variables_node() is None:
                self.check_locked_var_types()
            return success
        else:
            return False

    def removeChildren(self, position=0, count=None):
        count = count if count is not None else len(self.childItems) - position

        if position < 0 or position + count > len(self.childItems):
            return False
        saved_key_tr, saved_init_value = None, None
        for row in reversed(range(count)):
            child = self.childItems[position + row]
            if isinstance(child, VariablesNode):
                nb_sub_children = child.childCount()
                if nb_sub_children == 2:
                    saved_key_tr = child.childItems[0].cfg['key_tr'].copy()
                    saved_init_value = child.childItems[0].cfg['init_value']
                elif nb_sub_children > 2:
                    logger.warning('Cannot retrieve key translation and '\
                                   'init value from several deleted variables')
                break
        success = super(ItemNode, self).removeChildren(position, count)
        if success and saved_key_tr is not None:
            self.key_tr = saved_key_tr
            self.init_value = saved_init_value

        return success

    def add_variables_node(self, keys=None, init_values=None):
        if self.variables_node() is None:
            keys = if_none(keys, {self.label : self.key_tr})
            init_values = if_none(init_values, {self.label : self.init_value})
            variables_node = VariablesNode(keys, init_values, parent=self)
            self.childItems.append(variables_node)
            return True
        return False

    def variables_node(self):
        for child in self.childItems:
            if isinstance(child, VariablesNode):
                return child
        return None

    def new_label(self, label_pat='Var_%d'):
        return self.parent().new_child_label(label_pat)

    def choices_node(self):
        for child in self.childItems:
            if isinstance(child, ChoicesNode):
                return child
        return None

    def to_dict(self):
        var_dict = {'keys' : {}, 'init_values' : None}
        variables_node = self.variables_node()
        if variables_node is None:
            if not self.text_only:
                var_dict['keys'][self.label] = self.key_tr
                if self.init_value is not None:
                    var_dict['init_values'] = {self.label : self.init_value}
            else:
                var_dict['keys'] = None
                var_dict['init_values'] = None
        else:
            var_dict = variables_node.to_dict()

        choices_node = self.choices_node()
        if choices_node is not None:
            other_choice_node = choices_node.other_choice_node()
        else:
            other_choice_node = None
        return {
            **self.item_dict,
            **var_dict,
            **{'choices' : (choices_node.to_dict()
                            if choices_node is not None else None),
               'other_choice_label' : (other_choice_node.choice_tr.copy()
                                       if other_choice_node is not None
                                       else None)}
        }

    def to_json(self):
        return json.dumps({**{'label':self.label,
                              'parent_label':self.parent().label},
                           **self.to_dict()})

    def __add_choices_node(self, force=False):
        if force or self.choices_node() is None:
            choices_node = ChoicesNode({}, parent=self)
            self.childItems.insert(0, choices_node)
            return True
        return False

    def all_keys(self):
        variables_node = self.variables_node()
        if variables_node is None:
            return {self.label}
        else:
            return variables_node.all_keys()


class ChoicesNode(Node):
    def __init__(self, choices, parent=None):
        super(ChoicesNode, self).__init__('choices', parent)
        for choice_value, choice_tr in choices.items():
            self.childItems.append(ChoiceNode(choice_value, choice_tr,
                                              parent=self))

    def to_dict(self):
        return {child.label : child.choice_tr for child in self.childItems[:-1]
                if isinstance(child, ChoiceNode)}

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:(position+nb_children-1)] = \
            [self._new_choice_node() for i in range(nb_children)]

        return True

    def other_choice_node(self):
        for child in self.childItems:
            if isinstance(child, OtherChoiceNode):
                return child
        return None

    def add_other_choice_node(self):
        if self.other_choice_node() is None:
            other_choice_node = OtherChoiceNode({'French': 'Autre :',
                                                 'English' : 'Other'},
                                                parent=self)
            self.childItems.insert(0, other_choice_node)
            return True
        return False

    def children_labels(self):
        return set(child.label for child in self.childItems
                   if not isinstance(child, AddChoiceNode))

    def new_child_label(self, label_pat='choice_%d', label=None):
        used_choices = self.all_choice_labels
        if label is not None and label not in used_choices:
            return label

        i_choice = len(self.childItems) - 1
        while 'choice_%d' % i_choice in used_choices:
            i_choice += 1
        choice = 'choice_%d' % i_choice

    def _new_choice_node(self):
        return ChoiceNode(self.new_child_label(),
                          {'French': 'Choix %d' % i_choice,
                           'English' : 'Choice %d' % i_choice},
                          parent=self)

class VariablesNode(Node):
    def __init__(self, keys_tr, init_values, parent=None):
        super(VariablesNode, self).__init__('variables', parent)

        for key, key_tr in keys_tr.items():
            init_value = (init_values.get(key, None)
                          if init_values is not None else None)
            self.childItems.append(VarNode(key, key_tr, init_value, parent=self))

        self.childItems.append(AddVarNode(self))

    def all_keys(self):
        return {child.label for child in self.childItems
                if not isinstance(child, AddVarNode)}

    def to_dict(self):
        init_values = {child.label : child.cfg['init_value']
                       for child in self.childItems[:-1]}
        if all(value is None for value in init_values):
            init_values = None
        return {
            'keys' : {
                child.label : child.cfg['key_tr'] for child in self.childItems[:-1]
            },
            'init_values' : init_values
        }

    def insertChildren(self, position, nb_children):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position+nb_children-1] = \
            [self._new_var_node() for i in range(nb_children)]

        self.parent().check_locked_var_types()
        return True

    def _new_var_node(self):
        var_name =  self.parent().new_label()

        return VarNode(var_name, {'French': 'Nom de variable %d' % i_var,
                                  'English' : 'Name of variable %d' % i_var},
                       None, parent=self)

class VarNode(Node):
    def __init__(self, label, key_tr, init_value, parent=None):
        super(VarNode, self).__init__(label, parent)
        key_tr = {'French' : '', 'English' : ''}  if key_tr is None else key_tr
        self.cfg = {
            'key_tr' : key_tr,
            'init_value' : init_value
        }

        self.state = 'base'

    def setData(self, column, value, force=False):
        success = super(VariablesNode, self).setData(column, value)
        self.parent().parent().check_locked_var_types()
        return success

    def new_label(self, label_pat='Var_%d'):
        return self.parent().parent().new_child_label(label_pat)


class ChoiceNode(Node):
    def __init__(self, label, choice_tr, parent=None):
        super(ChoiceNode, self).__init__(label, parent)
        self.choice_tr = choice_tr

    def new_label(self, label_pat='choice_%d'):
        return self.parent().new_child_label(label_pat)

class OtherChoiceNode(Node):
    def __init__(self, choice_tr, parent=None):
        super(OtherChoiceNode, self).__init__('[Other]', parent)
        self.choice_tr = choice_tr

class AddSectionNode(Node):
    def __init__(self, parent=None):
        super(AddSectionNode, self).__init__('+', parent)

class AddItemNode(Node):
    def __init__(self, parent=None):
        super(AddItemNode, self).__init__('+', parent)

class AddVarNode(Node):
    def __init__(self, parent=None):
        super(AddVarNode, self).__init__('+', parent)

class AddSectionTransitionNode(Node):
    def __init__(self, parent=None):
        super(AddSectionTransitionNode, self).__init__('+', parent)

class AddChoiceNode(Node):
    def __init__(self, parent=None):
        super(AddChoiceNode, self).__init__('+', parent)

def make_unique_label(label, existing_labels):
    idx = 0
    label_origin = label
    while label in existing_labels:
        idx += 1
        label = label_origin + '_%d' % idx
    return label

ChildDef = namedtuple('ChildDef', ['node_types', 'is_container',
                                   'gen_label', 'gen_pdict'])
DLG = 'English'
SLG = ['English', 'French']

def gen_unique_label(label, parent_node, tree_model):
    return make_unique_label(label, tree_model.child_labels(parent_node))

def gen_item_label(parent_node, tree_model):
    if parent_node.node_type == 'section':
        all_keys = tree_model.all_section_keys(parent_node)
    elif parent_node.node_type == 'item':
        all_keys = tree_model.all_section_keys(parent_node.parent())
    all_keys.extend(tree_model.locked_variable_types.keys())
    label = make_unique_label('Var', all_keys)
    logger.debug('Generated variable label: %s', label)
    return label

def gen_new_item_single_var(label):
    item_dict = FormItem({label : {'French': 'Nom de variable',
                             'English': 'Variable name'}},
                         DLG, SLG, label=label).to_dict()
    item_dict['key_tr'] = item_dict.pop('keys')[label]
    if item_dict['init_values'] is not None:
        item_dict['init_value'] = (item_dict.pop('init_values').get(label, None))
    else:
        item_dict['init_value'] = None
    # Assume generated variable label is not associated with a locked type:
    item_dict['type_locked'] = False
    return item_dict

class TreeModel(QAbstractItemModel):
    CHILD_DEF = {
        'form' : ChildDef(['section'], True,
                          partial(gen_unique_label, 'section'),
                          lambda l: FormSection([], DLG, SLG).to_dict()),
        'section' : ChildDef(['item_single_var', 'item_text', 'item'],
                             False, gen_item_label, gen_new_item_single_var),
        'item' : ChildDef(['variable'], False, gen_item_label,
                          lambda l: {'key_tr' : {'French': 'Nom de variable',
                                                 'English': 'Variable name'},
                                     'init_value' : None}),
        'choices' : ChildDef(['choice'], False,
                             partial(gen_unique_label, 'choice'),
                             lambda l: {'French': 'Choix',
                                        'English': 'Choices'}),
        'transition_rules' : ChildDef(['transition_rule'], False,
                                      partial(gen_unique_label,'transition_rule'),
                                      lambda l: {'predicate' : 'True',
                                                 'next_section' : '__submit__'}),
    }

    def __init__(self, form_dict, locked_variable_types=None, selection_mode=None,
                 parent=None):
        super(TreeModel, self).__init__(parent)
        self.selection_mode = selection_mode

        self.locked_variable_types = locked_variable_types
        #self.root = MotherNode('')
        #self.root.childItems.append(FormNode(form_dict, locked_variable_types,
        #                                     parent=self.root))

        self.root = Node('root', 'root')
        # self.insert_node('', 'root', QModelIndex(),
        #                  is_container=True)
        self.insert_form(form_dict)

        self.text_item_icon = {
            'base' : QtGui.QIcon(':/icons/text_icon'),
            'sel_checked' : QtGui.QIcon(':/icons/form_checked_text_icon'),
            'sel_unchecked' : QtGui.QIcon(':/icons/form_unchecked_text_icon')
        }

        self.multi_variable_icon = {
            'base' : QtGui.QIcon(':/icons/form_multi_variable_icon'),
            'sel_checked' : QtGui.QIcon(':/icons/form_checked_multi_variable_icon'),
            'sel_unchecked' : QtGui.QIcon(':/icons/form_unchecked_multi_variable_icon')
        }
        self.variable_icon = {
            'base' : QtGui.QIcon(':/icons/form_variable_icon'),
            'sel_checked' : QtGui.QIcon(':/icons/form_checked_variable_icon'),
            'sel_unchecked' : QtGui.QIcon(':/icons/form_unchecked_variable_icon')
        }
        self.section_icon = {
            'base' : QtGui.QIcon(':/icons/form_section_icon'),
            'sel_checked' : QtGui.QIcon(':/icons/form_checked_section_icon'),
            'sel_unchecked' : QtGui.QIcon(':/icons/form_unchecked_section_icon')
        }
        self.new_section_icon = QtGui.QIcon(':/icons/form_new_section_icon')
        self.next_section_icon = QtGui.QIcon(':/icons/form_next_section_icon')
        self.choices_icon = QtGui.QIcon(':/icons/form_choices_icon')

    def toggle_node_selection(self, node_index):
        if self.selection_mode is None:
            return

        node = self.getItem(node_index)

        # if section selected: select all children
        # if section unselected: unselect all children
        # if item selected: select all children
        # if item unselected: unselect all children and
        #                     unselect parent if all siblings are unselected
        # if var unselected: unselect parent if all siblings are unselected

        new_state = None
        if (self.selection_mode == 'section' and node.node_type == 'section') or\
           node.node_type.startswith('item') or node.node_type == 'variable':
            new_state = Node.NEXT_SEL_STATE[node.state]
            state = self.set_node_selection(new_state, node_index)

        if new_state == 'sel_checked' and self.selection_mode == 'section' and \
           node.node_type.startswith('item') or node.node_type == 'variable':
            self.set_node_selection(new_state, self.parent(node_index),
                                    apply_to_children=False)

        if new_state == 'sel_unchecked' and \
           node.node_type.startswith('item') or node.node_type == 'variable' :
            self.unselect_if_no_selected_child(self.parent(node_index))

    def set_node_selection(self, state, node_index, apply_to_children=True):
        node = self.getItem(node_index)
        if node.state == state:
            return
        node.state = state
        self.dataChanged.emit(node_index, node_index)

        if apply_to_children and node.is_container:
            for irow in range(self.rowCount(node_index)):
                child_index = self.index(irow, 0, parent=node_index)
                child_node = self.getItem(child_index)
                if child_node.node_type == node.child_type:
                    self.set_node_selection(state, child_index,
                                            apply_to_children=apply_to_children)

    def unselect_if_no_selected_child(self, node_index):
        node = self.getItem(node_index)
        nb_children, nb_unchecked_children = 0, 0
        for irow in range(self.rowCount(node_index)):
            child_index = self.index(irow, 0, parent=node_index)
            child_node = self.getItem(child_index)
            if child_node.node_type == node.child_type:
                nb_children += 1
                nb_unchecked_children += (child_node.state == 'sel_unchecked')

        if nb_unchecked_children == nb_children:
            node.state = 'sel_unchecked'
            self.dataChanged.emit(node_index, node_index)

    def new_child(self, parent_index):
        parent_node = self.getItem(parent_index)
        if parent_node.is_container:
            child_def = TreeModel.CHILD_DEF[parent_node.node_type]
            logger.debug('Generate label for new child of %s', parent_node.label)
            label = child_def.gen_label(parent_node, self)
            new_index = self.insert_node(label, child_def.node_types[0],
                                         parent_index,
                                         pdict=child_def.gen_pdict(label),
                                         is_container=child_def.is_container)
            if child_def.node_types[0] == 'section':
                transitions_index = self.insert_node('next section',
                                                     'transition_rules',
                                                     new_index, irow=0,
                                                     is_container=True)
                self.new_child(transitions_index)
            return True
        else:
            return False

    def insert_node(self, label, node_type, parent_index, irow=None,
                    pdict=None, is_container=False, fix_duplicate_label=False):
        """
        ASSUME: given label is valid wrt underlying logic (eg uniqueness)
        """
        parent_node = self.getItem(parent_index)

        if fix_duplicate_label:
           label = make_unique_label(label, self.child_labels(parent_node))

        # Insert node in parent node before button to add new section
        has_add_button = (len(parent_node.childItems) > 0 and
                          parent_node.childItems[-1].node_type == 'add_button')
        default_irow = self.rowCount(parent_index) - int(has_add_button)
        irow = if_none(irow, default_irow)
        logger.debug('Add node %s of type %s to %s at irow=%d', label, node_type,
                     parent_node.label, irow)

        child_type = None
        if is_container:
            child_type = TreeModel.CHILD_DEF[node_type].node_types[0]

        if (self.selection_mode == 'section' and \
            node_type in ['section', 'item', 'variable',
                          'item_single_var', 'item_text']) or\
           (self.selection_mode == 'item' and \
            node_type in ['item', 'variable', 'item_single_var', 'item_text']):
            node_state = 'sel_unchecked'
        else:
            node_state = 'base'

        new_node = Node(label, node_type, is_container=is_container, pdict=pdict,
                        parent=parent_node, child_type=child_type,
                        state=node_state)
        self.beginInsertRows(parent_index, irow, irow)
        parent_node.childItems.insert(irow, new_node)
        self.endInsertRows()

        new_node_index = self.index(irow, 0, parent_index)
        if self.selection_mode is None and is_container:
            # Insert button to add new item
            self.beginInsertRows(new_node_index, 0, 0)
            new_node.childItems.append(Node('+', 'add_button', parent=new_node))
            self.endInsertRows()

        return new_node_index

    def child_labels(self, node):
        return node.child_labels()
        #child_type = TreeModel.CHILD_DEF[node.node_type].node_types[0]
        #return [c.label for c in node.childItems if c.node_type == child_type]

    def all_section_keys(self, section_node):
        all_keys = []
        for child in section_node.childItems:
            if child.node_type in ['item', 'item_single_var']:
                all_keys.extend(self.all_item_keys(child))
        logger.debug('All keys of section %s: %s', section_node.label,
                     all_keys)
        return all_keys

    def all_sibling_keys(self, node):
        if node.node_type == 'variable':
            section_node = node.parent().parent()
        elif node.node_type == 'item_single_var':
            section_node = node.parent()
        return self.all_section_keys(section_node)

    def all_item_keys(self, item_node):
        if item_node.node_type == 'item':
            return self.child_labels(item_node)
        elif item_node.node_type == 'item_single_var':
            return [item_node.label]

    def insert_form(self, form_dict):

        sections_dict = form_dict.pop('sections')
        form_label = form_dict.pop('label')
        form_index = self.insert_node(form_label, 'form', QModelIndex(),
                                      pdict=form_dict, is_container=True)

        # Insert sections
        for section_label, section_dict in sections_dict.items():
            self.insert_section(section_label, section_dict, form_index)

    def insert_section(self, label, section_dict, form_index, irow=None,
                       fix_duplicate_label=True):

        items = section_dict.pop('items')
        transitions_def = section_dict.pop('next_section_definition')

        # Insert section in form node before button to add new section
        section_index = self.insert_node(label, 'section', form_index,
                                         pdict=section_dict, is_container=True,
                                         irow=irow, fix_duplicate_label=True)

        # Insert transitions node as 1st child of section node
        transitions_index = self.insert_node('next section', 'transition_rules',
                                             section_index, irow=0,
                                             is_container=True)
        # Insert Transition rules
        if transitions_def is not None:
            if isinstance(transitions_def, str):
                transitions_def = [('True', transitions_def)]
            for it, transition_def in enumerate(transitions_def):
                self.insert_node('transition rule %d' % it, 'transition_rule',
                                 transitions_index,
                                 pdict={'predicate' : transition_def[0],
                                        'next_section' : transition_def[1]
                                 })

        for item_dict in items:
            self.insert_item(item_dict, section_index)

    def insert_item(self, item_dict, section_index, irow=None,
                    fix_duplicate_label=True):
        """
        IMPORTANT: item_dict can be altered in this function to fix
        duplicate variable names
        """
        section_node = self.getItem(section_index)
        has_add_button = (len(section_node.childItems) > 0 and
                          section_node.childItems[-1].node_type == 'add_button')
        irow = if_none(irow, self.rowCount(section_index) - int(has_add_button))
        if fix_duplicate_label:
            self.make_item_var_names_unique(section_node, item_dict)

        logger.debug('Add item %s to section %s at irow=%d', item_dict['label'],
                     section_node.label, irow)

        item_label = item_dict.pop('label')
        choices = item_dict.pop('choices')

        def _if_empty(l, d):
            if l is None or l == '':
                return d
            return l

        keys = item_dict.pop('keys')
        init_values = item_dict.pop('init_values')

        if keys == 0:
            item_label = _if_empty(item_label, 'Text Only')
            node_type = 'item_text'
            is_container = False
        elif len(keys) == 1:
            item_label = next(iter(keys))
            node_type = 'item_single_var'
            item_dict['key_tr'] = if_none(keys[item_label],
                                          {'English':'', 'French':''})
            if init_values is not None:
                item_dict['init_value'] = init_values[item_label]
            else:
                item_dict['init_value'] = None
            is_container = False
        else: # len(keys) > 1:
            item_label = _if_empty(item_label, 'Variable Group')
            node_type = 'item'
            is_container = True

        item_dict['type_locked'] = False
        for var_name in keys:
            if var_name in self.locked_variable_types:
                item_dict['vtype'] = self.locked_variable_types[var_name]
                item_dict['type_locked'] = True
                break
        item_index = self.insert_node(item_label, node_type, section_index,
                                      pdict=item_dict, is_container=is_container,
                                      irow=irow)

        if node_type != 'item_text':
            if choices is not None and len(choices) > 0:
                choices_index = self.add_choices_node(item_index)

                for choice_label, choice_dict in choices.items():
                    self.insert_node(choice_label, 'choice', choices_index,
                                     pdict=choice_dict)

        if node_type == 'item':
            init_values = if_none(init_values, [None] * len(keys))
            for (key, key_tr), init_value in zip(keys.items(), init_values):
                self.insert_sub_variable(item_index, key, init_value)

    def insert_sub_variable(self, item_index, var_label, var_tr, init_value,
                            irow=None):
        return self.insert_node(var_label, 'variable', item_index,
                                pdict={'key_tr' : var_tr,
                                       'init_value' : init_value},
                                irow=irow)


    def make_item_var_names_unique(self, section_node, item_dict):
        if item_dict['keys'] is None or len(item_dict['keys']) == 0:
            return

        all_keys = self.all_section_keys(section_node)
        given_keys = list(item_dict['keys'])
        for ikey, key in enumerate(given_keys):
            idx = 0
            key_origin = key
            while key in all_keys or (idx>0 and key in given_keys):
                idx += 1
                key = key_origin + '_%d' % idx
            if key != key_origin:
                if len(item_dict['keys']) == 1:
                    item_dict['label'] = key
                for k in ('keys', 'init_values'):
                    item_dict[k][key] = item_dict[k].pop(key_origin)
                given_keys[ikey] = key

    def add_choices_node(self, item_index):
        item_node = self.getItem(item_index)

        for ichild, child in enumerate(item_node.childItems):
            if child.node_type == 'choices':
                return self.index(ichild, 0, item_index)

        choices_index = self.insert_node('choices', 'choices', item_index,
                                         irow=0, is_container=True)

        return choices_index

    def ___insert_choice(self, label, choice_dict, choices_index, irow=None):
        item_index = None

        irow = if_none(irow, self.rowCount(choices_index) - 1)
        # TODO: use this pattern everywhere instead of adding default child
        #       and then changing its data
        self.beginInsertRows(choices_index, irow, irow)
        choices_node.childItems.insert(irow, ChoiceNode(label, choice_dict))
        self.endInsertRows()

    def columnCount(self, parent=QModelIndex()):
        return 1

    def data(self, index, role):
        if not index.isValid():
            return None

        if role != Qt.DisplayRole and role != Qt.EditRole and role != Qt.FontRole\
           and role != QtCore.Qt.DecorationRole:
            return None

        node = self.getItem(index)

        if role == Qt.DisplayRole or role == Qt.EditRole:
            return node.data(0)

        if role == Qt.FontRole and node.node_type in ['variables', 'choices',
                                                      'transition_rules']:
            font = QtGui.QFont()
            font.setItalic(True)
            return font
        elif role == QtCore.Qt.DecorationRole and \
             node.node_type in ['item_single_var', 'variable']:
            return self.variable_icon[node.state]
        elif role == QtCore.Qt.DecorationRole and node.node_type == 'item':
            return self.multi_variable_icon[node.state]
        elif role == QtCore.Qt.DecorationRole and node.node_type == 'item_text':
            return self.text_item_icon[node.state]
        elif role == QtCore.Qt.DecorationRole and node.node_type == 'section':
            if self.selection_mode == 'section':
                return self.section_icon[node.state]
            else:
                return self.section_icon['base']
        elif role == QtCore.Qt.DecorationRole and node.node_type == 'choices':
            return self.choices_icon
        elif role == QtCore.Qt.DecorationRole and \
             node.node_type == 'transition_rules':
            return self.next_section_icon

    def flags(self, index):
        if not index.isValid():
            return Qt.NoItemFlags

        default_flags = super(TreeModel, self).flags(index)

        item = self.getItem(index)
        if self.selection_mode is not None or \
           item.node_type in ['add_button', 'transition_rule',
                              'other_choice']:
            return default_flags
        elif item.node_type in ['choices', 'variables', 'transition_rules']:
            return Qt.ItemIsDropEnabled | default_flags
        elif item.node_type in ['choice', 'variable',
                                'item', 'item_single_var', 'item_text',
                                'section']:
            return Qt.ItemIsDragEnabled | Qt.ItemIsDropEnabled | \
                Qt.ItemIsEditable | default_flags
        else:
            return Qt.ItemIsEditable | default_flags

    def supportedDropActions(self):
        return Qt.MoveAction

    def mimeTypes(self):
        return ["text/json"]

    # QMimeData *DragDropListModel::
    def mimeData(self, indexes):
        mimeData = QtCore.QMimeData()
        encodedData = QtCore.QByteArray()
        stream = QtCore.QDataStream(encodedData, QtCore.QIODevice.WriteOnly)

        for index in indexes:
            if index.isValid():
                node = self.getItem(index)
                stream.writeQString(node.to_json());

        mimeData.setData("text/json", encodedData);
        return mimeData

    def canDropMimeData(self, mime_data, drop_action, irow, icolumn,
                        parent_index):
        # TODO adapt with new node API
        logger.debug2('Can drop on irow %d, icolumn %d, parent %s?',
                      irow, icolumn, self.getItem(parent_index))
        # default canDropMimeData: can drop if data has proper format and
        #                          action is in supportedDropActions
        #                          (here moveAction only)
        # Additional criterions:
        #     - only insertion is supported (irow != -1,
        #        cannot drop onto an existing element)
        #     - item can only be dropped in a section
        #     - section can only be dropped in a form
        #     - cannot drop below the node used as button to add new child
        if self.selection_mode is not None or (icolumn > self.columnCount() - 1):
            logger.debug2('can NOT drop!')
            return False

        if super().canDropMimeData(mime_data, drop_action, irow, icolumn,
                                   parent_index) and \
            irow != -1 and \
            irow < self.rowCount(parent_index) - 1:

            mime_dict, dropped_type, _ = self.unpack_mime_data(mime_data)
            if mime_dict is None:
                return False

            parent_node = self.getItem(parent_index)
            child_def = TreeModel.CHILD_DEF[parent_node.node_type]
            logger.debug2('dropped type: %s, parent_type: %s, '\
                          'child types: %s', dropped_type,
                          parent_node.node_type, child_def.node_types)
            if dropped_type in child_def.node_types:
                logger.debug2('can drop!')
                return True
            else:
                logger.debug2('can NOT drop!')
                return False
        else:
            logger.debug2('can NOT drop!')
            return False

    def unpack_mime_data(self, mime_data):
        stream = QtCore.QDataStream(mime_data.data('text/json'))
        try:
            mime_dict = json.loads(stream.readQString())
            logger.debug2('Dict from mime data:\n%s', pformat(mime_dict))
            parent_label = mime_dict.pop('parent_label', None)
            dropped_type = mime_dict.pop('origin_node_type', None)
            return mime_dict, dropped_type, parent_label
        except Exception as e:
            logger.error('Error while reading mime data:\n%s' % repr(e))
            logger.error(format_exc())
            return None, None, None

    def dropMimeData(self, mime_data, drop_action, irow, icolumn, parent_index):
        parent_node = self.getItem(parent_index)
        logger.debug2('process drop on irow %d, icolumn %d, parent %s (%s)',
                      irow, icolumn, parent_node.label,
                      parent_node.node_type)

        node_dict, dropped_type, parent_label = \
            self.unpack_mime_data(mime_data)
        if node_dict is None:
            return False

        # label = node_dict.pop('label')
        # if parent_label != parent_node.label:
        #     label = parent_node.new_child_label(label=label)


        fix_duplicate_label = (parent_label is not None and
                               parent_label != parent_node.label)
        if dropped_type == 'section':
            section_label = node_dict.pop('label')
            self.insert_section(section_label, node_dict, parent_index, irow,
                                fix_duplicate_label=fix_duplicate_label)
            return True
        elif dropped_type.startswith('item'):
            self.insert_item(node_dict, parent_index, irow,
                             fix_duplicate_label=fix_duplicate_label)
            return True
        elif dropped_type == 'choice':
            label, choice_tr = next(iter(node_dict.items()))
            self.insert_node(label, 'choice', parent_index, irow=irow,
                             pdict=choice_tr,
                             fix_duplicate_label=fix_duplicate_label)
            return True
        elif dropped_type == 'variable':
            label, var_tr = next(iter(node_dict['keys'].items()))
            init_value = node_dict['init_values'][label]
            self.insert_node(label, 'variable', parent_index, irow=irow,
                             pdict={'key_tr' : var_tr, 'init_value' : init_value},
                             fix_duplicate_label=fix_duplicate_label)
            return True

        return False

        # parent_node = self.getItem(parent_index)

        # logger.debug2('Drop data of type %s on row %d, col %d', dropped_type,
        #               irow, icolumn)
        # # logger.debug2('Dict to drop: %s', pformat(node_dict))
        # logger.debug2('Parent node: %s %s', parent_node, parent_node.label)


        # logger.debug2('Label for inserted item: %s', label)
        # if 1:
        #     #persistent_parent_index = QtCore.QPersistentModelIndex(parent_index)
        #     self.layoutAboutToBeChanged.emit()#[persistent_parent_index])
        #     if dropped_type == 'item': # parent_type is section node
        #         new_node = ItemNode(label, node_dict,
        #                             self.locked_variable_types)
        #     elif dropped_type == 'section': # parent_type is section node
        #         new_node = SectionNode(label, node_dict,
        #                                self.locked_variable_types)
        #     parent_node.childItems.insert(irow, new_node)
        #     #self.changePersistentIndexList()
        #     self.layoutChanged.emit() #[persistent_parent_index])
        #     # self.dataChanged.emit(parent_index, parent_index)
        # else:
        #     if dropped_type == 'item': # parent_type is section node
        #         new_node = ItemNode(label, node_dict,
        #                             self.locked_variable_types)
        #     elif dropped_type == 'section': # parent_type is section node
        #         new_node = SectionNode(label, node_dict,
        #                                self.locked_variable_types)

        #     if self.insertRows(irow, 1, parent_index):
        #         inserted_index = self.index(irow, 0, parent_index)
        #         self.setData(inserted_index, label,
        #                      force=parent_label==parent_node.label)
        #         inserted_node = self.getItem(inserted_index)
        #         if dropped_type == 'item':
        #             inserted_node.item_dict = node_dict
        #         elif dropped_type == 'section':
        #             inserted_node.section_dict = node_dict
        #     else:
        #         return False
        #     #parent_node.childItems[irow:irow] =  [new_node]
        #     #self.endInsertRows()
        # return True

    def getItem(self, index):
        if index.isValid():
            item = index.internalPointer()
            if item:
                return item
        return self.root

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return ''
        return None

    def index(self, row, column, parent=QModelIndex()):
        if parent.isValid() and parent.column() != 0:
            return QModelIndex()

        parentItem = self.getItem(parent)
        childItem = parentItem.child(row)
        if childItem is not None:
            return self.createIndex(row, column, childItem)
        else:
            return QModelIndex()

    def ___insertRows(self, position, rows, parent=QModelIndex()):
        parentItem = self.getItem(parent)

        self.beginInsertRows(parent, position, position + rows - 1)
        logger.debug('Add %d row(s) at position %d to %s',
                     rows, position, parentItem.label)
        for i in range(position, rows):
           pass
        success = parentItem.insertChildren(position, rows)
        child_def = TreeModel.CHILD_DEF[parent_node.node_type]
        def make_child(i):
            pass
        parent_node.children[p:p] = [make_child(i) for i in range(rows)]
        self.endInsertRows()
        return success

    def convert_item_to_multi_var(self, item_index):
        """ ASSUME node_type is item_single_var """
        item_node = self.getItem(item_index)
        item_node.node_type = 'item'
        item_node.child_type = 'variable'
        item_node.is_container = True
        key_tr = item_node.pdict.pop('key_tr')
        init_value = item_node.pdict.pop('init_value')

        self.beginInsertRows(item_index, 0, 1)
        item_node.childItems.append(Node(item_node.label, 'variable',
                                         pdict={'key_tr' : key_tr,
                                                'init_value' : init_value},
                                         parent=item_node))
        item_node.childItems.append(Node('+', 'add_button', parent=item_node))
        self.endInsertRows()

        self.dataChanged.emit(item_index, item_index)

    def convert_item_to_text_only(self, item_index):
        item_node = self.getItem(item_index)
        item_node.node_type = 'item_text'
        self.removeRows(0, self.rowCount(item_index), item_index)
        item_node.is_container = False
        item_node.pdict['keys'] = None
        item_node.pdict['init_values'] = None

        self.dataChanged.emit(item_index, item_index)

    def __add_sub_variables(self, item_model_index,
                          keys=None, init_values=None):
        item_node = self.getItem(item_model_index)
        position = 0 + int(item_node.choices_node is not None)
        self.beginInsertRows(item_model_index, position, position)
        print('Add variables_node at position %d to %s' % \
              (position, item_node.label))
        success = item_node.add_variables_node()
        self.endInsertRows()
        return success

    def add_other_choice_node_to_choices_node(self, item_model_index):
        choices_node = self.getItem(item_model_index)
        self.beginInsertRows(item_model_index, 0, 0)
        print('Add other_choice to %s' % choices_node.label)
        success = choices_node.add_other_choice_node()
        self.endInsertRows()
        return success

    def parent(self, index):
        if not index.isValid():
            return QModelIndex()

        childItem = self.getItem(index)
        parentItem = childItem.parent()

        if parentItem is None or parentItem == self.root:
            return QModelIndex()

        return self.createIndex(parentItem.childNumber(), 0, parentItem)

    def removeRows(self, position, rows, parent=QModelIndex()):
        parentItem = self.getItem(parent)

        self.beginRemoveRows(parent, position, position + rows - 1)
        success = parentItem.removeChildren(position, rows)
        self.endRemoveRows()

        return success

    def rowCount(self, parent=QModelIndex()):
        parentItem = self.getItem(parent)
        return parentItem.childCount()

    def check_locked_type(self, label, node):
        locked_type = self.locked_variable_types.get(label, None)
        if locked_type is not None:
            if node.node_type == 'item_single_var':
                node.pdict['type_locked'] = True
                node.pdict['vtype'] = locked_type
            else: # variable
                node.parent().pdict['type_locked'] = True
                node.parent().pdict['vtype'] = locked_type

    def setData(self, index, value, role=Qt.EditRole, force=False):
        if role != Qt.EditRole:
            return False

        node = self.getItem(index)
        if node.node_type in ['item_single_var', 'variable']:
            if value in self.all_sibling_keys(node):
                return False
            self.check_locked_type(value, node)
            locked_type = self.locked_variable_types.get(value, None)

        result = node.setData(index.column(), value)

        if result:
            self.dataChanged.emit(index, index)

        return result

    def setHeaderData(self, section, orientation, value, role=Qt.EditRole):
        if role != Qt.EditRole or orientation != Qt.Horizontal:
            return False

        result = self.root.setData(section, value)
        if result:
            self.headerDataChanged.emit(orientation, section, section)

        return result

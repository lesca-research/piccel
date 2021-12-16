# -*- coding: utf-8 -*-

from datetime import date, datetime, timedelta, time
import logging
import tempfile
import os.path as op
import shutil
import unittest
from collections import OrderedDict, defaultdict
import re
from pprint import pformat, pprint
from uuid import uuid1, uuid4
from time import sleep

import json
import numpy as np
import pandas as pd

from .logging import logger
from .core import UserRole, Notifier, LazyFunc, nexts


from .ui import (form_editor_main_ui, form_edit_ui, section_edit_ui, item_edit_ui,
                 choice_edit_ui, variable_edit_ui, section_transition_edit_ui)
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

    def __init__(self, sections, default_language, supported_languages,
                 title='', label='Form', watchers=None):
        """
        - sections:
          IMPORTANT:
            if no next_section_definition is given, then use the next section
            in order. If section is last then consider that the form can be
            submitted afterwards.
        """
        self.label = label
        self.notifier = Notifier(watchers)

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
        section_names = list(sections.keys())
        for i_section, (section_name, section) in enumerate(sections.items()):
            if section.tr.supported_languages != self.tr.supported_languages:
                raise UnsupportedLanguage('Supported languages for Form %s (s) =!'\
                                          'those of section %s (%s)',
                                          self, self.tr.supported_languages,
                                          section_name,
                                          section.tr.supported_languages)
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
            for section in self.sections.values():
                section.set_language(language)

    def get_dtypes(self):
        return {k:its[0].dtype_pd for k,its in self.key_to_items.items()}

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
                section.add_translations(other_form.sections)
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
        self.key_to_items[key].append(item)
        if vtype == 'date':
            self.date_keys.add(key)
        elif vtype == 'datetime':
            self.datetime_keys.add(key)

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
                label = protect_label(label)

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
        for item_gdict in gform_dict['items']:
            # print('Convert gform item %s' % pformat(item_gdict))
            if item_gdict['type'] == 'PAGE_BREAK':
                slabel, stitle = get_label(item_gdict['title'], section_gen_label)
                section_dict = {'title' : {language: stitle},
                                'default_language' : language,
                                'supported_languages' : {language},
                                'items' : []}
                sections[slabel] = section_dict
            else:
                item_title = item_gdict['title']
                item_choices = None
                other_choice_label = None
                if item_gdict['type'] == 'SECTION_HEADER':
                    item_keys = None
                elif item_gdict['type'] != 'CHECKBOX':
                    key_label, item_title = get_label(item_gdict['title'],
                                                      var_gen_label)
                    item_keys = {key_label : {language : item_title}}
                    if item_gdict['type'] in ['MULTIPLE_CHOICE', 'LIST']:
                        item_choices = {}
                        for c in item_gdict['choices']:
                            clabel, ctitle = get_label(c, protect=False)
                            item_choices[clabel] = {language : ctitle}
                        if item_gdict.get('allow_other_choice', False):
                            other_label = {'English' : 'Other',
                                           'French' : 'Autre'}.get(language,
                                                                   'Other')
                            other_choice_label = {language : other_label}
                else:
                    item_keys = {}
                    for c in item_gdict['choices']:
                        clabel, ctitle = get_label(c)
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

    def has_key(self, key):
        return any(key in item.keys for item in self.items)

    def add_translations(self, other_section):
        self.tr.add_translations(other_section.tr)
        if len(self.items) != len(other_section.item):
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
        return {'title': self.tr.trs['title'],
                'items' : [i.to_dict() for i in self.items],
                'default_language' : self.tr.language,
                'supported_languages' : list(self.tr.supported_languages),
                'next_section_definition' : self.next_section_definition}

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
        return {'keys' : self.keys,
                'label' : self.label,
                'default_language' : self.tr.language,
                'supported_languages' : list(self.tr.supported_languages),
                'vtype' : self.vtype,
                'title' : self.tr.trs.get('title', None),
                'description' : self.tr.trs.get('description', None),
                'regexp' : self.regexp.pattern,
                'regexp_invalid_message' : self.regexp_invalid_message,
                'allow_empty' : self.allow_None,
                'choices' : self.choices,
                'other_choice_label' : self.tr.trs.get('other_choice', None),
                'init_values' : self.init_values,
                'unique' : self.unique,
                'generator' : self.generator,
                'access_level' : self.access_level.name,
                'editable' : self.editable,
                'freeze_on_update' : self.freeze_on_update,
                # TODO: resolve from number_interval:
                'number_interval' : self.number_interval_param,
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

def link_line_edit(line_edit, dest_dict, dest_key):
    try:
        line_edit.editingFinished.disconnect()
    except TypeError:
        pass

    line_edit.setText(dest_dict[dest_key])
    callback = compose(line_edit.text, partial(dest_dict.__setitem__, dest_key))
    line_edit.editingFinished.connect(callback)

def link_text_edit(text_edit, dest_dict, dest_key):
    try:
        text_edit.editingFinished.disconnect()
    except TypeError:
        pass

    text_edit.setPlainText(dest_dict[dest_key])
    callback = compose(text_edit.toPlainText,
                       partial(dest_dict.__setitem__, dest_key))
    text_edit.editingFinished.connect(callback)

def link_combo_box(combox_box, dest_dict, dest_key, choices=None):
    try:
        combox_box.currentTextChanged.disconnect()
    except TypeError:
        pass
    if choices is not None:
        combox_box.clear()
        combox_box.addItems(choices)
    combox_box.setCurrentText(dest_dict[dest_key])
    combox_box.currentTextChanged.connect(partial(dest_dict.__setitem__, dest_key))

def link_check_box(check_box, dest_dict, dest_key):
    try:
        check_box.stateChanged.disconnect()
    except TypeError:
        pass
    check_box.setChecked(dest_dict[dest_key])
    def store_state_to_dict(qstate):
       dest_dict[dest_key] = (qstate == Qt.Checked)
    check_box.stateChanged.connect(store_state_to_dict)

def link_spin_box(spin_box, dest_dict, dest_key):
    try:
        spin_box.valueChanged.disconnect()
    except TypeError:
        pass
    spin_box.setValue(dest_dict[dest_key])
    spin_box.valueChanged.connect(partial(dest_dict.__setitem__, dest_key))

class FormPropertyEditor(QtWidgets.QWidget,
                         form_edit_ui.Ui_FormPropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, form_node):
        for field, language in [(self.title_field_french, 'French'),
                                (self.title_field_english, 'English')]:
            link_line_edit(field, form_node.form_dict['title'], language)

class SectionPropertyEditor(QtWidgets.QWidget,
                            section_edit_ui.Ui_SectionPropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, section_node):
        for field, language in [(self.title_field_french, 'French'),
                                (self.title_field_english, 'English')]:
            link_line_edit(field, section_node.section_dict['title'], language)

class ItemPropertyEditor(QtWidgets.QWidget, item_edit_ui.Ui_ItemPropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, item_node):
        for field, dest_dict, key in [(self.title_field_french,
                                       item_node.item_dict['title'], 'French'),
                                      (self.title_field_english,
                                       item_node.item_dict['title'], 'English'),
                                      (self.regExprLineEdit, item_node.item_dict,
                                       'regexp'),
                                      (self.regExprInvalidHintLineEdit,
                                       item_node.item_dict,
                                       'regexp_invalid_message')]:
            link_line_edit(field, dest_dict, key)

        for field, dest_dict, key in [(self.description_field_french,
                                       item_node.item_dict['description'],
                                       'French'),
                                      (self.description_field_english,
                                       item_node.item_dict['description'],
                                       'English')]:
            link_text_edit(field, dest_dict, key)


        link_combo_box(self.typeComboBox, item_node.item_dict, 'vtype')
        link_check_box(self.uniqueCheckBox, item_node.item_dict, 'unique')
        link_check_box(self.allowEmptyCheckBox, item_node.item_dict, 'allow_empty')
        link_combo_box(self.accessLevelComboBox, item_node.item_dict, 'access_level')
        link_spin_box(self.textNbLinesSpinBox, item_node.item_dict, 'nb_lines')

        if item_node.variables_node() is None:
            self.initialValueLineEdit.show()
            self.initialValueLabel.show()
            try:
                self.initialValueLineEdit.editingFinished.disconnect()
            except TypeError:
                pass
            #TODO: handle format/unformat
            self.initialValueLineEdit.setText(str(item_node.init_value))
            def store_init_value():
                # TODO: handle format/unformat
                item_node.init_value = self.initialValueLineEdit.text()
            self.initialValueLineEdit.editingFinished.connect(store_init_value)
        else:
            self.initialValueLineEdit.hide()
            self.initialValueLabel.hide()

class ChoicePropertyEditor(QtWidgets.QWidget, choice_edit_ui.Ui_ChoicePropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, choice_node):
        for field, language in [(self.choice_field_french, 'French'),
                                (self.choice_field_english, 'English')]:
            link_line_edit(field, choice_node.choice_tr,language)


class VariablePropertyEditor(QtWidgets.QWidget,
                             variable_edit_ui.Ui_VariablePropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, var_node):
        for field, dest_dict, key in [(self.variable_field_french,
                                       var_node.cfg['key_tr'], 'French'),
                                      (self.variable_field_english,
                                       var_node.cfg['key_tr'], 'English'),
                                      (self.initValueLineEdit,
                                       var_node.cfg, 'init_value')]:
            link_line_edit(field, dest_dict, key)

class SectionTransitionPropertyEditor(QtWidgets.QWidget,
                                      section_transition_edit_ui.Ui_SectionTransitionPropertyEditor):
    def __init__(self, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

    def attach(self, transition_node):
        link_line_edit(self.criterionLineEdit, transition_node.cfg, 'predicate')
        next_section_choices = ['__submit__'] + \
                                [s for s in (transition_node.parent().parent()
                                             .parent().section_labels())
                                 if s != transition_node.parent().parent().label]
        link_combo_box(self.nextSectionComboBox, transition_node.cfg, 'next_section',
                       choices=next_section_choices)

def form_save_file(form_dict, form_fn=None):
    if form_fn is None:
        form_fn, _ = (QtWidgets.QFileDialog
                      .getSaveFileName(None, "Save Form", "",
                                       "Piccel Form Files (*.form)"))
    if form_fn is not None and form_fn != '':
        form_json = Form.form_dict(form_dict).to_json()
        with open(form_fn, 'w') as fout:
            fout.write(form_json)

def form_save_as_file(form_dict):
    FormEditor.form_save_file(form_dict, None)

class FormEditorFileIO:
    def __init__(self, form_fn=None):
        self.current_form_fn = form_fn

    def get_form(self):
        if self.current_form_fn is None:
            return self.open_form()
        else:
            return self._load_form(self.current_form_fn)

    def _load_form(self, form_fn):
        with open(form_fn, 'r') as fin:
            return Form.from_json(fin.read())

    def open_form(self, parent_widget=None):
        open_dir = (op.dirname(self.current_form_fn)
                    if self.current_form_fn is not None else '')
        form_fn, _ = (QtWidgets.QFileDialog
                      .getOpenFileName(parent_widget, "Load Form", open_dir,
                                       "Piccel Form Files (*.form)"))

        form = None
        if form_fn is not None and form_fn != '':
            self.current_form_fn = form_fn
            form = self._load_form(self.current_form_fn)
            # TODO: handle error!
        return form

    def save_form(self, form, ask_as=False, parent_widget=None):
        if ask_as:
            form_fn, _ = (QtWidgets.QFileDialog
                          .getSaveFileName(parent_widget, "Save Form",
                                           self.current_form_fn,
                                           "Piccel Form Files (*.form)"))
        else:
            form_fn = self.current_form_fn

        if form_fn is not None and form_fn != '':
            form_json = form.to_json()
            with open(form_fn, 'w') as fout:
                fout.write(form_json)

class FormEditor(QtWidgets.QWidget, form_editor_main_ui.Ui_FormEditor):
    def __init__(self, form_io=None, parent=None):
        super(QtWidgets.QWidget, self).__init__(parent)
        self.setupUi(self)

        self.pending_changes = False
        self.form_io = (form_io if form_io is not None else
                        FormEditorFileIO())

        self.set_form(self.form_io.get_form())

        self.tree_view.setContextMenuPolicy(QtCore.Qt.CustomContextMenu)
        self.tree_view.customContextMenuRequested.connect(self.open_menu)

        self.tree_view.doubleClicked.connect(self.on_view_double_click)
        self.tree_view.clicked.connect(self.on_view_click)

        self.form_property_editor = FormPropertyEditor()
        self.verticalLayout.addWidget(self.form_property_editor)

        self.section_property_editor = SectionPropertyEditor()
        self.verticalLayout.addWidget(self.section_property_editor)

        self.section_transition_property_editor = SectionTransitionPropertyEditor()
        self.verticalLayout.addWidget(self.section_transition_property_editor)

        self.item_property_editor = ItemPropertyEditor()
        self.verticalLayout.addWidget(self.item_property_editor)

        self.choice_property_editor = ChoicePropertyEditor()
        self.verticalLayout.addWidget(self.choice_property_editor)

        self.variable_property_editor = VariablePropertyEditor()
        self.verticalLayout.addWidget(self.variable_property_editor)

        if hasattr(self.form_io, 'open_form'):
            def on_open():
                if self.check_pending_changes():
                    self.set_form(self.form_io.open_form(self))
            self.button_open.clicked.connect(on_open)
        else:
            self.open_button.hide()

        def on_save():
            form_dict = self.model.root.childItems[0].to_dict()
            self.form_io.save_form(Form.from_dict(form_dict), parent_widget=self)
        self.button_save.clicked.connect(on_save)

        def on_preview():
            pass
        self.button_preview.clicked.connect(on_preview)

        self.hide_property_editors()

    def on_change(self):
        self.pending_changes = True

    def check_pending_changes(self):
        if self.pending_changes:
            message_box = QtWidgets.QMessageBox()
            message_box.setIcon(QtWidgets.QMessageBox.Question)
            message_box.setText('There are unsaved modification. Save them?')
            message_box.addButton(QtWidgets.QMessageBox.Discard)
            message_box.addButton(QtWidgets.QMessageBox.Cancel)
            message_box.addButton(QtWidgets.QMessageBox.Save)
            result = message_box.exec_()
            if result == QtWidgets.QMessageBox.Discard:
                return True
            elif result == QtWidgets.QMessageBox.Cancel:
                return False
            elif result == QtWidgets.QMessageBox.Save:
                form_dict = self.model.root.childItems[0].to_dict()
                self.form_io.save_form(Form.from_dict(form_dict), ask_as=True,
                                       parent_widget=self)
                # TODO: if save fail, do not return True...
                return True
        return True

    def set_form(self, form):
        form.set_supported_languages(['French', 'English'])
        self.model = TreeModel(form.to_dict())
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
        print('Clicked: %s' % model_item.label)
        if isinstance(model_item, FormNode):
            self.show_form_editor(model_item)
        elif isinstance(model_item, SectionNode):
            self.show_section_editor(model_item)
        elif isinstance(model_item, ItemNode):
            self.show_item_editor(model_item)
        elif isinstance(model_item, ChoiceNode):
            self.show_choice_editor(model_item)
        elif isinstance(model_item, VarNode):
            self.show_variable_editor(model_item)
        elif isinstance(model_item, SectionTransitionNode):
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
        model_item = self.model.getItem(model_index)
        self.on_change()
        if isinstance(model_item, (AddItemNode, AddSectionNode,
                                   AddSectionTransitionNode, AddChoiceNode,
                                   AddVarNode)):
            self.insert_new_before(model_index)
            # insert_position = model_item.childNumber()-1
            #self.model.insertRows(insert_position, 1, model_index.parent())
            self.tree_view.expand(model_index.parent()) # TODO only expand locally

    def insert_new_before(self, model_index):
        current_item = self.model.getItem(model_index)
        current_row = current_item.childNumber()
        # print('Insert new before %s, at row %d' \
        #       %(current_item.label, current_row))
        self.model.insertRows(current_row, 1, model_index.parent())

    def add_variables_node_to_item_node(self, item_model_index):
        self.model.add_variables_node_to_item_node(item_model_index)
        self.tree_view.expandRecursively(item_model_index)

    def add_choices_node_to_item_node(self, item_model_index):
        self.model.add_choices_node_to_item_node(item_model_index)
        self.tree_view.expandRecursively(item_model_index)

    def closeEvent(self, event):
        pprint(Form.from_dict(self.model.root.childItems[0].to_dict()).to_dict())
        QtWidgets.QApplication.instance().quit()

    def open_menu(self, position):
        # indexes = self.sender().selectedIndexes()
        model_index = self.tree_view.indexAt(position)
        if not model_index.isValid():
            return
        model_item = self.model.getItem(model_index)

        right_click_menu = QtWidgets.QMenu()

        if isinstance(model_item, ItemNode) and model_item.variables_node() is None:
            action = right_click_menu.addAction(self.tr("To group of variables"))
            f = partial(self.add_variables_node_to_item_node, model_index)
            action.triggered.connect(f)

        if isinstance(model_item, ItemNode) and not model_item.choices_node():
            action = right_click_menu.addAction(self.tr("Add choices"))
            f = partial(self.add_choices_node_to_item_node, model_index)
            action.triggered.connect(f)

        if not isinstance(model_item,  (FormNode, SectionTransitionsNode)):
            act_del = right_click_menu.addAction(self.tr("Delete"))
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
    """ A node with no children """
    def __init__(self, label, parent=None):
        self.parentItem = parent
        self.label = label

    def child(self, row):
        return None

    def childCount(self):
        return 0

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

    def insertChildren(self, position, count):
        return False

    def insertColumns(self, position, columns):
        return False

    def parent(self):
        return self.parentItem

    def removeChildren(self, position=0, count=None):
        return False

    def removeColumns(self, position, columns):
        return False

    def setData(self, column, value):
        if column != 0:
            return False

        self.label = value
        return True

    def to_dict(self):
        return {}

class MotherNode(Node):

    def __init__(self, label, parent=None):
        self.parentItem = parent
        self.label = label
        self.childItems = []

    def child(self, row):
        if row < 0 or row >= len(self.childItems):
            return None
        return self.childItems[row]

    def childCount(self):
        return len(self.childItems)

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

class FormNode(MotherNode):
    def __init__(self, form_dict, parent=None):
        super(FormNode, self).__init__(form_dict.pop('label'), parent)
        self.form_dict = form_dict.copy()

        sections = self.form_dict.pop('sections')

        # children are sections
        self.childItems = [SectionNode(section_name, section, parent=self)
                           for section_name, section in sections.items()]
        self.childItems.append(AddSectionNode(self))

    def section_labels(self):
        return [s.label for s in self.childItems[:-1]]

    def section_after(self, section_node):
        i_section = section_node.childNumber()
        return (self.childItems[i_section+1].label if i_section < self.childCount()-1
                else None)

    def insertChildren(self, position, nb_childs):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position] = [self._new_section_node()
                                              for i in range(nb_childs)]

        return True

    def _new_section_node(self):
        i_section = len(self.childItems)
        set_names = set(s.label for s in self.childItems)
        while 'section_%d' % i_section in set_names:
            i_section += 1
        section_name = 'section_%d' % i_section

        new_section_cfg = (FormSection([], self.form_dict['default_language'],
                                       self.form_dict['supported_languages'])
                           .to_dict())
        return SectionNode(section_name, new_section_cfg, parent=self)

    def to_dict(self):
        return {
            **self.form_dict,
            **{'label' : self.label,
               'sections' : {s.label : s.to_dict() for s in self.childItems[:-1]}
            }
        }


class SectionNode(MotherNode):
    def __init__(self, section_name, section_dict, parent=None):
        super(SectionNode, self).__init__(section_name, parent)
        self.section_dict = section_dict
        self.section_name = section_name

        transitions_cfg = self.section_dict.pop('next_section_definition')
        transitions_node = SectionTransitionsNode(transitions_cfg, parent=self)
        self.childItems.append(transitions_node)

        self.childItems.extend(ItemNode(item['label'], item, parent=self) for item in
                               self.section_dict.pop('items'))
        self.childItems.append(AddItemNode(self))

    def insertChildren(self, position, nb_nodes):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position] = [self._new_item()
                                              for i_item in range(nb_nodes)]
        return True

    def all_keys(self):
        set_keys = set()
        for item in self.childItems:
            if not isinstance(item, (AddItemNode, SectionTransitionsNode)):
                set_keys.update(item.all_keys())
        return set_keys

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

        return ItemNode(new_item_dict.pop('label'), new_item_dict, parent=self)

    def to_dict(self):
        return {
            **self.section_dict,
            **self.childItems[0].to_dict(),
            **{'items' : [i.to_dict() for i in self.childItems[1:-1]]}
        }


class SectionTransitionsNode(MotherNode):
    def __init__(self, transitions_cfg, parent=None):
        super(SectionTransitionsNode, self).__init__('next section', parent)
        if isinstance(transitions_cfg, str):
            self.childItems.append(SectionTransitionNode('transition rule 1',
                                                         transitions_cfg, parent=self))
        else:
            self.childItems = [SectionTransitionNode('transition rule %d' % it,
                                                     transition_def, parent=self)
                               for it, transition_def in enumerate(transitions_cfg)]

        self.childItems.append(AddSectionTransitionNode(self))

    def insertChildren(self, position, nb_nodes):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position] = [self._new_transition()
                                              for i_item in range(nb_nodes)]
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

        if isinstance(transition_cfg, str):
            transition_cfg = ('True', transition_cfg)

        # label = ('submit' if transition_cfg[1] == '__submit__'
        #          else 'to %s' % transition_cfg[1])
        super(SectionTransitionNode, self).__init__(label, parent)

        self.cfg = {
            'predicate' : transition_cfg[0],
            'next_section' : transition_cfg[1]
        }

    def transition_rule(self):
        return (self.cfg['predicate'], self.cfg['next_section'])

class ItemNode(MotherNode):
    def __init__(self, label, item_dict, parent=None):
        if len(item_dict['keys']) == 1:
            label = next(iter(item_dict['keys']))
        elif label == '':
            label = 'Variable Group'
        super(ItemNode, self).__init__(label, parent)
        self.item_dict = item_dict

        if item_dict['choices'] is not None:
            choices_node = ChoicesNode(item_dict.pop('choices'), parent=self)
            self.childItems.append(choices_node)

        if not len(item_dict['keys']) <= 1:
            variables_node = VariablesNode(item_dict['keys'],
                                           item_dict['init_values'],
                                           parent=self)
            self.childItems.append(variables_node)
        else:
            self.key_tr = item_dict['keys'][self.label]
            init_values = item_dict.pop('init_values')
            self.init_value = (init_values[self.label]
                               if init_values is not None else None)
        item_dict.pop('keys')

    def add_variables_node(self):
        if self.variables_node() is None:
            variables_node = VariablesNode({self.label : self.key_tr},
                                           self.init_value, parent=self)
            self.childItems.append(variables_node)
            return True
        return False

    def variables_node(self):
        for child in self.childItems:
            if isinstance(child, VariablesNode):
                return child
        return None

    def choices_node(self):
        for child in self.childItems:
            if isinstance(child, ChoicesNode):
                return child
        return None

    def to_dict(self):
        var_dict = {'keys' : {}, 'init_values' : None}
        variables_node = self.variables_node()
        if variables_node is None:
            var_dict['keys'][self.label] = self.key_tr
            if self.init_value is not None:
                var_dict['init_values'] = {self.label : self.init_value}
        else:
            var_dict = variables_node.to_dict()

        choices_node = self.choices_node()
        return {
            **self.item_dict,
            **var_dict,
            **{'choices' : (choices_node.to_dict()
                            if choices_node is not None else None)}
        }

    def add_choices_node(self):
        if self.choices_node() is None:
            choices_node = ChoicesNode({'choice_value1' :
                                        {'French': 'Choix 1',
                                         'English' : 'Choice 1'}}, parent=self)
            self.childItems.insert(0, choices_node)
            return True
        return False

    def all_keys(self):
        variables_node = self.variables_node()
        if variables_node is None:
            return {self.label}
        else:
            return variables_node.all_keys()

    def new_var_name(self):
        used_keys = self.parent().all_keys()
        label_pat = 'Var_%d'
        label_idx = len(used_keys)
        while  label_pat % label_idx in used_keys:
            label_idx += 1

        return label_pat % label_idx


class ChoicesNode(MotherNode):
    def __init__(self, choices, parent=None):
        super(ChoicesNode, self).__init__('choices', parent)
        for choice_value, choice_tr in choices.items():
            self.childItems.append(ChoiceNode(choice_value, choice_tr,
                                              parent=self))
        self.childItems.append(AddChoiceNode(self))

    def to_dict(self):
        return {child.label : child.choice_tr for child in self.childItems[:-1]}

    def insertChildren(self, position, nb_childs):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position] = [self._new_choice_node()
                                              for i in range(nb_childs)]

        return True

    def _new_choice_node(self):
        i_choice = len(self.childItems) - 1
        used_choices = set(child.label for child in self.childItems)
        while 'choice_%d' % i_choice in used_choices:
            i_choice += 1
        choice = 'choice_%d' % i_choice

        return ChoiceNode(choice, {'French': 'Choix %d' % i_choice,
                                   'English' : 'Choice %d' % i_choice},
                          parent=self)

class VariablesNode(MotherNode):
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

    def insertChildren(self, position, nb_childs):
        if position < 0 or position > len(self.childItems):
            return False

        self.childItems[position:position] = [self._new_var_node()
                                              for i in range(nb_childs)]

        return True

    def _new_var_node(self):
        used_keys = self.parent().parent().all_keys()
        i_var = len(self.childItems) - 1
        while 'Var_%d' % i_var in used_keys:
            i_var += 1
        var_name = 'Var_%d' % i_var

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

class ChoiceNode(Node):
    def __init__(self, label, choice_tr, parent=None):
        super(ChoiceNode, self).__init__(label, parent)
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

class TreeModel(QAbstractItemModel):
    def __init__(self, form_dict, parent=None):
        super(TreeModel, self).__init__(parent)

        self.root = MotherNode('')
        self.root.childItems.append(FormNode(form_dict, parent=self.root))

    def columnCount(self, parent=QModelIndex()):
        return 1

    def data(self, index, role):
        if not index.isValid():
            return None

        if role != Qt.DisplayRole and role != Qt.EditRole and role != Qt.FontRole:
            return None


        item = self.getItem(index)

        if role == Qt.FontRole and isinstance(item, (VariablesNode, ChoicesNode,
                                                     SectionTransitionsNode)):
            font = QtGui.QFont()
            font.setItalic(True)
            return font
        else:
            return item.data(0)

    def flags(self, index):
        if not index.isValid():
            return 0

        item = self.getItem(index)
        if isinstance(item, (AddItemNode, AddSectionNode, AddChoiceNode,
                             AddVarNode, AddSectionTransitionNode,
                             ChoicesNode, VariablesNode, SectionTransitionsNode,
                             SectionTransitionNode)):
            return super(TreeModel, self).flags(index)
        else:
            return Qt.ItemIsEditable | super(TreeModel, self).flags(index)

    def getItem(self, index):
        if index.isValid():
            item = index.internalPointer()
            if item:
                return item

        return self.root

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return '' # self.root.data(section)

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

    def insertRows(self, position, rows, parent=QModelIndex()):
        parentItem = self.getItem(parent)

        self.beginInsertRows(parent, position, position + rows - 1)
        print('Add %d row(s) at position %d to %s' % \
              (rows, position, parentItem.label))
        success = parentItem.insertChildren(position, rows)
        self.endInsertRows()
        return success

    def add_variables_node_to_item_node(self, item_model_index):
        item_node = self.getItem(item_model_index)
        position = 0 + int(item_node.choices_node is not None)
        self.beginInsertRows(item_model_index, position, position)
        print('Add variables_node at position %d to %s' % \
              (position, item_node.label))
        success = item_node.add_variables_node()
        self.endInsertRows()
        return success

    def add_choices_node_to_item_node(self, item_model_index):
        item_node = self.getItem(item_model_index)
        self.beginInsertRows(item_model_index, 0, 0)
        print('Add choices_node to %s' % item_node.label)
        success = item_node.add_choices_node()
        self.endInsertRows()
        return success

    def parent(self, index):
        if not index.isValid():
            return QModelIndex()

        childItem = self.getItem(index)
        parentItem = childItem.parent()

        if parentItem == self.root:
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

    def setData(self, index, value, role=Qt.EditRole):
        if role != Qt.EditRole:
            return False

        item = self.getItem(index)
        result = item.setData(index.column(), value)

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

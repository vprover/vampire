
/*
 * File XML.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file XML.hpp
 * Defines very simple XML-related functions for a very simple subset of XML.
 *
 * @since 28/11/2003 Manchester
 * @since 03/12/2003, Manchester, allocation changed to use Allocator
 * @since 13/09/2005 Redmond, all classes reimplemented using reference
 *                   counting; memory management made indepedent of
 *                   Allocator since XML is used in many low-level procedures
 */

#ifndef __XML__
#define __XML__

#include <iostream>

#include "VString.hpp"

using namespace std;

namespace Lib {

/**
 * Class for representing (lists of) XML attributes.
 */
class XMLAttribute {
public:
  /** Attribute type */
  enum Type {
    TEXT = 0u,
    LONG = 1u,
    INTEGER = 2u,
    DOUBLE = 3u,
    UNSIGNED = 4u
  };

  class Data;

  /** dummy (uninitialised) attribute */
  XMLAttribute() : _data(0) {}
  XMLAttribute(const XMLAttribute& attr);
  XMLAttribute(const vstring& name,const vstring& value);
  XMLAttribute(const vstring& name,int value);
  XMLAttribute(const vstring& name,long value);
  XMLAttribute(const vstring& name,double value);
  XMLAttribute(const vstring& name,unsigned value);
  ~XMLAttribute();
  void operator= (const XMLAttribute& rhs);
  void setNext(const XMLAttribute&);
  void find(const vstring& name,XMLAttribute&) const;
  /** true if the attribute is not initialised */
  bool isNull() const { return _data == 0; }
  const vstring& name() const;

  // structure
  Type tag () const;
  bool operator == (const XMLAttribute& rhs) const;
  bool operator != (const XMLAttribute& rhs) const;

  // declared but not defined, to prevent on-heap allocation
  void* operator new(size_t);

  // miscellaneous
  void writeList(ostream&) const;

  /** XML classes could not work without lots of friends or redirections
   * before I have added this */
  Data* data() const { return _data; }
 private:
  // structure
  Data* _data;
}; // class XMLAttribute


/**
 * Class for representing XML elements.
 */
class XMLElement {
public:
  /** Element type */
  enum Type {
    /** element containing other elements */
    DEEP = 0u,
    /** empty element */
    EMPTY = 1u,
    /** element containing a string */
    TEXT = 2u,
    /** element containing an integer */
    INTEGER = 3u,
    /** element containing a floating point number */
    FLOAT = 4u,
    /** element containing a long integer */
    LONG = 5u,
    /** element containing a double number */
    DOUBLE = 6u
  };

  class Data;
  class ChildIterator;

  /** dummy (uninitialised) element */
  XMLElement() : _data(0) {}
  /** true if the element is not initialised */
  bool isNull() const { return _data == 0; }
  XMLElement(const vstring& name);  // deep element
  XMLElement(const vstring& name,bool dummy);  // empty element
  XMLElement(const vstring& name,const vstring& text);  // text element
  XMLElement(const vstring& name,int content);         // integer element
  XMLElement(const vstring& name,long content);        // long element
  XMLElement(const vstring& name,float content);       // floating point element
  XMLElement(const vstring& name,double content);
  XMLElement(const XMLElement& elem);
  ~XMLElement();
  void operator= (const XMLElement& rhs);

  void addAttribute(const vstring& name,const vstring& value);
  void addAttribute(const vstring& name,int value);
  void addAttribute(const vstring& name,unsigned value);
  void addAttribute(const vstring& name,long value);
  void addAttribute(const vstring& name,double value);
  void addChild(const XMLElement& element);
  const vstring& name() const;
  const vstring* findStringValue(const vstring& name) const;
  void write(ostream&) const;
  void write(ostream&,int indent) const;
  void append(const vstring& file); 
  void copyAttributes(const XMLElement&);

  // structure
  Type tag() const;
  const vstring& text() const;
  bool operator == (const XMLElement& rhs) const;
  bool operator != (const XMLElement& rhs) const;

  // declared but not defined, to prevent on-heap allocation
  void* operator new(size_t);

  static void writeString(ostream& str,const vstring& s);

  /** XML classes could not work without lots of friends or redirections
   * before I have added this */
  Data* data() const { return _data; }

  void checkDeep() const;
  void checkEmpty() const;
  void checkText() const;
  bool isEmpty() const;

  XMLElement firstChild() const;
 private:
  // structure
  Data* _data;
}; // class XMLElement


class XMLElement::ChildIterator {
public:
  explicit ChildIterator(const XMLElement&);
  bool hasNext() const;
  XMLElement next();
private:
  XMLElement _next;
};


} // namespace Lib

#endif

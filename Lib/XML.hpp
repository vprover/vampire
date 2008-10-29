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

#include <string>
#include <iostream>

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
  XMLAttribute(const string& name,const string& value);
  XMLAttribute(const string& name,int value);
  XMLAttribute(const string& name,long value);
  XMLAttribute(const string& name,double value);
  XMLAttribute(const string& name,unsigned value);
  ~XMLAttribute();
  void operator= (const XMLAttribute& rhs);
  void setNext(const XMLAttribute&);
  void find(const string& name,XMLAttribute&) const;
  /** true if the attribute is not initialised */
  bool isNull() const { return _data == 0; }
  const string& name() const;

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
  XMLElement(const string& name);  // deep element
  XMLElement(const string& name,bool dummy);  // empty element
  XMLElement(const string& name,const string& text);  // text element
  XMLElement(const string& name,int content);         // integer element
  XMLElement(const string& name,long content);        // long element
  XMLElement(const string& name,float content);       // floating point element
  XMLElement(const string& name,double content);
  XMLElement(const XMLElement& elem);
  ~XMLElement();
  void operator= (const XMLElement& rhs);

  void addAttribute(const string& name,const string& value);
  void addAttribute(const string& name,int value);
  void addAttribute(const string& name,unsigned value);
  void addAttribute(const string& name,long value);
  void addAttribute(const string& name,double value);
  void addChild(const XMLElement& element);
  const string& name() const;
  const string* findStringValue(const string& name) const;
  void write(ostream&) const;
  void write(ostream&,int indent) const;
  void append(const string& file); 
  void copyAttributes(const XMLElement&);

  // structure
  Type tag() const;
  const string& text() const;
  bool operator == (const XMLElement& rhs) const;
  bool operator != (const XMLElement& rhs) const;

  // declared but not defined, to prevent on-heap allocation
  void* operator new(size_t);

  static void writeString(ostream& str,const string& s);

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

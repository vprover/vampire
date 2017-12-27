
/*
 * File XML.cpp.
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
// /**
//  * @file XML.cpp
//  * Implements very simple XML-related functions for a very simple
//  * subset of XML.
//  */

// #include <fstream>

// #include "Debug/Assertion.hpp"
// #include "Debug/Tracer.hpp"

// #include "Allocator.hpp"
// #include "XML.hpp"
// #include "Exception.hpp"

// namespace Lib {

// class XMLAttribute::Data
// {
// public:
//   Data(const vstring& name);
//   virtual ~Data() {}
//   virtual Type kind() = 0;

//   inline void ref() { counter++; }
//   void deref();
//   void writeList(ostream&) const;
//   const XMLAttribute* find(const vstring& name) const;
//   vstring name;
//   int counter;
//   XMLAttribute next;

//   virtual void writeValue(ostream&) const = 0;
// }; // class XMLAttribute::Data


// /**
//  * Class for representing string-valued attributes.
//  */
// class TextXMLAttribute :
//   public XMLAttribute::Data
// {
// public:
//   TextXMLAttribute(const vstring& name, const vstring& value);
//   ~TextXMLAttribute() {}
//   XMLAttribute::Type kind() { return XMLAttribute::TEXT; }
//   void writeValue (ostream&) const;
//   vstring value;

//   CLASS_NAME(XML::TextXMLAttribute);
//   USE_ALLOCATOR(TextXMLAttribute);
// }; // class TextXMLAttribute

// /**
//  * Class for representing long-valued attributes.
//  */
// class LongXMLAttribute :
//   public XMLAttribute::Data
// {
// public:
//   LongXMLAttribute(const vstring& name, long value);
//   ~LongXMLAttribute() {}
//   XMLAttribute::Type kind() { return XMLAttribute::LONG; }
//   void writeValue (ostream&) const;
//   long value;

//   CLASS_NAME(XML::LongXMLAttribute);
//   USE_ALLOCATOR(LongXMLAttribute);
// }; // class LongXMLAttribute

// /**
//  * Class for representing double-valued attributes.
//  */
// class DoubleXMLAttribute :
//   public XMLAttribute::Data
// {
// public:
//   DoubleXMLAttribute(const vstring& name, double value);
//   ~DoubleXMLAttribute() {}
//   XMLAttribute::Type kind() { return XMLAttribute::DOUBLE; }
//   void writeValue (ostream&) const;
//   double value;

//   CLASS_NAME(XML::DoubleXMLAttribute);
//   USE_ALLOCATOR(DoubleXMLAttribute);
// }; // class DoubleXMLAttribute

// /**
//  * Class for representing unsigned-valued attributes.
//  */
// class UnsignedXMLAttribute :
//   public XMLAttribute::Data
// {
// public:
//   UnsignedXMLAttribute(const vstring& name, unsigned value);
//   ~UnsignedXMLAttribute() {}
//   XMLAttribute::Type kind() { return XMLAttribute::UNSIGNED; }
//   void writeValue (ostream&) const;
//   unsigned value;

//   CLASS_NAME(XML::UnsignedXMLAttribute);
//   USE_ALLOCATOR(UnsignedXMLAttribute);
// }; // class UnsignedXMLAttribute

// /**
//  * Class for representing integer-valued attributes.
//  */
// class IntegerXMLAttribute :
//   public XMLAttribute::Data
// {
// public:
//   IntegerXMLAttribute(const vstring& name, int value);
//   ~IntegerXMLAttribute() {}
//   XMLAttribute::Type kind() { return XMLAttribute::INTEGER; }
//   void writeValue (ostream&) const;
//   int value;

//   CLASS_NAME(XML::IntegerXMLAttribute);
//   USE_ALLOCATOR(IntegerXMLAttribute);
// }; // class IntegerXMLAttribute

// class XMLElement::Data
// {
// public:
//   Data(const vstring& name);
//   virtual ~Data() {}
//   virtual Type kind() = 0;

//   inline void ref() { counter++; }
//   void deref();
//   void addAttribute(const XMLAttribute&);
//   virtual void write(ostream&,int indent) const;

//   vstring name;
//   int counter;
//   XMLAttribute firstXMLAttribute;
//   XMLAttribute lastXMLAttribute;
//   XMLElement next;

//   static void writeSpaces(ostream& str,int n);
//   /** 
//    * Writes end of header, needed to write empty elements correctly. 
//    * For non-empty elements does nothing.
//    */
//   virtual void writeEndOfHeader(ostream& str) const {}
//   /** For empty element writing content makes nothing */
//   virtual void writeContent (ostream&,int indent) const = 0;
//   virtual void writeFooter(ostream& str) const;
// }; // class XMLElement::Data


// class EmptyXMLElement
//   : public XMLElement::Data
// {
// public:
//   EmptyXMLElement(const vstring& name) : XMLElement::Data(name) {}
//   ~EmptyXMLElement() {}
//   virtual XMLElement::Type kind() { return XMLElement::EMPTY; }
//   void writeEndOfHeader(ostream& str) const;
//   void writeContent (ostream&,int indent) const {}
//   void writeFooter(ostream& str) const {}

//   CLASS_NAME(XML::EmptyXMLElement);
//   USE_ALLOCATOR(EmptyXMLElement);
// }; // EmptyXMLElement


// /**
//  * Class XML::TextXMLElement for handling text-only XML elements.
//  */
// class TextXMLElement
//   : public XMLElement::Data
// {
// public: 
//   TextXMLElement(const vstring& name, const vstring& text);
//   ~TextXMLElement() {}
//   vstring text;
//   virtual XMLElement::Type kind() { return XMLElement::TEXT; }
//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::TextXMLElement);
//   USE_ALLOCATOR(TextXMLElement);
// }; // class TextXMLElement


// /**
//  * Class XML::DeepXMLElement for handling XML elements containing sub-elements.
//  */
// class DeepXMLElement
//   : public XMLElement::Data
// {
// public: 
//   explicit DeepXMLElement (const vstring& name);
//   void addChild(const XMLElement& subelement);
//   ~DeepXMLElement () {}
//   XMLElement firstChild;
//   XMLElement lastChild;
//   virtual XMLElement::Type kind() { return XMLElement::DEEP; }

//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::DeepXMLElement);
//   USE_ALLOCATOR(DeepXMLElement);
// }; // class DeepXMLElement

// /**
//  * Class XML::IntegerXMLElement for handling integer XML elements.
//  */
// class IntegerXMLElement
//   : public XMLElement::Data
// {
// public: 
//   IntegerXMLElement(const vstring& name, int value);
//   ~IntegerXMLElement() {}
//   int value;
//   virtual XMLElement::Type kind() { return XMLElement::INTEGER; }

//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::IntegerXMLElement);
//   USE_ALLOCATOR(IntegerXMLElement);
// }; // class IntegerXMLElement

// /**
//  * Class XML::LongXMLElement for handling long integer XML elements.
//  */
// class LongXMLElement
//   : public XMLElement::Data
// {
// public: 
//   LongXMLElement(const vstring& name, long value);
//   ~LongXMLElement() {}
//   long value;
//   virtual XMLElement::Type kind() { return XMLElement::LONG; }

//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::LongXMLElement);
//   USE_ALLOCATOR(LongXMLElement);
// }; // class LongXMLElement

// /**
//  * Class FloatXMLElement for handling floating point XML elements.
//  */
// class FloatXMLElement
//   : public XMLElement::Data
// {
// public: 
//   FloatXMLElement(const vstring& name, float value);
//   ~FloatXMLElement() {}
//   float value;
//   virtual XMLElement::Type kind() { return XMLElement::FLOAT; }

//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::FloatXMLElement);
//   USE_ALLOCATOR(FloatXMLElement);
// }; // class FloatXMLElement


// /**
//  * Class DoubleXMLElement for handling doubleing point XML elements.
//  */
// class DoubleXMLElement
//   : public XMLElement::Data
// {
// public: 
//   DoubleXMLElement(const vstring& name, double value);
//   ~DoubleXMLElement() {}
//   double value;
//   virtual XMLElement::Type kind() { return XMLElement::DOUBLE; }

//   void writeContent (ostream&,int indent) const;

//   CLASS_NAME(XML::DoubleXMLElement);
//   USE_ALLOCATOR(DoubleXMLElement);
// }; // class DoubleXMLElement


// XMLElement::Data::Data (const vstring& nm)
//   : name(nm),
//     counter(1)
// {
// } // XMLElement::Data::Data


// XMLAttribute::Data::Data (const vstring& nm)
//   : name(nm),
//     counter(1)
// {
// } // XMLAttribute::Data::Data


// void XMLAttribute::Data::deref () 
// { 
//   CALL("XMLAttribute::Data::deref");

//   ASS (this);
//   ASS (counter > 0);
//   counter--;

//   if (counter == 0) {
//     delete this;
//   }
// } // XMLAttribute::Data::deref ()


// XMLAttribute::~XMLAttribute () 
// {
//   CALL("XMLAttribute::~XMLAttribute");

//   if (_data) {
//     _data->deref ();
//   }
// } // XMLAttribute::~XMLAttribute


// void XMLElement::Data::deref () 
// { 
//   CALL("XMLElement::Data::deref");
//   ASS (this);
//   ASS (counter > 0);

//   counter--;

//   if (counter == 0) {
//     delete this;
//   }
// } // XMLElement::Data::deref ()


// XMLElement::~XMLElement () 
// {
//   CALL("XMLElement::~XMLElement");

//   if (_data) {
//     _data->deref ();
//   }
// } // XMLElement::~XMLElement


// /** 
//  * Copy constructor.
//  */
// XMLElement::XMLElement (const XMLElement& t)
//   :
//   _data (t._data)
// {
//   CALL("XMLElement::XMLElement (const XMLElement& t)");

//   if (_data) {
//     _data->ref ();
//   }
// } // XMLElement::XMLElement


// /** 
//  * Copy constructor.
//  */
// XMLAttribute::XMLAttribute (const XMLAttribute& t)
//   :
//   _data (t._data)
// {
//   CALL("XMLAttribute::XMLAttribute (const XMLAttribute& t)");

//   if (_data) {
//     _data->ref ();
//   }
// } // XMLAttribute::XMLAttribute


// XMLAttribute::XMLAttribute (const vstring& name, const vstring& value)
//   : _data(new TextXMLAttribute(name,value))
// {
//   CALL("XMLAttribute::XMLAttribute (const vstring& name, const vstring& value)");
// } // XMLAttribute::XMLAttribute(const vstring& name, const vstring& value)


// XMLAttribute::XMLAttribute (const vstring& name, long value)
//   : _data(new LongXMLAttribute(name,value))
// {
//   CALL("XMLAttribute::XMLAttribute (const vstring& name, long value)");
// } // XMLAttribute::XMLAttribute(const vstring& name, long value)


// XMLAttribute::XMLAttribute (const vstring& name, double value)
//   : _data(new DoubleXMLAttribute(name,value))
// {
//   CALL("XMLAttribute::XMLAttribute (const vstring& name, double value)");
// } // XMLAttribute::XMLAttribute(const vstring& name, double value)


// XMLAttribute::XMLAttribute (const vstring& name, unsigned value)
//   : _data(new UnsignedXMLAttribute(name,value))
// {
//   CALL("XMLAttribute::XMLAttribute (const vstring& name, unsigned value)");
// } // XMLAttribute::XMLAttribute(const vstring& name, unsigned value)

// XMLAttribute::XMLAttribute (const vstring& name, int value)
//   : _data(new IntegerXMLAttribute(name,value))
// {
//   CALL("XMLAttribute::XMLAttribute (const vstring& name, int value)");
// } // XMLAttribute::XMLAttribute(const vstring& name, int value)


// XMLElement::XMLElement (const vstring& name, const vstring& value)
//   : _data(new TextXMLElement(name,value))
// {
//   CALL("XMLElement::XMLElement (const vstring& name, const vstring& value)");
// } // XMLElement::XMLElement(const vstring& name, const vstring& value)


// XMLElement::XMLElement (const vstring& name, int value)
//   : _data(new IntegerXMLElement(name,value))
// {
//   CALL("XMLElement::XMLElement (const vstring& name, int value)");
// } // XMLElement::XMLElement(const vstring& name, int value)


// XMLElement::XMLElement (const vstring& name, long value)
//   : _data(new LongXMLElement(name,value))
// {
//   CALL("XMLElement::XMLElement (const vstring& name, long value)");
// } // XMLElement::XMLElement(const vstring& name, long value)


// XMLElement::XMLElement (const vstring& name, float value)
//   : _data(new FloatXMLElement(name,value))
// {
//   CALL("XMLElement::XMLElement (const vstring& name, float value)");
// } // XMLElement::XMLElement(const vstring& name, float value)


// XMLElement::XMLElement (const vstring& name, double value)
//   : _data(new DoubleXMLElement(name,value))
// {
//   CALL("XMLElement::XMLElement (const vstring& name, double value)");
// } // XMLElement::XMLElement(const vstring& name, double value)


// XMLElement::XMLElement (const vstring& name)
//   : _data(new DeepXMLElement(name))
// {
//   CALL("XMLElement::XMLElement (const vstring& name)");
// } // XMLElement::XMLElement(const vstring& name)

// /**
//  * Assignment operator.
//  * @since 25/08/2002 Torrevieja
//  */
// void XMLElement::operator= (const XMLElement& t)
// {
//   CALL("XMLElement::operator=");

//   if (t._data) {
//     t._data->ref();
//   }

//   if (_data) {
//     _data->deref ();
//   }

//   _data = t._data;
// } // XMLElement::operator=


// /**
//  * Assignment operator.
//  * @since 25/08/2002 Torrevieja
//  */
// void XMLAttribute::operator = (const XMLAttribute& t)
// {
//   CALL("XMLAttribute::operator =");

//   if (t._data) {
//     t._data->ref();
//   }

//   if (_data) {
//     _data->deref ();
//   }

//   _data = t._data;
// } // XMLAttribute::operator=


// /**
//  * Empty element constructor
//  * @since 14/09/2005 Redmond
//  */
// XMLElement::XMLElement (const vstring& name,bool dummy)
//   : _data(new EmptyXMLElement(name))
// {
//   CALL("XMLElement::XMLElement (const vstring& name,bool dummy)");
// } // XMLElement::XMLElement


// void XMLElement::addAttribute (const vstring& name,const vstring& value)
// {
//   CALL("XMLElement::addAttribute (const vstring& name,const vstring& value)");
//   ASS(_data);

//   XMLAttribute attr(name,value);
//   _data->addAttribute(attr);
// } // XMLElement::addAttribute (const vstring& name,const vstring& value)


// void XMLElement::addAttribute (const vstring& name,int value)
// {
//   CALL("XMLElement::addAttribute (const vstring& name,int value)");
//   ASS(_data);

//   XMLAttribute attr(name,value);
//   _data->addAttribute(attr);
// } // XMLElement::addAttribute (const vstring& name,long value)


// void XMLElement::addAttribute (const vstring& name,unsigned value)
// {
//   CALL("XMLElement::addAttribute (const vstring& name,unsigned value)");
//   ASS(_data);

//   XMLAttribute attr(name,value);
//   _data->addAttribute(attr);
// } // XMLElement::addAttribute (const vstring& name,unsigned value)


// void XMLElement::addAttribute (const vstring& name,long value)
// {
//   CALL("XMLElement::addAttribute (const vstring& name,long value)");
//   ASS(_data);

//   XMLAttribute attr(name,value);
//   _data->addAttribute(attr);
// } // XMLElement::addAttribute (const vstring& name,long value)


// void XMLElement::addAttribute (const vstring& name,double value)
// {
//   CALL("XMLElement::addAttribute (const vstring& name,int value)");
//   ASS(_data);

//   XMLAttribute attr(name,value);
//   _data->addAttribute(attr);
// } // XMLElement::addAttribute (const vstring& name,double value)


// /**
//  * Return a pointer to the value of an attribute given its
//  * name (0 if an attribute with such a name does not exist).
//  * The atribute must be an XML::TextXMLAttribute.
//  * @since 11/09/2005 Redmond, copied from Bag::find
//  */
// const vstring* XMLElement::findStringValue (const vstring& name) const
// {
//   CALL("XMLElement::findStringValue (const vstring& name) const");
//   ASS(_data);
//   XMLAttribute attr;
//   _data->firstXMLAttribute.find(name,attr);
//   if (attr.isNull()) {
//     return 0;
//   }
//   if (attr.data()->kind() != XMLAttribute::TEXT) {
//     XML_ERROR("string value expected in attribute " + name,*this);
//   }
//   return &static_cast<TextXMLAttribute*>(attr.data())->value;
// } // XMLElement::findStringValue


// const vstring& XMLAttribute::name () const
// {
//   CALL("XMLAttribute::name");
//   ASS(_data);
//   return _data->name;
// } // XMLAttribute::name


// const vstring& XMLElement::name () const
// {
//   CALL("XMLElement::name");
//   ASS(_data);
//   return _data->name;
// } // XMLElement::name


// /**
//  * Create an iterator over children of an element.
//  */
// XMLElement::ChildIterator::ChildIterator (const XMLElement& e)
// {
//   CALL("XMLElement::ChildIterator::ChildIterator");
//   ASS(e._data);
//   ASS(e._data->kind() == DEEP);

//   _next = static_cast<DeepXMLElement*>(e._data)->firstChild;
// } // XMLElement::ChildIterator::ChildIterator

// bool XMLElement::ChildIterator::hasNext () const
// {
//   CALL("XMLElement::ChildIterator::hasNext");
//   return ! _next.isNull();
// } // XMLElement::ChildIterator::hasNext


// XMLElement XMLElement::ChildIterator::next ()
// {
//   CALL("XMLElement::ChildIterator::next");
//   XMLElement result (_next);
//   _next = _next._data->next;
//   return result;
// } // XMLElement::ChildIterator::next


// const vstring& XMLElement::text () const
// {
//   CALL("XMLElement::text");
//   ASS(_data);
//   ASS(_data->kind() == TEXT);

//   return static_cast<const TextXMLElement*>(_data)->text;
// } // XMLElement::text()

// /**
//  * Copy attributes from an XMLElement.
//  * @since 15/09/2005 Redmond
//  */
// void XMLElement::copyAttributes (const XMLElement& from)
// {
//   CALL("XMLElement::copyAttributes");
//   ASS(_data);
//   ASS(from._data);

//   _data->firstXMLAttribute = from._data->firstXMLAttribute;
//   _data->lastXMLAttribute = from._data->lastXMLAttribute;
// } // XMLElement::copyAttributes


// void DeepXMLElement::addChild (const XMLElement& subelement)
// {
//   CALL("DeepXMLElement::addChild");
//   if (lastChild.isNull()) {
//     firstChild = subelement;
//     lastChild = subelement;
//     return;
//   }
//   lastChild.data()->next = subelement;
//   lastChild = subelement;
// } // DeepXMLElement::addChild

// // /**
// //  * Create a new attribute.
// //  */
// // XMLAttribute::XMLAttribute (Type type, const vstring& name)
// //   : _type (type),
// //     _name (name),
// //     _next (0),
// //     _previous (0)
// // {
// //   CALL("XMLAttribute::XMLAttribute");
// // }

// /**
//  * Create a new integer-valued attribute.
//  */
// IntegerXMLAttribute::IntegerXMLAttribute (const vstring& name, int val)
//   : XMLAttribute::Data(name),
//     value(val)
// {
//   CALL("IntegerXMLAttribute::IntegerXMLAttribute");
// }

// /**
//  * Create a new long-valued attribute.
//  */
// LongXMLAttribute::LongXMLAttribute (const vstring& name, long val)
//   : XMLAttribute::Data(name),
//     value(val)
// {
//   CALL("LongXMLAttribute::LongXMLAttribute");
// }

// /**
//  * Create a new text-valued attribute.
//  */
// TextXMLAttribute::TextXMLAttribute (const vstring& name, const vstring& text)
//   : XMLAttribute::Data(name),
//     value(text)
// {
//   CALL("TextXMLAttribute::TextXMLAttribute");
// }

// /**
//  * Create a new double-valued attribute.
//  */
// DoubleXMLAttribute::DoubleXMLAttribute (const vstring& name, double val)
//   : XMLAttribute::Data(name),
//     value(val)
// {
//   CALL("DoubleXMLAttribute::DoubleXMLAttribute");
// }

// /**
//  * Create a new unsigned-valued attribute.
//  */
// UnsignedXMLAttribute::UnsignedXMLAttribute (const vstring& name, unsigned val)
//   : XMLAttribute::Data(name),
//     value(val)
// {
//   CALL("UnsignedXMLAttribute::UnsignedXMLAttribute");
// }

// /**
//  * Write this element  to a stream using no indentation.
//  */
// void XMLElement::write (ostream& str) const
// {
//   CALL("XMLElement::write");

//   write(str,0);
// } // XMLElement::write (ostream& str)


// /**
//  * Write this element to a stream using indentation.
//  */
// void XMLElement::write (ostream& str,int indent) const
// {
//   ASS(_data);
//   CALL("XMLElement::write/2");

//   _data->write(str,0);
// } // XMLElement::write (ostream& str,int indent)

// void XMLElement::addChild (const XMLElement& e)
// {
//   ASS(_data);
//   ASS(_data->kind() == DEEP);

//   static_cast<DeepXMLElement*>(_data)->addChild(e);
// } // XMLElement::addChild


// /**
//  * Write the element to the end of the file.
//  */
// void XMLElement::append (const vstring& file)
// {
//   CALL("XMLElement::append");

//   ofstream stream(file.c_str(),ios::app);
//   if (! stream) { // cannot open stream
//     USER_ERROR("cannot open file XML file for appending");
//   }

//   write(stream);
// } // void XMLElement::append (const char* file)

// /**
//  * Add attribute as the last attribute to this element's attributes.
//  */
// void XMLElement::Data::addAttribute(const XMLAttribute& att)
// {
//   CALL("XMLElement::addAttribute");

//   if (lastXMLAttribute.isNull()) {
//     firstXMLAttribute = att;
//     lastXMLAttribute = att;
//     return;
//   }
//   ASS(lastXMLAttribute.data());
//   lastXMLAttribute.data()->next = att;
//   lastXMLAttribute = att;
// } // XMLElement::Data::addAttribute


// /**
//  * Create a new text element with no attributes.
//  */
// TextXMLElement::TextXMLElement (const vstring& name, const vstring& txt)
//   : XMLElement::Data(name),
//     text(txt)
// {
//   CALL("TextXMLElement::TextXMLElement");
// }

// /**
//  * Create a new deep element with no attributes.
//  */
// DeepXMLElement::DeepXMLElement (const vstring& name)
//   : XMLElement::Data(name)
// {
//   CALL("DeepXMLElement::DeepXMLElement");
// }

// /**
//  * Create a new float-valued element with no attributes.
//  */
// FloatXMLElement::FloatXMLElement (const vstring& name, float val)
//   : XMLElement::Data(name),
//     value(val)
// {
//   CALL("FloatXMLElement::FloatXMLElement");
// }

// /**
//  * Create a new double-valued element with no attributes.
//  */
// DoubleXMLElement::DoubleXMLElement (const vstring& name, double val)
//   : XMLElement::Data(name),
//     value(val)
// {
//   CALL("DoubleXMLElement::DoubleXMLElement");
// }

// /**
//  * Create a new long-valued element with no attributes.
//  */
// LongXMLElement::LongXMLElement (const vstring& name, long val)
//   : XMLElement::Data(name),
//     value(val)
// {
//   CALL("LongXMLElement::LongXMLElement");
// }

// /**
//  * Create a new integer-valued element with no attributes.
//  */
// IntegerXMLElement::IntegerXMLElement (const vstring& name, int val)
//   : XMLElement::Data(name),
//     value(val)
// {
//   CALL("IntegerXMLElement::IntegerXMLElement");
// }

// /**
//  * Write a list of attributes to ostream.
//  * @since 28/08/2004 Torrevieja, changed to translate special characters
//  */
// void XMLAttribute::Data::writeList (ostream& str) const
// {
//   CALL("XMLAttribute::Data::writeList (ostream& str)");

//   for (const Data* attr = this; attr; attr = attr->next._data) {
//     str << ' ';
//     XMLElement::writeString(str,attr->name);
//     str << "=\"";
//     attr->writeValue(str);
//     str << '\"';
//   }
// } // XMLAttribute::writeList

// /**
//  * Write a list of attributes to ostream.
//  */
// void XMLAttribute::writeList (ostream& str) const
// {
//   _data->writeList(str);
// } // XMLAttribute::writeList


// /**
//  * Write the value to an ostream.
//  * @since 28/08/2004 Torrevieja, changed to translate special characters
//  */
// void TextXMLAttribute::writeValue (ostream& str) const
// {
//   XMLElement::writeString(str,value);
// } // TextXMLAttribute::writeValue


// /**
//  * Write the value to an ostream.
//  */
// void IntegerXMLAttribute::writeValue (ostream& str) const
// {
//   str << value;
// } // IntegerXMLAttribute::writeValue


// /**
//  * Write the value to an ostream.
//  */
// void LongXMLAttribute::writeValue (ostream& str) const
// {
//   CALL("LongXMLAttribute::writeValue");
//   str << value;
// } // LongXMLAttribute::writeValue


// /**
//  * Write the value to an ostream.
//  */
// void DoubleXMLAttribute::writeValue (ostream& str) const
// {
//   str << value;
// } // DoubleXMLAttribute::writeValue


// /**
//  * Write the value to an ostream.
//  */
// void UnsignedXMLAttribute::writeValue (ostream& str) const
// {
//   str << value;
// } // UnsignedXMLAttribute::writeValue


// /**
//  * Write the content of a deep element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation
//  */
// void DeepXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("DeepXMLElement::writeContent(ostream& str, int indent)");

//   XMLElement::Data* d = firstChild.data();
//   if (! d) {
//     return;
//   }
//   str << '\n';
//   do {
//     d->write(str,indent+1);
//     d = d->next.data();
//   } while (d);
//   writeSpaces(str,indent);
// } // DeepXMLElement::writeContent

// /**
//  * Write the content (that is, the text) of a text element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation, plays no role
//  * @since 28/08/2004 Torrevieja, changed to translate special characters
//  */
// void TextXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("TextXMLElement::writeContent");
//   XMLElement::writeString(str,text);
// } // TextXMLElement::writeContent


// /**
//  * Write the content (that is, the value) of a long-valued 
//  * element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation, plays no role
//  */
// void LongXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("LongXMLElement::writeContent");
//   str << value;
// } // LongXMLElement::writeContent

// /**
//  * Write the content (that is, the value) of a integer-valued 
//  * element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation, plays no role
//  */
// void IntegerXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("IntegerXMLElement::writeContent");
//   str << value;
// } // IntegerXMLElement::writeContent

// /**
//  * Write the content (that is, the value) of a float-valued 
//  * element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation, plays no role
//  */
// void FloatXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("FloatXMLElement::writeContent");
//   str << value;
// } // FloatXMLElement::writeContent

// /**
//  * Write the content (that is, the value) of a double-valued 
//  * element to an ostream.
//  *
//  * @param str the stream
//  * @param indent indentation, plays no role
//  */
// void DoubleXMLElement::writeContent (ostream& str, int indent) const
// {
//   CALL("DoubleXMLElement::writeContent");
//   str << value;
// } // DoubleXMLElement::writeContent

// /**
//  * Writing an XML footer &lt;/name&gt; to a stream.
//  */
// void XMLElement::Data::writeFooter (ostream& str) const
// {
//   CALL("XMLElement::Data::writeFooter");
//   str << "</" << name << '>';
// } // XMLElement::Data::writeFooter

// /**
//  * Write n spaces to str.
//  */
// void XMLElement::Data::writeSpaces (ostream& str,int n)
// {
//   CALL("XMLElement::Data::writeSpaces");

//   ASS(n >= 0);

//   while (n > 0) {
//     n--;
//     str << ' ';
//   }
// } // XMLElement::Data::writeSpaces

// /**
//  * Write an element to an ostream. This is a virtual function that does 
//  * not work correctly for empty or deep elements, so EmptyXMLElement and
//  * DeepXMLElement redefine it.
//  *
//  * @param str the stream
//  * @param indent indentation
//  */
// void XMLElement::Data::write (ostream& str, int indent) const
// {
//   CALL("XMLElement::Data::write(ostream& str, int indent)");

//   writeSpaces(str,indent);
//   str << '<' << name;
//   firstXMLAttribute.writeList(str);
//   writeEndOfHeader(str);
//   str << '>';
//   writeContent(str,indent);
//   writeFooter(str);
//   str << '\n';
// } // XMLElement::write

// /**
//  * Writes the extra part of header in the empty element.
//  */
// void EmptyXMLElement::writeEndOfHeader (ostream& str) const
// {
//   CALL("EmptyXMLElement::writeEndOfHeader");
//   str << " /";
// }

// /**
//  * Write a vstring by translating characters in it.
//  * @since 28/08/2004 Torrevieja
//  */
// void XMLElement::writeString (ostream& str,const vstring& s)
// {
//   CALL("XMLElement::writeString");

//   size_t length = s.length();
//   for (size_t i=0;i < length;i++) {
//     char c = s[i];
//     switch (c) {
//     case '>':
//       str << "&gt;";
//       break;
//     case '<':
//       str << "&lt;";
//       break;
//     case '&':
//       str << "&amp;";
//       break;
//     case '\'':
//       str << "&apos;";
//       break;
//     case '\"':
//       str << "&quot;";
//       break;
//     default:
//       str << c;
//       break;
//     }
//   }
// } // XMLElement::writeString

// /**
//  * Find an attribute with a given @b name and return it in @b result
//  * @since 07/04/2005 Torrevieja
//  */
// void XMLAttribute::find (const vstring& name,XMLAttribute& result) const
// {
//   CALL("XMLAttribute::find");

//   const XMLAttribute* a = this;
//   while(a->_data) {
//     if (a->_data->name == name) {
//       result = *a;
//       return;
//     }
//     a = &(a->_data->next);
//   }
// } // XMLAttribute::find


// /**
//  * Check that the element is deep and if not, raise an exception
//  * @since 16/09/2005 Redmond
//  */
// void XMLElement::checkDeep () const
// {
//   CALL("XMLElement::checkDeep");

//   if (_data->kind() != DEEP) {
//     XML_ERROR("XML element with subelements expected",*this);
//   }
// } // XMLElement::checkDeep()


// /**
//  * Check that the element is empty and if not, raise an exception
//  * @since 16/09/2005 Redmond
//  */
// void XMLElement::checkEmpty () const
// {
//   CALL("XMLElement::checkEmpty");

//   if (_data->kind() != EMPTY) {
//     XML_ERROR("XML element with subelements expected",*this);
//   }
// } // XMLElement::checkEmpty()


// /**
//  * Check that the element is text and if not, raise an exception
//  * @since 16/09/2005 Redmond
//  */
// void XMLElement::checkText () const
// {
//   CALL("XMLElement::checkText");

//   if (_data->kind() != TEXT) {
//     XML_ERROR("XML element with a simple text content expected",*this);
//   }
// } // XMLElement::checkText()


// /**
//  * Return the fist child of a deep element.
//  * @since 06/10/2005 Redmond
//  */
// XMLElement XMLElement::firstChild () const
// {
//   CALL("XMLElement::firstChild");
//   ASS(_data);
//   ASS(_data->kind() == DEEP);

//   XMLElement result(static_cast<DeepXMLElement*>(_data)->firstChild);
//   return result;;
// } // XMLElement::firstChild

// /**
//  * True if the element is empty.
//  * @since 06/10/2005 Redmond
//  */
// bool XMLElement::isEmpty () const
// {
//   CALL("XMLElement::isEmpty");
//   ASS(_data);

//   return _data->kind() == EMPTY;
// } // XMLElement::isEmpty

// }

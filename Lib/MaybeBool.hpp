/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MaybeBool.hpp
 * Defines class MaybeBool.
 */

#ifndef __MaybeBool__
#define __MaybeBool__

#include "Debug/Assertion.hpp"

#include <ostream>

namespace Lib {

class MaybeBool
{
public:
  enum Value {
    False = 0,
    True = 1,
    Unknown = 2
  };

  MaybeBool() : _value(Unknown) {}
  MaybeBool(bool val) : _value(val ? True : False) {}
  MaybeBool(Value val) : _value(val) {}

  bool known() const { return _value!=Unknown; }
  bool isTrue() const { return _value==True; }
  bool isFalse() const { return _value==False; }

  bool operator==(const MaybeBool& o) const { return _value==o._value; }
  bool operator==(MaybeBool::Value o) const { return _value==o; }

  bool value() const {
    ASS(known());
    return _value==True;
  }

  void makeUnknown() { _value = Unknown; }
  void mightBecameFalse() { if(isTrue()) { makeUnknown(); } }
  void mightBecameTrue() { if(isFalse()) { makeUnknown(); } }

private:
  Value _value;
};

inline
std::ostream& operator<< (std::ostream& out, const MaybeBool& u )
{
  return out << (u.isFalse() ? "0" : u.isTrue() ? "1" : "Unknown");
}


}

#endif // __MaybeBool__

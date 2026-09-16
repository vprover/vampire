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
 * @file SATLiteral.hpp
 * Defines class SATLiteral.
 */


#ifndef __SATLiteral__
#define __SATLiteral__

#include <ostream>

#include "Debug/Assertion.hpp"
#include "Lib/Hash.hpp"

namespace SAT {

class SATLiteral
{
public:
  SATLiteral() = default;

  /*
   * wrap an integer SAT literal
   */
  SATLiteral(int lit) : _lit(lit) {}

  /**
   * Create a SAT literal of variable @b var and polarity &b polarity
   *
   * @b var must be greater than 0
   */
  SATLiteral(unsigned var, bool polarity) {
    ASS(var > 0 && var < std::numeric_limits<int>::max())
    _lit = polarity ? var : -int(var);
  }

  unsigned var() const { return abs(_lit); }
  bool positive() const { return _lit > 0; }
  SATLiteral opposite() const { return SATLiteral(-_lit); }

  unsigned defaultHash() const;
  unsigned defaultHash2() const;

  bool operator==(const SATLiteral& l) const
  { return _lit==l._lit; }
  bool operator!=(const SATLiteral& l) const
  { return _lit!=l._lit; }
  bool operator<(SATLiteral l) const
  { return _lit < l._lit; }

private:
  int _lit = 0;

  friend struct SATLiteralHash;
  friend struct SATLiteralHash2;
};

// hash a SATLiteral by FNV-1a of the signed integer it wraps
struct SATLiteralHash {
  static bool equals(SATLiteral l1, SATLiteral l2) { return l1 == l2; }
  static unsigned hash(SATLiteral l) { return FnvHash::hash(l._lit); }
};

// cheap secondary hash: that integer itself
struct SATLiteralHash2 {
  static unsigned hash(SATLiteral l) { return l._lit; }
};

inline unsigned SATLiteral::defaultHash() const { return SATLiteralHash::hash(*this); }
inline unsigned SATLiteral::defaultHash2() const { return SATLiteralHash2::hash(*this); }

inline std::ostream& operator<<(std::ostream &out, const SAT::SATLiteral &lit)
{
  if(!lit.positive())
    out << '~';
  return out << lit.var();
}

};

template<>
struct std::hash<SAT::SATLiteral> {
  unsigned operator()(SAT::SATLiteral l) const { return SAT::SATLiteralHash::hash(l); }
};


#endif /* __SATLiteral__ */

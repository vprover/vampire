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

  unsigned defaultHash() const { return DefaultHash::hash(_lit); }
  unsigned defaultHash2() const { return _lit; }

  bool operator==(const SATLiteral& l) const
  { return _lit==l._lit; }
  bool operator!=(const SATLiteral& l) const
  { return _lit!=l._lit; }
  bool operator<(SATLiteral l) const
  { return _lit < l._lit; }

private:
  int _lit = 0;
};

inline std::ostream& operator<<(std::ostream &out, const SAT::SATLiteral &lit)
{
  if(!lit.positive())
    out << '~';
  return out << lit.var();
}

};

template<>
struct std::hash<SAT::SATLiteral> {
  unsigned operator()(SAT::SATLiteral l) const { return l.defaultHash(); }
};


#endif /* __SATLiteral__ */

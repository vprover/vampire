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

  /**
   * Create a SAT literal of variable @b var and polarity &b polarity
   *
   * @b var must be greater than 0
   */
  SATLiteral(unsigned var, bool polarity) {
    ASS(var > 0 && var < std::numeric_limits<int>::max())
    _content = polarity ? var : -int(var);
  }

  unsigned var() const { return abs(_content); }
  bool positive() const { return _content > 0; }
  SATLiteral opposite() const { return SATLiteral(var(), !positive()); }

  unsigned defaultHash() const { return DefaultHash::hash(_content); }
  unsigned defaultHash2() const { return _content; }

  bool operator==(const SATLiteral& l) const
  { return _content==l._content; }
  bool operator!=(const SATLiteral& l) const
  { return _content!=l._content; }
  bool operator<(SATLiteral l) const
  { return _content < l._content; }

private:
  int _content;
};

inline std::ostream& operator<<(std::ostream &out, const SAT::SATLiteral &lit)
{
  if(!lit.positive())
    out << '~';
  return out << lit.var();
}

};

#endif /* __SATLiteral__ */

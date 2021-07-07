/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__CLAUSE_PATTERN__
#define __TEST__CLAUSE_PATTERN__

#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/TestUtils.hpp"

namespace Test {

class ClausePattern;

/**
 * An alternative between two patterns. matches if either of the subpatterns matches.
 */
struct AnyOf 
{
  shared_ptr<ClausePattern> lhs;
  shared_ptr<ClausePattern> rhs;
// friend bool operator==( ClausePattern const& l, ClausePattern const& r)
//   { return operator==((Copro const&)l,(Copro const&)r); }

  friend bool operator==(AnyOf const& l, AnyOf const& r)
  { return std::tie(l.lhs,l.rhs) == std::tie(r.lhs,r.rhs) ; }

  friend bool operator<(AnyOf const& l, AnyOf const& r)
  { return std::tie(l.lhs,l.rhs) < std::tie(r.lhs,r.rhs) ; }

};

/**
 * A pattern to match a clause against. 
 * Can be either a Clause, or a AnyOf which is a combination of two patterns.
 * A Clause matches a pattern Clause, if they are equal.
 * A Clause matches an AnyOf pattern if it matches both of the subpatterns.
 */
class ClausePattern : Coproduct<Kernel::Clause const*, AnyOf>
{
  using Copro =  Coproduct<Kernel::Clause const*, AnyOf>;
public:
  ClausePattern(Kernel::Clause const* clause) 
    : Copro(clause) {}

  ClausePattern(ClausePattern l, ClausePattern r) : Copro(AnyOf {
        Lib::make_unique<ClausePattern>(std::move(l)),
        Lib::make_unique<ClausePattern>(std::move(r))
      }) {}

  template<class EqualityOperator>
  bool matches(EqualityOperator& equality, Kernel::Clause const* result);
  friend ostream& operator<<(ostream& out, ClausePattern const& self);

  friend bool operator==( ClausePattern const& l, ClausePattern const& r)
  { return operator==((Copro const&)l,(Copro const&)r); }

  friend bool operator<( ClausePattern const& l, ClausePattern const& r)
  { return operator<((Copro const&)l,(Copro const&)r); }
};

inline ostream& operator<<(ostream& out, ClausePattern const& self) 
{
  return self.match(
      [&](Kernel::Clause const* const& self) -> ostream&
      { return out << pretty(self); },

      [&](AnyOf const& self)  -> ostream&
      { return out << pretty(self.lhs) << " or " << pretty(self.rhs); });
}

template<class EqualityOperator>
bool ClausePattern::matches(EqualityOperator& equality, Kernel::Clause const* result)
{
  return match(
      [&](Kernel::Clause const*& self) 
      { return equality.eq(result, self); },

      [&](AnyOf& self) 
      { return self.lhs->matches(equality, result) || self.rhs->matches(equality, result); });
}

inline ClausePattern anyOf(Kernel::Clause const* lhs) 
{ return ClausePattern(lhs); }

template<class... As>
inline ClausePattern anyOf(Kernel::Clause const* lhs, Kernel::Clause const* rhs, As... rest) 
{ return ClausePattern(lhs, anyOf(rhs, rest...)); }


};

#endif // __TEST__CLAUSE_PATTERN__

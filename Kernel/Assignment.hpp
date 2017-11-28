
/*
 * File Assignment.hpp.
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
 * @file Assignment.hpp
 * Defines class Assignment.
 */

#ifndef __Assignment__
#define __Assignment__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/ArrayMap.hpp"

#include "Constraint.hpp"

#include "Number.hpp"

namespace Kernel {

class Assignment {
public:
  Assignment(size_t varCnt) : _data(varCnt) {}
  
  bool isAssigned(Var v) { return _data.find(v); }

  void set(Var v, const BoundNumber& val) {
    CALL("Assignment::set");
    _data.set(v, val);
  }

  const BoundNumber& operator[](Var v) {
    CALL("Assignment::operator[]");
    return _data.get(v);
  }

  VarIterator getAssignedVars() const;
  
  BoundNumber evalCoeffs(Constraint::CoeffIterator coeffs);

  bool isSatisfied(const Constraint* c);
  bool isSatisfied(ConstraintList* c);

#if VDEBUG
  void assertSatisfied(const Constraint* c);
  void assertSatisfied(ConstraintList* c);
#endif

private:
  
  typedef ArrayMap<BoundNumber> AssignmentMap;
  AssignmentMap _data;
};

}
#endif //GNUMP
#endif // __Assignment__

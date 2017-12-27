
/*
 * File V2CIndex.hpp.
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
 * @file V2CIndex.hpp
 * Defines class V2CIndex.
 */

#ifndef __V2CIndex__
#define __V2CIndex__
#if GNUMP

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"
#include "Lib/RCPtr.hpp"

#include "Constraint.hpp"

namespace Kernel {

using namespace Lib;

class V2CIndex {
public:
  typedef VirtualIterator<Constraint*> Iterator;

  V2CIndex();

  void insert(const ConstraintRCPtr& c);
  void insert(Constraint* c) { insert(ConstraintRCPtr(c)); }
  void insert(ConstraintRCList* lst);

  Iterator getConsraintsWithBound(const BoundId& b) const;
  Iterator getConsraintsWithComplementary(const BoundId& b) const;

  ConstraintRCStack& getStack(const BoundId& b)
  {
    CALL("V2CIndex::getStack");
    ASS_L(b.var, _varCnt);

    return b.left ? _pos[b.var] : _neg[b.var];
  }

  const ConstraintRCStack& getStack(const BoundId& b) const
  {
    return const_cast<V2CIndex&>(*this).getStack(b);
  }

  size_t getConstraintCnt(const BoundId& b) const
  {
    return getStack(b).size();
  }

  /**
   * Return number of constraints containing variable @c v
   */
  size_t getConstraintCnt(Var v) const
  {
    return getConstraintCnt(BoundId(v, true))+getConstraintCnt(BoundId(v, false));
  }

  /**
   * If there is only one constraint containing boud @c b, return
   * pointer to it. Otherwise return 0.
   *
   * A constraint containt left bound if it has its variable with
   * positive coeffitient, and a right one if it has it with negative
   * coeffitient.
   */
  Constraint* getOnlyConstraint(const BoundId& b) const
  {
    CALL("V2CIndex::getOnlyConstraint");

    const ConstraintRCStack& s = getStack(b);
    if(s.size()!=1) {
      return 0;
    }
    return s.top().ptr();
  }

  void reset();
private:

  Var _varCnt;
  DArray<ConstraintRCStack> _pos;
  DArray<ConstraintRCStack> _neg;
};

}
#endif //GNUMP
#endif // __V2CIndex__

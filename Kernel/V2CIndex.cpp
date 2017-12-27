
/*
 * File V2CIndex.cpp.
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
 * @file V2CIndex.cpp
 * Implements class V2CIndex.
 */
#if GNUMP

#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

#include "V2CIndex.hpp"

namespace Kernel
{

V2CIndex::V2CIndex()
 : _varCnt(env.signature->vars()), _pos(_varCnt), _neg(_varCnt)
{
  CALL("V2CIndex::V2CIndex");
}

void V2CIndex::insert(const ConstraintRCPtr& c)
{
  CALL("V2CIndex::insert");

  size_t sz = c->coeffCnt();
  for(size_t i=0; i<sz; i++) {
    Var v = (*c)[i].var;
    bool pos = (*c)[i].isPositive();
    BoundId bound(v, pos);
    getStack(bound).push(c);
  }
}

void V2CIndex::insert(ConstraintRCList* lst)
{
  CALL("V2CIndex::insert");

  ConstraintRCList::Iterator cit(lst);
  while(cit.hasNext()) {
    insert(cit.next());
  }
}

void V2CIndex::reset()
{
  CALL("V2CIndex::reset");

  for(Var i=0; i<_varCnt; i++) {
    _pos[i].reset();
    _neg[i].reset();
  }
}

V2CIndex::Iterator V2CIndex::getConsraintsWithBound(const BoundId& b) const
{
  CALL("V2CIndex::getConsraintsWithBound");

  ConstraintRCStack::Iterator rcit(const_cast<V2CIndex&>(*this).getStack(b));
  return pvi( getMappingIterator(rcit, ConstraintRCPtr::UnRCFunctor()) );
}

V2CIndex::Iterator V2CIndex::getConsraintsWithComplementary(const BoundId& b) const
{
  CALL("V2CIndex::getConsraintsWithComplementary");

  return getConsraintsWithBound(-b);
}


}
#endif


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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Inference.hpp"

#include "Kernel/HOL/HOL.hpp"

#include "Lib/Metaiterators.hpp"

#include "BoolEqToDiseq.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace HOL::create;

ClauseIterator BoolEqToDiseq::generateClauses(Clause* cl)
{
  unsigned pos = 0;
  Literal* newLit = 0;

  for(unsigned i = 0; i < cl->length(); i++){
    Literal* lit = (*cl)[i];
    if(!lit->polarity()){
      pos++;
      continue;
    }
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort.isBoolSort()) {
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);
      if(HOL::isBool(lhs) || HOL::isBool(rhs)){
        pos++;
        continue;
      }
      TermList head = lhs.head();
      if(!head.isVar() && !head.isProxy(Proxy::NOT)){
        newLit = Literal::createEquality(false, app(neg(), lhs), rhs, AtomicSort::boolSort());
        goto afterLoop;
      }
      head = rhs.head();
      if(!head.isVar() && !head.isProxy(Proxy::NOT)){
        newLit = Literal::createEquality(false, lhs, app(neg(), rhs), AtomicSort::boolSort());
        goto afterLoop;
      }
    }
    pos++;
  }

  return ClauseIterator::getEmpty();

afterLoop:

  RStack<Literal*> resLits;

  for (unsigned i = 0; i < cl->length(); i++) {
    resLits->push(i == pos ? newLit : (*cl)[i]);
  }

  return pvi(getSingletonIterator(Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::EQ_TO_DISEQ, cl))));

}

}

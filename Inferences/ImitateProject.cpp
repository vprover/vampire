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
 * @file EqualityResolution.cpp
 * Implements class EqualityResolution.
 */

#if VHOL

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#include "EqualityResolution.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ImitateProject::IsFlexRigid
{
  bool operator()(Literal* l)
  { 
    ASS(l->isEquality());
    return l->isFlexRigid();
  }
};


struct ImitateProject::ResultFn
{
  ResultFn(Clause* cl)
      : _cl(cl), _cLen(cl->length()) {}
  ClauseIterator operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isFlexRigid());

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    static RobSubstitution subst(_handler);
    subst.reset();

    if(!subst.unify(arg0,0,arg1,0)){
      return 0;    
    }

    //cout << "equalityResolution with " + _cl->toString() << endl;
    //cout << "The literal is " + lit->toString() << endl;
    //cout << "cLength " << cLength << endl;

    unsigned newLen=_cLen-1+ subst.numberOfConstraints();

    Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, _cl));

    Literal* litAfter = 0;

    if (_afterCheck && _cl->numSelected() > 1) {
      TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
      litAfter = subst.apply(lit, 0);
    }

    unsigned next = 0;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        Literal* currAfter = subst.apply(curr, 0);

        if (litAfter) {
          TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);

          if (i < _cl->numSelected() && _ord->compare(currAfter,litAfter) == Ordering::GREATER) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            res->destroy();
            return 0;
          }
        }

        (*res)[next++] = currAfter;
      }
    }
    auto constraints = subst.getConstraints();
    while(constraints.hasNext()){
      Literal* constraint = constraints.next();
      (*res)[next++] = constraint;
    }
    ASS_EQ(next,newLen);

    env.statistics->equalityResolution++;

    return res;
  }
private:
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator ImitateProject::generateClauses(Clause* premise)
{
  CALL("ImitateProject::generateClauses");

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  // selected literals
  auto it1 = premise->getSelectedLiteralIterator();

  // only selected literals which are flex rigid
  auto it2 = getFilteredIterator(it1,IsNegativeEqualityFn());

  // carry out imitations and projections
  auto it3 = getMapAndFlattenIterator(it2,ResultFn(premise));

  return pvi( it4 );
}

}

#endif

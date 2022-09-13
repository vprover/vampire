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
      : _cl(cl), _cLen(cl->length()), _maxVar(cl->maxVar()) {}
  ClauseIterator operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    typedef ApplicativeHelper AH;

    ASS(lit->isEquality());
    ASS(lit->isFlexRigid());

    static RobSubstitution subst;
    static ClauseStack results;
    results.reset();

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    TermList flexTerm, rigidTerm;

    if(arg0.head().isVar()){
      flexTerm = arg0;
      rigidTerm = arg1;
    } else {
      flexTerm = arg1;
      rigidTerm = arg0;
    }

    TermList headFlex, headRigid;
    TermStack argsFlex, argsRigid;

    AH::getHeadAndArgs(flexTerm, headFlex, argsFlex);
    AH::getHeadAndArgs(rigidTerm, headRigid, argsRigid);
    ASS(argsFlex.size()); // Flex side is not a variable

    // replaces the result sort with a new result sort
    // e.g. i > i > o  ==> i > i > nat
    auto replaceRes = [](TermList arrowSort, TermList newRes){
      TermStack args;
      while(arrowSort.isArrowSort()){
        args.push(arrowSort.domain());
        arrowSort = arrowSort.result();
      }
      while(!args.isEmpty()){
        newRes = AtomicSort::arrowSort(args.pop(), newRes);
      }
      return newRes;
    };

    // imitation
    TermStack sorts; //sorts of arguments of flex head
    TermStack deBruijnIndices;
    AH::getArgSorts(flexTerm, sorts); 
    if(argsRigid.size()){
      for(int i = argsFlex.size() - 1; i >= 0; i--){
        deBruijnIndices.push(AH::getDeBruijnIndex(i, sorts[i]));
      }
    } 

    for(unsigned i = 0; i < argsRigid.size(); i++){

    }

  
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
  unsigned _maxVar;
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

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

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

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

struct EqualityResolution::IsNegativeEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, Ordering* ord = nullptr)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()) {}
  Clause* operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    FuncSubtermMap funcSubtermMap;

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    static Options::UnificationWithAbstraction uwa = env.options->unificationWithAbstraction();
    static Options::FunctionExtensionality ext = env.options->functionExtensionality();
    bool use_uwa_handler = uwa != Options::UnificationWithAbstraction::OFF;
    bool use_ho_handler = (ext == Options::FunctionExtensionality::ABSTRACTION) &&
                          env.property->higherOrder();

    if(use_ho_handler){
      TermList sort = SortHelper::getEqualityArgumentSort(lit);
      if(!arg0.isVar() && !arg1.isVar() && 
         !sort.isVar() && !sort.isArrowSort()){
        arg0 = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(arg0.term(), &funcSubtermMap);
        arg1 = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(arg1.term(), &funcSubtermMap);
      }
    }

    //cout << "arg0 " + arg0.toString() << endl;
    //cout << "arg1 " + arg1.toString() << endl;

    // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
    // and therefore a constraint can be created between arguments
    if(use_uwa_handler &&  arg0.isTerm() && arg1.isTerm() &&
       arg0.term()->functor() == arg1.term()->functor()){
      use_uwa_handler = false;
    }

    static RobSubstitution subst;
    static UnificationConstraintStack constraints;
    subst.reset();
    constraints.reset();
    subst.setMap(&funcSubtermMap);

    if(use_uwa_handler){
      UWAMismatchHandler hndlr(constraints);
      if(!subst.unify(arg0,0,arg1,0,&hndlr)){ 
        return 0; 
      }
    }

    if(use_ho_handler){
      HOMismatchHandler hndlr(constraints);
      if(!subst.unify(arg0,0,arg1,0,&hndlr)){ 
        return 0; 
      }    
    }

    if(!use_uwa_handler && !use_ho_handler && !subst.unify(arg0,0,arg1,0)){
      return 0;    
    }

    //cout << "equalityResolution with " + _cl->toString() << endl;
    //cout << "The literal is " + lit->toString() << endl;
    //cout << "cLength " << cLength << endl;

    unsigned newLen=_cLen-1+ constraints.length();

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
    for(unsigned i=0;i<constraints.length();i++){
      UnificationConstraint con = (constraints)[i];
      TermList qT = subst.apply(con.first.first,0);
      TermList rT = subst.apply(con.second.first,0);

      TermList sort = SortHelper::getResultSort(rT.term());
      Literal* constraint = Literal::createEquality(false,qT,rT,sort);      

      if(use_uwa_handler && uwa==Options::UnificationWithAbstraction::GROUND &&
         !constraint->ground() &&
         !UnificationWithAbstractionConfig::isInterpreted(qT) && 
         !UnificationWithAbstractionConfig::isInterpreted(rT) ) {

        // the unification was between two uninterpreted things that were not ground 
        res->destroy();
        return 0;
      }

      (*res)[next++] = constraint;
    }
    ASS_EQ(next,newLen);

    env.statistics->equalityResolution++;

    return res;
  }
private:
  bool _afterCheck;
  Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  CALL("EqualityResolution::generateClauses");

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsNegativeEqualityFn());

  auto it3 = getMappingIterator(it2,ResultFn(premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      &_salg->getOrdering()));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  return pvi( it4 );
}

/**
 * @c toResolve must be an negative equality. If it is resolvable,
 * resolve it and return the resulting clause. If it is not resolvable,
 * return 0.
 */
Clause* EqualityResolution::tryResolveEquality(Clause* cl, Literal* toResolve)
{
  CALL("EqualityResolution::tryResolveEquality");

  return ResultFn(cl)(toResolve);
}

}

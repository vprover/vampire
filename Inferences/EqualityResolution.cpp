
/*
 * File EqualityResolution.cpp.
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

#include "Saturation/SaturationAlgorithm.hpp"

#include "EqualityResolution.hpp"

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
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, Ordering* ord = nullptr)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()) {}
  DECL_RETURN_TYPE(Clause*);
  Clause* operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    static RobSubstitution subst;
    subst.reset();
    static Stack<UnificationConstraint> constraints;
    constraints.reset();
    MismatchHandler* hndlr = 0;
    // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
    // and therefore a constraint can be created between arguments
    //TODO add check on UWA option?
    //TODO delete handler? Or instead of creating memory perhaps we just need a NullHandlr
    if(lit->nthArgument(0)->isTerm() && lit->nthArgument(1)->isTerm() &&
       lit->nthArgument(0)->term()->functor() == lit->nthArgument(1)->term()->functor()){
      hndlr = new UWAMismatchHandler(constraints);
    }
    cout << "UNIFY " << lit->nthArgument(0)->toString() << " and " << lit->nthArgument(1)->toString() << endl;
    if(!subst.unify(*lit->nthArgument(0),0,*lit->nthArgument(1),1,hndlr)) {
      return 0;
    }
    cout << "HERE with subst " << subst.toString() << endl;
    cout << " and constraints " << endl;
    for(unsigned i=0;i<constraints.size();i++){
      auto con = constraints[i];
      cout << "> " << con.first.first.toString() << "!=" << con.second.first.toString() << endl;
    }


    unsigned newLen=_cLen-1 + constraints.length();

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
        cout << curr->toString() << " becomes " << currAfter->toString() << endl;

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
      pair<pair<TermList,unsigned>,pair<TermList,unsigned>> con = (constraints)[i];
      TermList qT = subst.apply(con.first.first,0);
      TermList rT = subst.apply(con.second.first,0);

      unsigned sort = SortHelper::getResultSort(rT.term());
      Literal* constraint = Literal::createEquality(false,qT,rT,sort);      

      static Options::UnificationWithAbstraction uwa = env.options->unificationWithAbstraction();
      if(uwa==Options::UnificationWithAbstraction::GROUND &&
         !constraint->ground() &&
         (!theory->isInterpretedFunction(qT) && !theory->isInterpretedConstant(qT)) &&
         (!theory->isInterpretedFunction(rT) && !theory->isInterpretedConstant(rT))){

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

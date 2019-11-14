
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
#include "Lib/Set.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

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

    FuncSubtermMap funcSubtermMap;

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    if(env.options->combinatorySup()){
      TermList sort = SortHelper::getEqualityArgumentSort(lit);
      if(!arg0.isVar() && !arg1.isVar() && 
         !sort.isVar() && !ApplicativeHelper::isArrowType(sort.term())){
        arg0 = ApplicativeHelper::replaceFunctionalSubterms(arg0.term(), &funcSubtermMap);
        arg1 = ApplicativeHelper::replaceFunctionalSubterms(arg1.term(), &funcSubtermMap);
      }
    }

    static RobSubstitution subst;
    subst.reset();
    subst.setMap(&funcSubtermMap);
    if(!subst.unify(arg0,0,arg1,0)) {
      return 0;
    }

    typedef pair<Term*, Term*> ConPair;
    unsigned cLength = subst.constraintsSize();
    const Set<ConPair>& constraints = subst.constraints();

    //cout << "equalityResolution with " + _cl->toString() << endl;
    //cout << "The literal is " + lit->toString() << endl;
    //cout << "cLength " << cLength << endl;

    unsigned newLen=_cLen-1+cLength;

    Inference* inf = new Inference1(Inference::EQUALITY_RESOLUTION, _cl);
    Clause* res = new(newLen) Clause(newLen, _cl->inputType(), inf);

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
    if(cLength){
      Set<ConPair>::Iterator it(constraints);
      ConPair con;
      while(it.hasNext()){
        con = it.next();
        TermList qT = subst.apply(TermList(con.first), 0);
        TermList rT = subst.apply(TermList(con.second), 0);

        TermList sort = SortHelper::getResultSort(rT.term());
        Literal* constraint = Literal::createEquality(false,qT,rT,sort);

        (*res)[next] = constraint;
        next++;        
      }
    }
    ASS_EQ(next,newLen);

    res->setAge(_cl->age()+1);
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

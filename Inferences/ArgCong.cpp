
/*
 * File ArgCong.cpp.
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
 * @file ArgCong.cpp
 * Implements class ArgCong.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "ArgCong.hpp"

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

struct ArgCong::IsPositiveEqualityFn
{
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { return l->isEquality() && l->isPositive(); }
};

struct ArgCong::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, Ordering* ord = nullptr)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()) {
        _freshVar = cl->maxVar() + 1;
      }
  DECL_RETURN_TYPE(Clause*);
  Clause* operator() (Literal* lit)
  {
    CALL("ArgCong::ResultFn::operator()");

    //cout << "ArgCong with clause " + _cl->toString() << endl;
    //cout << "the literal is " + lit->toString() << endl;

    ASS(lit->isEquality());
    ASS(lit->isPositive());

    static RobSubstitution subst;

    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    bool sortIsVar = eqSort.isVar();
    if(!sortIsVar && !ApplicativeHelper::isArrowType(eqSort.term())){
      return 0;
    }
   
    TermList alpha1, alpha2;
    if(sortIsVar){
      subst.reset();
      alpha1 = TermList(_freshVar+1, false);
      alpha2 = TermList(_freshVar+2, false);
      subst.unify(eqSort, 0, Term::arrowSort(alpha1, alpha2), 0);
    } else {
      alpha1 = *eqSort.term()->nthArgument(0);
      alpha2 = *eqSort.term()->nthArgument(1);
    }

    TermList freshVar = TermList(_freshVar, false);
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList newLhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, lhs, freshVar);
    TermList newRhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, rhs, freshVar);

    Literal* newLit = Literal::createEquality(true, newLhs, newRhs, alpha2);

    Inference* inf = new Inference1(Inference::ARG_CONG, _cl);
    Clause* res = new(_cLen) Clause(_cLen, _cl->inputType(), inf);

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        Literal* currAfter;

        if (sortIsVar && _afterCheck && _cl->numSelected() > 1) {
          currAfter = subst.apply(curr, 0);
          TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);

          if (i < _cl->numSelected() && _ord->compare(currAfter,newLit) == Ordering::GREATER) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            res->destroy();
            return 0;
          }
        } else {
          currAfter = curr;
        }

        (*res)[i] = currAfter;
      } else {
        (*res)[i] = newLit;
      }
    }

    res->setAge(_cl->age()+1);
    env.statistics->argumentCongruence++;

    return res;
  }
private:
  bool _afterCheck;
  Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
  unsigned _freshVar;
};

ClauseIterator ArgCong::generateClauses(Clause* premise)
{
  CALL("ArgCong::generateClauses");

  //cout << "argcong with " + premise->toString() << endl;
  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsPositiveEqualityFn());

  auto it3 = getMappingIterator(it2,ResultFn(premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      &_salg->getOrdering()));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  //cout << "out of arg cong" << endl;
  return pvi( it4 );
}

}

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
 * @file NegativeExt.cpp
 * Implements class NegativeExt.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "NegativeExt.hpp"

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

struct NegativeExt::IsNegativeEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && !l->isPositive(); }
};

struct NegativeExt::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl), _cLen(cl->length()) {}
  
  Clause* operator() (Literal* lit)
  {
    CALL("NegativeExt::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(!lit->isPositive());

    static DHMap<unsigned,TermList> varSorts;
    varSorts.reset();
   
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort.isVar() || !eqSort.isArrowSort()){
      return 0;
    }
    
    TermList lhs = *lit->nthArgument(0); 
    if(lhs.isVar()){
      varSorts.insert(lhs.var(), eqSort);
    } else {
      VariableWithSortIterator vit(lhs.term());
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }

    TermList rhs = *lit->nthArgument(1); 
    if(rhs.isVar()){
      varSorts.insert(rhs.var(), eqSort);
    } else {
      VariableWithSortIterator vit(rhs.term());
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }

    if(lit->isTwoVarEquality()){
      VariableWithSortIterator vit(eqSort.term());
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        //cout << "variable " + varTypePair.first.toString() + " has type " + varTypePair.second.toString() << endl;
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }
   
    static TermStack termVarSorts;
    static TermStack termVars;
    static TermStack typeVars;
    termVarSorts.reset();
    termVars.reset();
    typeVars.reset();
   
    unsigned var;
    TermList varSort; 
    DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
    while(mapIt.hasNext()) {
      mapIt.next(var, varSort);
      if(varSort == AtomicSort::superSort()){
        typeVars.push(TermList(var, false));
      } else {
        termVarSorts.push(varSort);
        termVars.push(TermList(var, false));
      }
    }

    TermList alpha1 = *eqSort.term()->nthArgument(0);
    TermList alpha2 = *eqSort.term()->nthArgument(1);
   
    TermList resultSort = alpha1;
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    SortHelper::normaliseSort(typeVars, resultSort);

    TermList skSymSort = AtomicSort::arrowSort(termVarSorts, resultSort);
    unsigned fun = Skolem::addSkolemFunction(typeVars.size(), typeVars.size(), 0, skSymSort);
    TermList head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
    //cout << "the head is " + head.toString() << endl;
    //cout << "It has sort " + skSymSort.toString() << endl;
    TermList skolemTerm = ApplicativeHelper::createAppTerm(SortHelper::getResultSort(head.term()), head, termVars);

    TermList newLhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, lhs, skolemTerm);
    TermList newRhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, rhs, skolemTerm);

    Literal* newLit = Literal::createEquality(false, newLhs, newRhs, alpha2);

    Clause* res = new(_cLen) Clause(_cLen, GeneratingInference1(InferenceRule::NEGATIVE_EXT, _cl));

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        (*res)[i] = curr;
      } else {
        (*res)[i] = newLit;
      }
    }

    env.statistics->negativeExtensionality++;
 
    return res;
  }
private:
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator NegativeExt::generateClauses(Clause* premise)
{
  CALL("NegativeExt::generateClauses");

  //cout << "NegativeExt with " + premise->toString() << endl;
  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsNegativeEqualityFn());

  auto it3 = getMappingIterator(it2,ResultFn(premise));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  //cout << "out of arg cong" << endl;
  return pvi( it4 );
}

}

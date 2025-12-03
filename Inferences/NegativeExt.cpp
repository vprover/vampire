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

#include "Lib/DHMap.hpp"
#include "Shell/Skolem.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NegativeExt.hpp"


namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using std::pair;

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
    TermList skolemTerm = HOL::create::app(head, termVars);

    TermList newLhs = HOL::create::app(alpha1, alpha2, lhs, skolemTerm);
    TermList newRhs = HOL::create::app(alpha1, alpha2, rhs, skolemTerm);

    Literal* newLit = Literal::createEquality(false, newLhs, newRhs, alpha2);

    RStack<Literal*> resLits;

    for (Literal* curr : iterTraits(_cl->iterLits())) {
      resLits->push(curr == lit ? newLit : curr);
    }
 
    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::NEGATIVE_EXT, _cl));
  }
private:
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator NegativeExt::generateClauses(Clause* premise)
{
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

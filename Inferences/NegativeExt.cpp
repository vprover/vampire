
/*
 * File NegativeExt.cpp.
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
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { return l->isEquality() && !l->isPositive(); }
};

struct NegativeExt::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl), _cLen(cl->length()) {}
  
  DECL_RETURN_TYPE(Clause*);
  Clause* operator() (Literal* lit)
  {
    CALL("NegativeExt::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(!lit->isPositive());

    static DHMap<unsigned,TermList> varSorts;
    varSorts.reset();
   
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort.isVar() || !ApplicativeHelper::isArrowType(eqSort.term())){
      return 0;
    }
    
    TermList lhs = *lit->nthArgument(0); 
    if(lhs.isVar()){
      varSorts.insert(lhs.var(), eqSort);
    } else {
      VariableIterator2 vit(lhs.term());
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        if(!varSorts.find(varTypePair.first.var())){
          varSorts.insert(varTypePair.first.var(), varTypePair.second);
        }
      }
    }

    TermList rhs = *lit->nthArgument(1); 
    if(rhs.isVar()){
      if(!varSorts.find(rhs.var())){
        varSorts.insert(rhs.var(), eqSort);
      }
    } else {
      VariableIterator2 vit(rhs.term());
      if(_cl->number() == 85){ cout << "the rhs is " + rhs.toString() << endl; }
      while(vit.hasNext()){
        pair<TermList, TermList> varTypePair = vit.next();
        if(!varSorts.find(varTypePair.first.var())){
          varSorts.insert(varTypePair.first.var(), varTypePair.second);
        }
      }
    }

    //cout << "the eqSort is " + eqSort.toString() << endl;
    VariableIterator2 vit(eqSort.term());
    while(vit.hasNext()){
      pair<TermList, TermList> varTypePair = vit.next();
      //cout << "variable " + varTypePair.first.toString() + " has type " + varTypePair.second.toString() << endl;
      if(!varSorts.find(varTypePair.first.var())){
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }
   
    static Stack<TermList> argSorts;
    static Stack<TermList> termArgs;
    static Stack<TermList> args;
    argSorts.reset();
    termArgs.reset();
    args.reset();
   
    unsigned var;
    TermList varSort; 
    DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
    while(mapIt.hasNext()) {
      mapIt.next(var, varSort);
      if(varSort == Term::superSort()){
        args.push(TermList(var, false));//TODO check that this works
      } else {
        argSorts.push(varSort);
        termArgs.push(TermList(var, false));
      }
    }
    ASS(termArgs.size() == argSorts.size());

    VList* vl = VList::empty();
    for(int i = args.size() -1; i >= 0 ; i--){
      VList::push(args[i].var(), vl);
    }

    TermList alpha1 = *eqSort.term()->nthArgument(0);
    TermList alpha2 = *eqSort.term()->nthArgument(1);

    TermList skSymSort = Term::arrowSort(argSorts, alpha1);
    unsigned fun = Skolem::addSkolemFunction(VList::length(vl), 0, skSymSort, vl);
    TermList head = TermList(Term::create(fun, args.size(), args.begin()));
    //cout << "the head is " + head.toString() << endl;
    //cout << "It has sort " + skSymSort.toString() << endl;
    TermList skolemTerm = ApplicativeHelper::createAppTerm(skSymSort, head, termArgs);

    TermList newLhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, lhs, skolemTerm);
    TermList newRhs = ApplicativeHelper::createAppTerm(alpha1, alpha2, rhs, skolemTerm);

    Literal* newLit = Literal::createEquality(false, newLhs, newRhs, alpha2);

    Inference* inf = new Inference1(Inference::NEGATIVE_EXT, _cl);
    Clause* res = new(_cLen) Clause(_cLen, _cl->inputType(), inf);

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        (*res)[i] = curr;
      } else {
        (*res)[i] = newLit;
      }
    }

    res->setAge(_cl->age()+1);
    env.statistics->negativeExtensionality++;

    //cout << "the original clause " + _cl->toString() << endl;
    //cout << "the new clause " + res->toString() << endl;
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

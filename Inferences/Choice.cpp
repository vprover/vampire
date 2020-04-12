/*
 * File PrimitiveInstantiation.cpp.
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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHSet.hpp"

#include "Choice.hpp"

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

Clause* Choice::createChoiceAxiom(TermList op, TermList set)
{
  CALL("Choice::createChoiceAxiom");

  TermList opType = SortHelper::getResultSort(op.term());
  TermList setType = ApplicativeHelper::getNthArg(opType, 1);

  VList* fvars = set.freeVars();
  unsigned max = 0;
  while(fvars){
    if(fvars->head() > max){
      max = fvars->head();
    }
    fvars = fvars->tail();
  }
  TermList freshVar = TermList(max+1, false);
  TermList t1 = ApplicativeHelper::createAppTerm(setType, set, freshVar);

  TermList t2 = ApplicativeHelper::createAppTerm(opType, op, set);
  t2 =  ApplicativeHelper::createAppTerm(setType, set, t2);

  Inference* inf = new Inference(Inference::CHOICE_AXIOM);  
  Clause* axiom = new(2) Clause(2, Unit::AXIOM, inf);

  (*axiom)[0] = Literal::createEquality(true, t1, TermList(Term::foolFalse()), Term::boolSort());;
  (*axiom)[1] = Literal::createEquality(true, t2, TermList(Term::foolTrue()), Term::boolSort());;

  return axiom;
}

struct Choice::AxiomsIterator
{
  AxiomsIterator(TermList term)
  {
    CALL("Choice::AxiomsIterator");

    ASS(term.isTerm());
    _set = *term.term()->nthArgument(3);
    _headSort = Term::arrowSort(*term.term()->nthArgument(0),*term.term()->nthArgument(1));
    _resultSort = ApplicativeHelper::getResultSort(_headSort);

    DHSet<unsigned>* ops = env.signature->getChoiceOperators();
    DHSet<unsigned>::Iterator opsIt(*ops);
    _choiceOps.loadFromIterator(opsIt);
    _inBetweenNextandHasNext = false;
  }

  DECL_ELEMENT_TYPE(Clause*);

  bool hasNext() {  
    CALL("Choice::AxiomsIterator::hasNext()");
    
    if(_inBetweenNextandHasNext){ return true; }

    while(!_choiceOps.isEmpty()){
      unsigned op = _choiceOps.getOneKey();
      _choiceOps.remove(op);
      OperatorType* type = env.signature->getFunction(op)->fnType();
      if(type->typeArgsArity()){
        _nextChoiceOperator = TermList(Term::create1(op, _resultSort));
        _inBetweenNextandHasNext = true;
        return true;
      } else if(type->result() == _headSort) {
        _nextChoiceOperator = TermList(Term::createConstant(op));
        _inBetweenNextandHasNext = true;
        return true;        
      }
    }
     
    return false;   
  }

  OWN_ELEMENT_TYPE next()
  {
    CALL("Choice::AxiomsIterator::next()");

    _inBetweenNextandHasNext = false;
    Clause* c = createChoiceAxiom(_nextChoiceOperator, _set); 
    return c;
  }
private:
  DHSet<unsigned> _choiceOps;
  TermList _nextChoiceOperator;
  TermList _resultSort;
  TermList _headSort;
  TermList _set;
  bool _inBetweenNextandHasNext;
};

struct Choice::ResultFn
{
  ResultFn(){}
  
  DECL_RETURN_TYPE(VirtualIterator<Clause*>);
  OWN_RETURN_TYPE operator() (TermList term){
    TermList op = *term.term()->nthArgument(2);
    if(op.isVar()){
      return pvi(AxiomsIterator(term));
    } else {
      Clause* axiom = createChoiceAxiom(op, *term.term()->nthArgument(3));
      return pvi(getSingletonIterator(axiom));
    }
  }
};

struct Choice::IsChoiceTerm
{
  DECL_RETURN_TYPE(bool);
  bool operator()(TermList t)
  { 
    TermStack args;
    TermList head;
    ApplicativeHelper::getHeadAndArgs(t, head, args);
    if(args.size() != 1){ return false; }
    
    TermList headSort = Term::arrowSort(*t.term()->nthArgument(0), *t.term()->nthArgument(1));

    TermList tv = TermList(0, false);
    TermList o  = Term::boolSort();
    TermList sort = Term::arrowSort(Term::arrowSort(tv, o), tv);
 
    static RobSubstitution subst;
    subst.reset();
    return ((head.isVar() || env.signature->isChoiceOperator(head.term()->functor())) &&
           subst.match(sort,0,headSort,0));

  }
};


struct Choice::SubtermsFn
{
  SubtermsFn() {}

  DECL_RETURN_TYPE(VirtualIterator<TermList>);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    CALL("Choice::RewriteableSubtermsFn()");

    NonVariableNonTypeIterator nvi(lit);
    return pvi(getUniquePersistentIteratorFromPtr(&nvi));
  }
};

ClauseIterator Choice::generateClauses(Clause* premise)
{
  CALL("PrimitiveInstantiation::generateClauses");

  //cout << "Choice with " << premise->toString() << endl;
  
  //is this correct?
  auto it1 = premise->getSelectedLiteralIterator();
  //filter out literals that are not suitable for narrowing
  auto it2 = getMapAndFlattenIterator(it1, SubtermsFn());

  //pair of literals and possible rewrites that can be applied to literals
  auto it3 = getFilteredIterator(it2, IsChoiceTerm());
  
  //apply rewrite rules to literals
  auto it4 = getMapAndFlattenIterator(it3, ResultFn());
  

  return pvi( it4 );

}

}
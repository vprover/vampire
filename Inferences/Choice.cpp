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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"

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

  unsigned max = 0;
  FormulaVarIterator fvi(&set);
  while (fvi.hasNext()) {
    unsigned var = fvi.next();
    if (var > max) {
      max = var;
    }
  }
  TermList freshVar = TermList(max+1, false);

  TermList t1 = ApplicativeHelper::createAppTerm(setType, set, freshVar);
  TermList t2 = ApplicativeHelper::createAppTerm(opType, op, set);
  t2 =  ApplicativeHelper::createAppTerm(setType, set, t2);

  Clause* axiom = new(2) Clause(2, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::CHOICE_AXIOM));

  (*axiom)[0] = Literal::createEquality(true, t1, TermList(Term::foolFalse()), AtomicSort::boolSort());;
  (*axiom)[1] = Literal::createEquality(true, t2, TermList(Term::foolTrue()), AtomicSort::boolSort());;

  return axiom;
}

struct Choice::AxiomsIterator
{
  AxiomsIterator(TermList term)
  {
    CALL("Choice::AxiomsIterator");

    ASS(term.isTerm());
    _set = *term.term()->nthArgument(3);
    _headSort = AtomicSort::arrowSort(*term.term()->nthArgument(0),*term.term()->nthArgument(1));
    _resultSort = ApplicativeHelper::getResultApplieadToNArgs(_headSort, 1);

    //cout << "the result sort is " + _resultSort.toString() << endl;

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
      
      static RobSubstitution subst;
      static TermStack typeArgs;
      typeArgs.reset();
      subst.reset();

      for(int i = type->typeArgsArity() -1; i >= 0; i--){
        TermList typeArg = TermList((unsigned)i, false);
        typeArgs.push(typeArg);
      }
      Term* choiceOp = Term::create(op, typeArgs.size(), typeArgs.begin());
      TermList choiceOpSort = SortHelper::getResultSort(choiceOp);
      if(subst.unify(choiceOpSort, 0, _headSort, 1)){
        _nextChoiceOperator = TermList(choiceOp);
        _opApplied = subst.apply(_nextChoiceOperator, 0);
        _setApplied = subst.apply(_set, 1);
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
    Clause* c = createChoiceAxiom(_opApplied, _setApplied); 
    env.statistics->choiceInstances++;
    return c;
  }

private:
  DHSet<unsigned> _choiceOps;
  TermList _opApplied;
  TermList _setApplied;
  TermList _nextChoiceOperator;
  TermList _resultSort;
  TermList _headSort;
  TermList _set;
  bool _inBetweenNextandHasNext;
};

struct Choice::ResultFn
{
  ResultFn(){}
  
  VirtualIterator<Clause*> operator() (TermList term){
    TermList op = *term.term()->nthArgument(2);
    if(op.isVar()){
      return pvi(AxiomsIterator(term));
    } else {
      Clause* axiom = createChoiceAxiom(op, *term.term()->nthArgument(3));
      env.statistics->choiceInstances++;
      return pvi(getSingletonIterator(axiom));
    }
  }
};

struct Choice::IsChoiceTerm
{
  bool operator()(TermList t)
  { 
    TermStack args;
    TermList head;
    ApplicativeHelper::getHeadAndArgs(t, head, args);
    if(args.size() != 1){ return false; }
    
    TermList headSort = AtomicSort::arrowSort(*t.term()->nthArgument(0), *t.term()->nthArgument(1));

    TermList tv = TermList(0, false);
    TermList o  = AtomicSort::boolSort();
    TermList sort = AtomicSort::arrowSort(AtomicSort::arrowSort(tv, o), tv);
 
    static RobSubstitution subst;
    subst.reset();

    subst.reset();
    return ((head.isVar() || env.signature->isChoiceOperator(head.term()->functor())) &&
           subst.match(sort,0,headSort,1));

  }
};


struct Choice::SubtermsFn
{
  SubtermsFn() {}

  VirtualIterator<TermList> operator()(Literal* lit)
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

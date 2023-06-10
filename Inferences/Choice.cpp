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

#if VHOL

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

typedef ApplicativeHelper AH;

Clause* Choice::createChoiceAxiom(TermList op, TermList set)
{
  CALL("Choice::createChoiceAxiom");

  TermList setSort = SortHelper::getResultSort(op.term()).domain();

  unsigned max = 0;
  FormulaVarIterator fvi(&set);
  while (fvi.hasNext()) {
    unsigned var = fvi.next();
    if (var > max) {
      max = var;
    }
  }
  TermList freshVar = TermList(max+1, false);

  TermList t1 = AH::app(setSort, set, freshVar);
  TermList t2 = AH::app(op, set);
  t2 =          AH::app(setSort, set, t2);

  Clause* axiom = new(2) Clause(2, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::CHOICE_AXIOM));

  (*axiom)[0] = Literal::createEquality(true, t1, AH::bottom(), AtomicSort::boolSort());
  (*axiom)[1] = Literal::createEquality(true, t2, AH::top(), AtomicSort::boolSort());

  return axiom;
}

struct Choice::AxiomsIterator
{
  AxiomsIterator(TermList term)
  {
    CALL("Choice::AxiomsIterator");
    ASS(term.isApplication());
  
    _set = term.rhs(); 

    _headSort = AH::lhsSort(term);
    _resultSort = SortHelper::getResultSort(term.term());

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
      
      static RobSubstitutionTL subst;
      static TermStack typeArgs;
      typeArgs.reset();
      subst.reset();

      for(int i = type->numTypeArguments() -1; i >= 0; i--){
        TermList typeArg = TermList((unsigned)i, VarBank::QUERY_BANK);
        typeArgs.push(typeArg);
      }
      Term* choiceOp = Term::create(op, typeArgs.size(), typeArgs.begin());
      TermList choiceOpSort = SortHelper::getResultSort(choiceOp);
      if(subst.unify(choiceOpSort, _headSort)){
        _nextChoiceOperator = TermList(choiceOp);
        _opApplied = subst.apply(_nextChoiceOperator, VarBank::QUERY_BANK);
        _setApplied = subst.apply(_set, DEFAULT_BANK);
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
  
  VirtualIterator<Clause*> operator() (Term* t){
    TermList term(t);
    TermList op = term.lhs();
    if(op.isVar()){
      return pvi(AxiomsIterator(term));
    } else {
      Clause* axiom = createChoiceAxiom(op, term.rhs());
      env.statistics->choiceInstances++;
      return pvi(getSingletonIterator(axiom));
    }
  }
};

struct Choice::IsChoiceTerm
{
  bool operator()(Term* t)
  { 
    if(t->isLambdaTerm()) return false;
    TermStack args;
    TermList head;
    ApplicativeHelper::getHeadAndArgs(t, head, args);
    if(args.size() == 1 && !args[0].isVar() && !args[0].containsLooseIndex()){
      TermList headSort = AH::lhsSort(TermList(t));

      TermList tv = TermList(0, VarBank::QUERY_BANK); // put on QUERY_BANK to separate in from variables in headSort
      TermList o  = AtomicSort::boolSort();
      TermList sort = AtomicSort::arrowSort(AtomicSort::arrowSort(tv, o), tv);
   
      static RobSubstitutionTL subst;
      subst.reset();
      return ((head.isVar() || env.signature->isChoiceOperator(head.term()->functor())) &&
             subst.match(sort,headSort,VarBank::QUERY_BANK));
    }
    return false;
  }
};


struct Choice::SubtermsFn
{
  SubtermsFn() {}

  VirtualIterator<Term*> operator()(Literal* lit)
  {
    CALL("Choice::RewriteableSubtermsFn()");

    NonVariableNonTypeIterator nvi(lit);
    return pvi(getUniquePersistentIteratorFromPtr(&nvi));
  }
};

ClauseIterator Choice::generateClauses(Clause* premise)
{
  CALL("Choice::generateClauses");
  
  //is this correct?
  auto it1 = premise->getSelectedLiteralIterator();
 
  auto it2 = getMapAndFlattenIterator(it1, SubtermsFn());

  auto it3 = getFilteredIterator(it2, IsChoiceTerm());
  
  auto it4 = getMapAndFlattenIterator(it3, ResultFn());
  
  return pvi( it4 );

}

}

#endif

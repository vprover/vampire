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
 * @file Choice.cpp
 * Implements class Choice.
 */

#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHSet.hpp"

#include "Choice.hpp"

namespace HC = HOL::create;

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

Clause* Choice::createChoiceAxiom(TermList op, TermList set)
{
  TermList setSort = SortHelper::getResultSort(op.term()).domain();

  unsigned max = 0;
  FormulaVarIterator fvi(set);
  while (fvi.hasNext()) {
    unsigned var = fvi.next();
    if (var > max) {
      max = var;
    }
  }
  TermList freshVar = TermList(max+1, false);

  TermList t1 = HC::app(setSort, set, freshVar);
  TermList t2 = HC::app(op, set);
  t2 =          HC::app(setSort, set, t2);

  return Clause::fromLiterals(
      { Literal::createEquality(true, t1, TermList(Term::foolFalse()), AtomicSort::boolSort()),
        Literal::createEquality(true, t2, TermList(Term::foolTrue()), AtomicSort::boolSort())},
       NonspecificInference0(UnitInputType::AXIOM, InferenceRule::HILBERTS_CHOICE_INSTANCE)
  );
}

struct Choice::AxiomsIterator
{
  AxiomsIterator(Term* term)
  {
    _set = *term->nthArgument(3);
    _headSort = AtomicSort::arrowSort(*term->nthArgument(0),*term->nthArgument(1));
    _resultSort = HOL::getResultAppliedToNArgs(_headSort, 1);

    //cout << "the result sort is " + _resultSort.toString() << endl;

    DHSet<unsigned>* ops = env.signature->getChoiceOperators();
    DHSet<unsigned>::Iterator opsIt(*ops);
    _choiceOps.loadFromIterator(opsIt);
    _inBetweenNextandHasNext = false;
  }

  DECL_ELEMENT_TYPE(Clause*);

  bool hasNext() {
    if(_inBetweenNextandHasNext){ return true; }

    while(!_choiceOps.isEmpty()){
      unsigned op = _choiceOps.getOneKey();
      _choiceOps.remove(op);
      OperatorType* type = env.signature->getFunction(op)->fnType();

      static RobSubstitution subst;
      static TermStack typeArgs;
      typeArgs.reset();
      subst.reset();

      for(int i = type->numTypeArguments() -1; i >= 0; i--){
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
    _inBetweenNextandHasNext = false;
    Clause* c = createChoiceAxiom(_opApplied, _setApplied);
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

  VirtualIterator<Clause*> operator() (Term* term){
    TermList op = *term->nthArgument(2);
    if(op.isVar()){
      return pvi(AxiomsIterator(term));
    } else {
      Clause* axiom = createChoiceAxiom(op, *term->nthArgument(3));
      return pvi(getSingletonIterator(axiom));
    }
  }
};

struct Choice::IsChoiceTerm
{
  bool operator()(Term* t)
  {
    auto [head, args] = HOL::getHeadAndArgs(TermList(t));
    if(args.size() != 1){ return false; }

    TermList headSort = AtomicSort::arrowSort(*t->nthArgument(0), *t->nthArgument(1));

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

  VirtualIterator<Term*> operator()(Literal* lit)
  {
    NonVariableNonTypeIterator nvi(lit);
    return pvi(getUniquePersistentIteratorFromPtr(&nvi));
  }
};

ClauseIterator Choice::generateClauses(Clause* premise)
{
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

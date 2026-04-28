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
  for (const auto& var : iterTraits(FormulaVarIterator(set))) {
    if (var > max) {
      max = var;
    }
  }
  auto freshVar = TermList::var(max+1);

  TermList t1 = HC::app(setSort, set, freshVar);
  TermList t2 = HC::app(op, set);
  t2 =          HC::app(setSort, set, t2);

  return Clause::fromLiterals({
    Literal::createEquality(true, t1, HOL::create::bottom(), AtomicSort::boolSort()),
    Literal::createEquality(true, t2, HOL::create::top(), AtomicSort::boolSort())
  }, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::HILBERTS_CHOICE_INSTANCE));
}

struct Choice::AxiomsIterator
{
  AxiomsIterator(TermList term)
  {
    ASS(term.isApplication());

    _set = term.rhs();
    _headSort = HOL::lhsSort(term);
    _choiceOps.loadFromIterator(env.signature->getChoiceOperators()->iter());
  }

  DECL_ELEMENT_TYPE(Clause*);

  bool hasNext() {
    if (_curr) {
      return true;
    }

    while (_choiceOps.isNonEmpty()) {
      auto op = _choiceOps.pop();
      auto type = env.signature->getFunction(op)->fnType();

      static TermStack typeArgs;
      typeArgs.reset();
      for (int i = type->numTypeArguments() -1; i >= 0; i--) {
        typeArgs.push(TermList::var((unsigned)i));
      }

      auto choiceOp = Term::create(op, typeArgs.size(), typeArgs.begin());
      static RobSubstitution subst;
      subst.reset();

      if (subst.unify(SortHelper::getResultSort(choiceOp), 0, _headSort, 1)) {
        _curr = createChoiceAxiom(
          subst.apply(TermList(choiceOp), 0),
          subst.apply(_set, 1)
        );
        return true;
      }
    }

    return false;
  }

  OWN_ELEMENT_TYPE next()
  {
    Clause* res = nullptr;
    std::swap(res, _curr);
    return res;
  }

private:
  Stack<unsigned> _choiceOps;
  Clause* _curr = nullptr;
  TermList _headSort;
  TermList _set;
};

struct Choice::ResultFn
{
  VirtualIterator<Clause*> operator() (Term* t){
    TermList term(t);
    TermList op = term.lhs();
    if(op.isVar()){
      return pvi(AxiomsIterator(term));
    } else {
      Clause* axiom = createChoiceAxiom(op, term.rhs());
      return pvi(getSingletonIterator(axiom));
    }
  }
};

struct Choice::IsChoiceTerm
{
  bool operator()(Term* t)
  {
    if (t->isLambdaTerm()) {
      return false;
    }
    auto [head, args] = HOL::getHeadAndArgs(TermList(t));
    if (args.size() != 1 || args[0].isVar() || args[0].containsLooseDBIndex()) {
      return false;
    }
    TermList headSort = HOL::lhsSort(TermList(t));

    TermList tv = TermList::var(0);
    TermList sort = AtomicSort::arrowSort(AtomicSort::arrowSort(tv, AtomicSort::boolSort()), tv);

    static RobSubstitution subst;
    subst.reset();
    return ((head.isVar() || env.signature->isChoiceOperator(head.term()->functor())) &&
           subst.match(sort,0,headSort,1));
  }
};

ClauseIterator Choice::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .flatMap([](Literal* lit) {
      NonVariableNonTypeIterator nvi(lit);
      return pvi(getUniquePersistentIteratorFromPtr(&nvi));
    })
    .filter(IsChoiceTerm())
    .flatMap(ResultFn()));
}

}

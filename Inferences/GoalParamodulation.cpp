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
 * @file GoalParamodulation.cpp
 * Implements class GoalParamodulation.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/LiteralSelector.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "GoalParamodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace std;

void GoalParamodulation::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);

  _rhsIndex=static_cast<TermIndex<TermLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_RHS_INDEX) );
  _subtermIndex=static_cast<TermIndex<TermPositionSideLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_SUBTERM_INDEX) );
}

void GoalParamodulation::detach()
{
  _rhsIndex = nullptr;
  _subtermIndex = nullptr;
  _salg->getIndexManager()->release(GOAL_PARAMODULATION_RHS_INDEX);
  _salg->getIndexManager()->release(GOAL_PARAMODULATION_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

TermList replaceOccurrence(Term* t, const Term* orig, TermList repl, const Position& pos)
{
  Stack<pair<Term*,unsigned>> todo;
  Term* curr = t;
  for (unsigned i = 0; i < pos.size(); i++) {
    auto p = pos[i];
    ASS_L(p,curr->arity());
    todo.push(make_pair(curr,p));

    auto next = curr->nthArgument(p);
    ASS(next->isTerm());
    curr = next->term();
  }
  ASS_EQ(orig,curr);
  TermList res = repl;

  while(todo.isNonEmpty()) {
    auto [term,index] = todo.pop();
    TermStack args;
    for (unsigned i = 0; i < term->arity(); i++) {
      if (i == index) {
        args.push(TermList(res));
      } else {
        args.push(*term->nthArgument(i));
      }
    }
    res = TermList(Term::create(term,args.begin()));
  }
  return res;
}

ClauseIterator GoalParamodulation::generateClauses(Clause* premise)
{
  auto itf = premise->getSelectedLiteralIterator()
    .filter([](Literal* lit) { return lit->isNegative(); })
    .flatMap([this](Literal* lit)
      { return pushPairIntoRightIterator(lit, EqHelper::getSubtermIteratorWithPosition(lit,  _salg->getOrdering())); })
    .flatMap([this](pair<Literal*, tuple<Term*,Stack<unsigned>,Term*>> arg)
      { return pushPairIntoRightIterator(arg, _rhsIndex->getUnifications(get<0>(arg.second))); })
    .map([this,premise](pair<pair<Literal*, tuple<Term*,Stack<unsigned>,Term*>>, QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) -> Clause* {
      auto& qr = arg.second;
      return perform(premise, arg.first.first, get<2>(arg.first.second), get<0>(arg.first.second), get<1>(arg.first.second),
        qr.data->clause, qr.data->literal, qr.data->term, qr.unifier.ptr(), /*forward=*/ true);
    });

  auto itb = premise->getSelectedLiteralIterator()
    .flatMap(EqHelper::SuperpositionLHSIteratorFn(_salg->getOrdering(), _salg->getOptions()))
    .map([](pair<Literal*, TypedTermList> arg)
      { return make_pair(arg.first, EqHelper::getOtherEqualitySide(arg.first, arg.second)); })
    .flatMap([this] (pair<Literal*, TermList> arg)
      { return pushPairIntoRightIterator(arg,
          _subtermIndex->getUnifications(TypedTermList(arg.second, SortHelper::getEqualityArgumentSort(arg.first)))); })
    .map([this,premise](pair<pair<Literal*, TermList>, QueryRes<ResultSubstitutionSP, TermPositionSideLiteralClause>> arg) -> Clause* {
        if (premise == arg.second.data->clause) { return nullptr; }

        auto& qr = arg.second;
        return perform(qr.data->clause, qr.data->literal, qr.data->side, qr.data->term.term(), qr.data->pos,
          premise, arg.first.first, arg.first.second, qr.unifier.ptr(), /*forward=*/ false);
      });

  // Add the results of forward and backward together
  return pvi(concatIters(itf,itb)
    .filter(NonzeroFn()));
}

Clause* GoalParamodulation::perform(Clause* rwClause, Literal* rwLit, Term* rwSide, const Term* rwTerm, const Position& pos,
  Clause* eqClause, Literal* eqLit, TermList eqRhs, ResultSubstitution* subst, bool eqIsResult)
{
  ASS_EQ(rwClause->store(),Clause::ACTIVE);
  ASS_EQ(eqClause->store(),Clause::ACTIVE);
  ASS(rwLit->isNegative());
  ASS(eqLit->isPositive());

  const Ordering& ordering = _salg->getOrdering();

  struct Applicator : SubstApplicator {
    Applicator(ResultSubstitution* subst, bool result) : subst(subst), result(result) {}
    TermList operator()(unsigned v) const override { return subst->apply(TermList::var(v), result); }
    ResultSubstitution* subst;
    bool result;
  };

  Applicator rwAppl(subst, !eqIsResult);
  Applicator eqAppl(subst, eqIsResult);

  AppliedTerm eqLhsApplied(EqHelper::getOtherEqualitySide(eqLit, eqRhs), &eqAppl, true);
  AppliedTerm eqRhsApplied(eqRhs, &eqAppl, true);

  if (ordering.compareUnidirectional(eqLhsApplied,eqRhsApplied)!=Ordering::GREATER) {
    return nullptr;
  }

  AppliedTerm rwSideApplied(TermList(rwSide), &rwAppl, true);
  AppliedTerm rwOtherSideApplied(EqHelper::getOtherEqualitySide(rwLit, TermList(rwSide)), &rwAppl, true);

  if (Ordering::isGreaterOrEqual(ordering.compareUnidirectional(rwOtherSideApplied, rwSideApplied))) {
    return nullptr;
  }

  auto tgtSideS = replaceOccurrence(rwSideApplied.apply().term(), eqRhsApplied.apply().term(), eqLhsApplied.apply(), pos);
  auto tgtLitS = Literal::createEquality(false, tgtSideS, rwOtherSideApplied.apply(), AppliedTerm(rwLit->eqArgSort(), &rwAppl, true).apply());

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();

  Recycled<Stack<Literal*>> res;
  res->reserve(rwLength + eqLength - 1);
  res->push(tgtLitS);

  for (const auto& lit : rwClause->iterLits()) {
    if (lit == rwLit) {
      continue;
    }
    res->push(subst->apply(lit, !eqIsResult));
  }

  for (const auto& lit : eqClause->iterLits()) {
    if (lit == eqLit) {
      continue;
    }
    res->push(subst->apply(lit, eqIsResult));
  }

  return Clause::fromStack(*res, Inference(GeneratingInference2(InferenceRule::GOAL_PARAMODULATION, rwClause, eqClause)));
}

}
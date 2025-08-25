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
 * @file PartialRedundancyLazy.cpp
 * Implements class PartialRedundancyLazy.
 */

#include "Saturation/SaturationAlgorithm.hpp"

#include "Inferences/Superposition.hpp"

#include "Kernel/EqHelper.hpp"

#include "Shell/PartialRedundancyHandler.hpp"

#include "PartialRedundancyLazy.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace std;

Clause* getGeneratedParent(Clause* cl)
{
  // cout << "starting with " << cl->toNiceString() << endl;
  while (isSimplifyingInferenceRule(cl->inference().rule())) {
    // cout << "cl is " << cl->toNiceString() << endl;
    if (cl->inference().rule() == InferenceRule::FORWARD_DEMODULATION) {
      auto pit = cl->getParents();
      ALWAYS(pit.hasNext());
      cl = static_cast<Clause*>(pit.next());
    }
  }
  // cout << "returning" << endl;
  return cl;
}

bool PartialRedundancyLazy::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  auto gcl = getGeneratedParent(cl);
  const auto& inf = gcl->inference();

  if (inf.rule() != InferenceRule::SUPERPOSITION) {
    env.statistics->intFinInduction++;
    return false;
  }

  // TODO get inference that produced clause before simplifications

  // TODO check that premise did not participate in any simplifications

  auto sup = env.proofExtra.get<Inferences::SuperpositionExtra>(gcl);
  UnitIterator it = gcl->getParents();
  ALWAYS(it.hasNext());
  auto rwClause = static_cast<Clause*>(it.next());
  ALWAYS(it.hasNext());
  auto eqClause = static_cast<Clause*>(it.next());
  ALWAYS(!it.hasNext());

  // compute unifier for selected literals
  RobSubstitution subst;
  Literal *rwLit = sup.selected.selectedLiteral.selectedLiteral;
  Literal *eqLit = sup.selected.otherLiteral;
  TermList eqLHS = sup.rewrite.lhs;
  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList rwTerm = sup.rewrite.rewritten;
  ASS(eqLit->isEquality());
  ASS(eqLit->isPositive());
  ASS(eqLit->termArg(0) == eqLHS || eqLit->termArg(1) == eqLHS);
  ALWAYS(subst.unify(rwTerm, 0, eqLHS, 1));

  auto rwTermS = subst.apply(rwTerm, 0);
  auto tgtTermS = subst.apply(tgtTerm, 0);
  auto rwLitS = subst.apply(rwLit, 0);
  auto comp = ordering.compare(tgtTermS,rwTermS);

  auto rsubst = ResultSubstitution::fromSubstitution(&subst, 0, 1);
  env.statistics->inductionApplication++;

  const auto& parRedHandler = _salg->parRedHandler();
  // if (!parRedHandler.checkSuperposition(eqClause, eqLit, rwClause, rwLit, true, rsubst.ptr())) {
  //   // TODO
  //   // premises = pvi( getSingletonIterator(clauseFromHandler));
  //   premises = ClauseIterator::getEmpty();
  //   env.statistics->inductionApplicationInProof++;
  //   return true;
  // }

  if (!parRedHandler.checkSuperposition2(eqClause, rwClause, true, rsubst.ptr(), rwTermS, tgtTermS)) {
    // TODO
    // premises = pvi( getSingletonIterator(clauseFromHandler));
    premises = ClauseIterator::getEmpty();
    replacement = nullptr;
    env.statistics->inductionApplicationInProof++;
    return true;
  }

  parRedHandler.insertSuperposition(
    eqClause, rwClause, rwTerm, rwTermS, tgtTermS, eqLHS, rwLitS, eqLit, comp, true, rsubst.ptr());

  return false;
}

}

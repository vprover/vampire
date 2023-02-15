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
 * @file InductionPostponement.cpp
 * Implements class InductionPostponement.
 */

// #include <utility>

// #include "Indexing/IndexManager.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "InductionPostponement.hpp"
#include "Inferences/Induction.hpp"

using std::pair;
using std::make_pair;

TermList VAR = TermList(0,false);

namespace Inferences
{

namespace InductiveReasoning
{
using namespace Kernel;
using namespace Lib;

inline bool isPureCtorTerm(TermList tt)
{
  CALL("isPureCtorTerm");

  if (tt.isVar()) {
    return false;
  }
  DHSet<unsigned> vars;
  Stack<Term*> terms;
  terms.push(tt.term());
  while (terms.isNonEmpty()) {
    auto t = terms.pop();
    auto sym = env.signature->getFunction(t->functor());
    if (!sym->termAlgebraCons()) {
      // not term algebra constructor
      return false;
    }
    for (unsigned i = sym->numTypeArguments(); i < sym->arity(); i++) {
      auto ts = t->nthArgument(i);
      if (ts->isVar()) {
        if (!vars.insert(ts->var())) {
          // variable has multiple occurrences
          return false;
        }
      } else {
        terms.push(ts->term());
      }
    }
  }
  return true;
}

inline TermList createCtorWithVars(Term* t, unsigned index)
{
  CALL("createCtorWithVars");

  TermList sort = SortHelper::getResultSort(t);
  ASS(env.signature->isTermAlgebraSort(sort));
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  auto ctor = ta->constructor(index);
  auto taArity = ctor->numTypeArguments();
  auto arity = ctor->arity();

  TermStack args(arity);
  for (unsigned i = 0; i < taArity; i++) {
    args.push(*sort.term()->nthArgument(i));
  }
  for (unsigned i = 0; i < arity-taArity; i++) {
    args.push(TermList(i,false));
  }
  auto res = TermList(Term::create(ctor->functor(), args.size(), args.begin()));
  return res;
}

void InductionPostponement::attach(SaturationAlgorithm* salg)
{
  CALL("InductionPostponement::attach");

  _salg = salg;
  _enabled = _salg->getOptions().inductionPostponement();
  if (_enabled) {
    _lhsIndex = static_cast<TermIndex*>(salg->getIndexManager()->request(INDUCTION_POSTPONEMENT_LHS_INDEX));
    _literalIndex = static_cast<LiteralIndex*>(salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE));
  }
}

void InductionPostponement::detach()
{
  CALL("InductionPostponement::detach");

  if (_enabled) {
    _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
    _literalIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_POSTPONEMENT_LHS_INDEX);
    _lhsIndex = nullptr;
  }
  _salg = nullptr;
}

void InductionPostponement::updateIndices(InductionFormulaKey* key, bool adding)
{
  CALL("InductionPostponement::updateIndices");

  DHSet<Term*> done;
  DHSet<Literal*> doneL;
  TermReplacement trMaster(getPlaceholderForTerm(Term::createConstant(key->first)), VAR);

  for (const auto& lits : key->second.first) {
    for (const auto& lit : lits) {
      auto tlit = trMaster.transform(lit);
      ASS(doneL.insert(tlit)); // a key cannot contain a literal twice
      NonVariableNonTypeIterator it(tlit);
      while (it.hasNext()) {
        auto t = it.next();
        if (!t.containsSubterm(VAR) || !done.insert(t.term())) {
          it.right();
          continue;
        }
        if (adding) {
          _postponedTermIndex.insert(t, tlit, reinterpret_cast<Clause *>(key));
        } else {
          _postponedTermIndex.remove(t, tlit, reinterpret_cast<Clause *>(key));
        }
      }
      if (!tlit->isEquality()) {
        if (adding) {
          _postponedLitIndex.insert(tlit, reinterpret_cast<Clause *>(key));
        } else {
          _postponedLitIndex.remove(tlit, reinterpret_cast<Clause *>(key));
        }
      }
    }
  }
}

/**
 * Postpone the induction formula generation for @b e and the induction
 * application corresponding to @b ctx if needed. If the entry @b e is
 * already postponed, just save the application in the postponed stack
 * of @b e. Otherwise, check if there are clauses that may rewrite or
 * resolve with any literal of the induction formula. This is done by
 * first replacing the placeholder term with a variable @b x in each literal,
 * then finding equations that unify with a subterm of this literal and
 * binds @b x to a term algebra constructor term or finding a literal
 * that unifies with the literal binding @b x in the same way.
 */
bool InductionPostponement::maybePostpone(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("InductionPostponement::maybePostpone");
  TIME_TRACE("forward induction postponement");
  if (!_enabled) {
    return false;
  }
  // this induction is already postponed
  if (e->_postponed) {
    env.statistics->postponedInductionApplications++;
    e->_postponedApplications.push(ctx);
    return true;
  }
  // if not postponed but this field is initialized,
  // then the induction was reactivated already
  if (e->_activatingClauses.size()) {
    return false;
  }
  TermList sort = SortHelper::getResultSort(ctx._indTerm);
  if (!env.signature->isTermAlgebraSort(sort)) {
    return false;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  bool postpone = false;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    auto activating = findActivatingClauseForIndex(ctx, i);
    e->_activatingClauses.push(activating);
    if (!activating) {
      postpone = true;
      // rest of the activated clauses will be lazily updated later
      for (unsigned j = i+1; j < ta->nConstructors(); j++) {
        e->_activatingClauses.push(nullptr);
      }
      break;
    }
  }
  if (postpone) {
    // update entry and stats
    e->_postponed = true;
    e->_postponedApplications.push(ctx);
    env.statistics->postponedInductions++;
    env.statistics->postponedInductionApplications++;

    InductionFormulaKey *key;
    {
      // can't use std::pair with allocator
      BYPASSING_ALLOCATOR
      key = new InductionFormulaKey(InductionFormulaIndex::represent(ctx));
    }
    static_assert(sizeof(Clause *) == sizeof(InductionFormulaKey *), "must have same pointer size for evil hack");

    // update index
    updateIndices(key, true /*adding*/);
    return true;
  }
  return false;
}

/**
 * This function checks whether any of the postponed inductions can be
 * finally done by using the currently activated clause @b cl.
 */
void InductionPostponement::checkForPostponedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::checkForPostponedInductions");
  TIME_TRACE("backward induction postponement");
  if (!_enabled) {
    return;
  }
  ASS(_toBeRemoved.isEmpty());

  if (lit->isEquality()) {
    if (lit->isPositive()) {
      for (unsigned j=0; j<2; j++) {
        auto lhs = *lit->nthArgument(j);
        auto qrit = _postponedTermIndex.getUnifications(lhs,true);
        while (qrit.hasNext()) {
          auto qr = qrit.next();
          ASS(qr.clause);
          performInductionsIfNeeded(qr.substitution, reinterpret_cast<InductionFormulaKey *>(qr.clause), cl, clIt);
        }
      }
    }
  } else {
    auto qrit = _postponedLitIndex.getUnifications(lit, true/*complementary*/, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      ASS(qr.clause);
      performInductionsIfNeeded(qr.substitution, reinterpret_cast<InductionFormulaKey *>(qr.clause), cl, clIt);
    }
  }

  // The removal of inductions that were done above must be performed
  // afterwards, since we were traversing the indices until this point
  decltype(_toBeRemoved)::Iterator rit(_toBeRemoved);
  while (rit.hasNext()) {
    InductionFormulaKey* key = rit.next();
    auto ph = getPlaceholderForTerm(Term::createConstant(key->first));
    TermReplacement trMaster(ph, VAR);
    ASS(!key->second.second.first);
    ASS(!key->second.second.second);
    updateIndices(key, false /*adding*/);
    {
      BYPASSING_ALLOCATOR
      delete key;
    }
  }
  _toBeRemoved.reset();
}

void InductionPostponement::performInductionsIfNeeded(ResultSubstitutionSP subst, InductionFormulaKey* key, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::performInductionsIfNeeded");
  auto t = subst->applyToResult(VAR);
  if (!isPureCtorTerm(t)) {
    return;
  }
  if (_toBeRemoved.contains(key)) {
    return;
  }
  TermList sort = SortHelper::getResultSort(t.term());
  if (!env.signature->isTermAlgebraSort(sort)) {
    return;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  auto e = _formulaIndex.findByKey(*key);
  ASS(e);
  if (!e->_postponed) {
    return;
  }
  ASS(e->_postponedApplications.isNonEmpty());

  ASS_EQ(e->_activatingClauses.size(), ta->nConstructors());
  // first round, we check whether the cl is activating
  bool activate = false;
  for (unsigned j = 0; j < ta->nConstructors(); j++) {
    auto& curr = e->_activatingClauses[j];
    if ((!curr || curr->store()==Clause::NONE) &&
        ta->constructor(j)->functor() == t.term()->functor())
    {
      if (!curr) {
        activate = true;
      }
      curr = cl;
      // the functor matches at most one ctor, we can break
      break;
    }
  }
  if (!activate) {
    return;
  }
  // second round, if cl is activating, we update the rest
  for (unsigned j = 0; j < ta->nConstructors(); j++) {
    auto& curr = e->_activatingClauses[j];
    if (!curr || curr->store() == Clause::NONE) {
      curr = findActivatingClauseForIndex(e->_postponedApplications[0], j);
      if (!curr) {
        activate = false;
        break;
      }
    }
  }
  if (!activate) {
    return;
  }
  // any of the postponed contexts suffices to generate the formulas
  clIt.generateStructuralFormulas(e->_postponedApplications[0], e);
  ASS_NEQ(0,env.statistics->postponedInductions);
  env.statistics->postponedInductions--;
  while (e->_postponedApplications.isNonEmpty()) {
    auto ctx = e->_postponedApplications.pop();
    ASS_NEQ(0,env.statistics->postponedInductionApplications);
    env.statistics->postponedInductionApplications--;

    for (auto& kv : e->get()) {
      clIt.resolveClauses(kv.first, ctx, kv.second);
    }
  }
  e->_postponed = false;
  _toBeRemoved.insert(key);
}

Clause* InductionPostponement::findActivatingClauseForIndex(const InductionContext& ctx, unsigned index)
{
  CALL("InductionPostponement::findActivatingClauseForIndex");
  auto ph = getPlaceholderForTerm(ctx._indTerm);
  TermReplacement trMaster(ph, VAR);
  RobSubstitution subst;
  DHSet<Term*> tried;

  // create ctor replacement
  Substitution ctorSubst;
  ctorSubst.bind(VAR.var(), createCtorWithVars(ctx._indTerm, index));

  // check if there is a literal which unifies with an equality or
  // an opposite sign literal, if not store subterms in an index
  Clause* activating = nullptr;
  auto lIt = ctx.iterLits();
  while (!activating && lIt.hasNext()) {
    auto litMaster = trMaster.transform(lIt.next());

    NonVariableNonTypeIterator nvi(litMaster);
    while (!activating && nvi.hasNext()) {
      auto master = nvi.next();
      if (!master.containsSubterm(VAR)) {
        nvi.right();
        continue;
      }
      auto ctor = SubstHelper::apply(master, ctorSubst);
      if (!tried.insert(ctor.term())) {
        nvi.right();
        continue;
      }

      auto uit = _lhsIndex->getUnifications(ctor, false);
      while (uit.hasNext()) {
        auto qr = uit.next();
        subst.reset();
        ALWAYS(subst.unify(master, 0, qr.term, 1));
        auto tt = subst.apply(VAR, 0);
        if (isPureCtorTerm(tt)) {
          activating = qr.clause;
          break;
        }
      }
    }
    if (!activating && !litMaster->isEquality()) {
      auto litCtor = SubstHelper::apply(litMaster, ctorSubst);
      auto uit = _literalIndex->getUnifications(litCtor, true/*complementary*/, false);
      while (uit.hasNext()) {
        auto qr = uit.next();
        subst.reset();
        ALWAYS(subst.unifyArgs(litMaster, 0, qr.literal, 1));
        auto tt = subst.apply(VAR, 0);
        if (isPureCtorTerm(tt)) {
          activating = qr.clause;
          break;
        }
      }
    }
  }
  return activating;
}

}

}

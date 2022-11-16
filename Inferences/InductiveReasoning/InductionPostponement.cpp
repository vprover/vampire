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

/**
 * Given a stack of indices @b pos, which correspond to indices of ctors in the term algebra @b ta
 * that are still not covered by any clause for this particular induction, decide whether @b tt
 * from clause @b cl covers any of the remaining indices and update the induction entry @b e and
 * @b indices accordingly. 
 * 
 * A term covers a ctor from the term algebra if its top-level functor is the ctor functor and
 * it only contains term algebra terms with distinct variables. 
 */
inline void updatePositions(TermList tt, Stack<unsigned>& indices, TermAlgebra* ta, InductionFormulaIndex::Entry* e, Clause* cl) {
  if (!tt.isTerm()) {
    return;
  }
  auto t = tt.term();
  if (!env.signature->getFunction(t->functor())->termAlgebraCons()) {
    return;
  }
  for (unsigned i = 0; i < indices.size(); i++) {
    if (t->functor() != ta->constructor(indices[i])->functor()) {
      continue;
    }
    Set<unsigned> vars;
    SubtermIterator sti(t);
    while (sti.hasNext()) {
      auto st = sti.next();
      if (st.isVar()) {
        if (vars.contains(st.var())) {
          // variable has multiple occurrences
          return;
        }
        vars.insert(st.var());
      } else if (!env.signature->getFunction(st.term()->functor())->termAlgebraCons()) {
        // not term algebra constructor
        return;
      }
    }
    // term has the right structure, save the clause as activating
    ASS_EQ(e->_activatingClauses[indices[i]], nullptr);
    e->_activatingClauses[indices[i]] = cl;
    swap(indices[i],indices.top());
    indices.pop();
    return;
  }
}

inline bool isPureCtorTerm(TermList tt) {
  if (tt.isVar()) {
    return false;
  }
  Set<unsigned> vars;
  SubtermIterator sti(tt.term());
  while (sti.hasNext()) {
    auto st = sti.next();
    if (st.isVar()) {
      if (vars.contains(st.var())) {
        // variable has multiple occurrences
        return false;
      }
      vars.insert(st.var());
    } else if (!env.signature->getFunction(st.term()->functor())->termAlgebraCons()) {
      // not term algebra constructor
      return false;
    }
  }
  return true;
}

inline TermList createCtorWithVars(TermAlgebra* ta, unsigned index) {
  auto ctor = ta->constructor(index);
  TermStack args(ctor->arity());
  for (unsigned i = 0; i < ctor->arity(); i++) {
    args.push(TermList(i,false));
  }
  return TermList(Term::create(ctor->functor(), args.size(), args.begin()));
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
  auto ph = getPlaceholderForTerm(ctx._indTerm);
  TermReplacement trMaster(ph, VAR);
  DHSet<Term*> tried;
  RobSubstitution subst;
  bool postpone = false;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    // create ctor replacement
    Substitution ctorSubst;
    ctorSubst.bind(VAR.var(), createCtorWithVars(ta, i));

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
    e->_activatingClauses.push(activating);
    if (!activating) {
      postpone = true;
    }
  }
  if (postpone) {
    e->_postponed = true;
    e->_postponedApplications.push(ctx);
    env.statistics->postponedInductions++;
    env.statistics->postponedInductionApplications++;
    for (const auto& kv : ctx._cls) {
      for (const auto& lit : kv.second) {
        Stack<InductionFormulaKey>* ks = nullptr;
        // TODO: This multi-layered indexing is obviously not ideal, update
        // it to a single-layered one once custom LeafData is available
        if (_literalMap.getValuePtr(lit, ks)) {
          auto tlit = trMaster.transform(lit);
          NonVariableNonTypeIterator it(tlit);
          while (it.hasNext()) {
            auto t = it.next();
            if (!t.containsSubterm(VAR)) {
              it.right();
              continue;
            }
            _postponedTermIndex.insert(t, tlit, nullptr);
          }
          _postponedLitIndex.insert(tlit, nullptr);
        }
        ASS(ks);
        ks->push(InductionFormulaIndex::represent(ctx));
      }
    }
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
          auto tt = qr.substitution->applyToResult(VAR);
          performInductionsIfNeeded(tt, qr.literal, cl, clIt);
        }
      }
    }
  } else {
    auto qrit = _postponedLitIndex.getUnifications(lit, true/*complementary*/, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      auto tt = qr.substitution->applyToResult(VAR);
      performInductionsIfNeeded(tt, qr.literal, cl, clIt);
    }
  }
  // The removal of inductions that were done above must be performed
  // afterwards, since we were traversing the indices until this point
  decltype(_toBeRemoved)::Iterator rit(_toBeRemoved);
  while (rit.hasNext()) {
    InductionFormulaKey key;
    Term* ph;
    rit.next(key,ph);
    for (const auto& lits : key.first) {
      for (const auto& lit : lits) {
        Stack<InductionFormulaKey>* ks = nullptr;
        ALWAYS(!_literalMap.getValuePtr(lit, ks));
        int i = -1;
        for (unsigned j = 0; j < ks->size(); j++) {
          if ((*ks)[j] == key) {
            ASS_L(i,0);
            i = j;
#if !VDEBUG
            break;
#endif
          }
        }
        ASS_GE(i,0);
        swap((*ks)[i],ks->top());
        ks->pop();
        if (ks->isEmpty()) {
          _literalMap.remove(lit);
          TermReplacement tr(ph, VAR);
          auto tlit = tr.transform(lit);
          _postponedLitIndex.remove(tlit, nullptr);
          NonVariableNonTypeIterator it(tlit);
          while (it.hasNext()) {
            auto t = it.next();
            if (!t.containsSubterm(VAR)) {
              it.right();
              continue;
            }
            _postponedTermIndex.remove(t, tlit, nullptr);
          }
        }
      }
    }
  }
  _toBeRemoved.reset();
}

void InductionPostponement::performInductionsIfNeeded(TermList t, Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::performInductionsIfNeeded");
  if (!t.isTerm()) {
    return;
  }
  TermList sort = SortHelper::getResultSort(t.term());
  if (!env.signature->isTermAlgebraSort(sort)) {
    return;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  Substitution subst;
  subst.bind(VAR.var(), getPlaceholderForTerm(t.term()));
  auto ks = _literalMap.findPtr(lit->apply(subst));
  for (const auto& key : *ks) {
    if (_toBeRemoved.find(key)) {
      continue;
    }
    auto e = _formulaIndex.findByKey(key);
    ASS(e);
    ASS(e->_postponed);
    ASS(e->_postponedApplications.isNonEmpty());

    Stack<unsigned> pos;
    ASS_EQ(e->_activatingClauses.size(), ta->nConstructors());
    for (unsigned i = 0; i < ta->nConstructors(); i++) {
      if (!e->_activatingClauses[i]) {
        pos.push(i);
      }
    }
    updatePositions(t, pos, ta, e, cl);
    if (pos.isNonEmpty()) {
      continue;
    }
    // any of the postponed contexts suffices to generate the formulas
    auto ph = getPlaceholderForTerm(e->_postponedApplications[0]._indTerm);
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
    _toBeRemoved.insert(key,ph);
  }
};

}

}

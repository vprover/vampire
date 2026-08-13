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
 * @file PredicateElimination.cpp
 * Implements class PredicateElimination.
 */

#include "PredicateElimination.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"

#include "Shell/Options.hpp"
#include "Shell/Shuffling.hpp"
#include "Shell/Statistics.hpp"

#include "Debug/TimeProfiling.hpp"

#include <algorithm>

namespace Shell {

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;

/**
 * Renames variables by adding a fixed offset.
 */
struct VarShiftApplicator {
  unsigned off;
  TermList apply(unsigned var) const { return TermList::var(var + off); }
};

/**
 * Replaces a single variable by a term, leaving other variables intact.
 */
struct SingleVarApplicator {
  unsigned var;
  TermList term;
  TermList apply(unsigned v) const { return v == var ? term : TermList::var(v); }
};

void PredicateElimination::apply(Problem &prb)
{
  TIME_TRACE("predicate elimination");

  // resolving clauses of different colours could produce colour-mixing resolvents
  if (env.colorUsed) {
    return;
  }

  // dropping non-unifiable pairs is only sound if equality and theories don't interfere
  _equational = _forceEquationally || prb.hasEquality() || prb.hasInterpretedOperations() || prb.hasNumerals();

  _preds.ensure(env.signature->predicates());

  // clauses may still contain duplicate literals (or be tautologies) at this stage of
  // preprocessing; besides making our occurrence counting needlessly conservative, they would,
  // more importantly, violate an invariant of the multi-literal matching in ClauseCodeTree
  // (which in saturation is maintained by running these very simplifications on every new clause)
  Inferences::DuplicateLiteralRemovalISE duplicateLiteralRemoval;
  Inferences::TautologyDeletionISE tautologyDeletion;

  ClauseStack input;
  for (const auto& u : iterTraits(UnitList::Iterator(prb.units()))) {
    Clause *cl = u->asClause();
    Clause *simp = tautologyDeletion.simplify(duplicateLiteralRemoval.simplify(cl));
    if (simp != cl) {
      _modified = true;
      if (!simp) {
        continue; // a tautology, simply dropped
      }
      cl = simp;
    }
    input.push(cl);
  }

  if (_useSubsumption) {
    // inserting shorter clauses first, the forward check below
    // makes the initial clause set fully inter-subsumed
    std::stable_sort(input.begin(), input.end(),
                     [](Clause *a, Clause *b) { return a->length() < b->length(); });
  }

  for (Clause *cl : input) {
    if (_useSubsumption) {
      Clause *simplified = forwardSimplify(cl);
      if (simplified != cl) { // subsumed away, or replaced by a subsumption resolution descendant
        _modified = true;
        if (!simplified) {
          continue;
        }
        cl = simplified;
      }
    }
    _all.push(cl);
    handleClause</*add=*/true>(cl);
    if (_useSubsumption) {
      indexInsert(cl);
    }
  }
  _curTotal = _origTotal = _all.size();

  // under randomized preprocessing, each picked candidate predicate is with this
  // probability skipped: it gets marked as never-to-be-reconsidered, so it stays
  // in the problem for good (the loss is monotone; to be tuned)
  constexpr double RPR_SKIP_PROB = 0.1;
  bool rpr = env.options->randomizedPreprocessing();

  for (;;) {
    int pred = pickCandidate();
    if (pred < 0) {
      break;
    }
    if (rpr && Random::getDouble(0.0,1.0) < RPR_SKIP_PROB) {
      _preds[pred].rprSkipped = true;
      continue;
    }
    eliminate(prb, (unsigned)pred);
  }

  if (_modified) {
    UnitList *res = 0;
    for (const auto& cl : iterTraits(ClauseStack::Iterator(_all))) {
      if (!_deleted.contains(cl)) {
        UnitList::push(cl, res);
      }
    }
    prb.units() = res;
    if (_keptDisequality) {
      prb.reportEqualityAdded(true, _keptVarVarDisequality);
    }
    prb.invalidateProperty();
  }
}

template<bool add>
void PredicateElimination::handleClause(Clause *cl)
{
  static DHMap<unsigned, int, FnvHash, IdentityHash> occ;
  occ.reset();

  for (const auto& lit : *cl) {
    unsigned pred = lit->functor();
    if (env.signature->getPredicate(pred)->protectedSymbol()) {
      continue;
    }
    int *val;
    if (occ.getValuePtr(pred, val)) {
      *val = lit->isPositive() ? 1 : -1;
    }
    else {
      *val = 2;
    }
  }

  for (const auto& [pred, val] : iterTraits(occ.items())) {
    if constexpr (add) {
      if (val == 2) {
        _preds[pred].blockers++;
      }
      else if (val == 1) {
        _preds[pred].pos.insert(cl);
      }
      else {
        _preds[pred].neg.insert(cl);
      }
    } else {
      if (val == 2) {
        ASS_G(_preds[pred].blockers, 0);
        _preds[pred].blockers--;
      }
      else if (val == 1) {
        ALWAYS(_preds[pred].pos.remove(cl));
      }
      else {
        ALWAYS(_preds[pred].neg.remove(cl));
      }
    }
  }
}

bool PredicateElimination::eligible(unsigned pred) const
{
  const PredInfo &info = _preds[pred];
  return !info.eliminated && !info.rprSkipped && info.blockers == 0 && (info.pos.size() + info.neg.size() > 0);
}

double PredicateElimination::estimatedTotalAfter(unsigned pred) const
{
  double sp = _preds[pred].pos.size();
  double sn = _preds[pred].neg.size();
  return (double)_curTotal - sp - sn + sp * sn;
}

bool PredicateElimination::admissible(unsigned pred) const
{
  return estimatedTotalAfter(pred) <= (double)_origTotal * _totalLimit;
}

int PredicateElimination::pickCandidate() const
{
  static Stack<unsigned> order;
  order.reset();
  for (unsigned pred = 1; pred < _preds.size(); pred++) {
    order.push(pred);
  }
  if (env.options->randomTraversals()) {
    // ties on the estimate get broken randomly
    Shuffling::shuffleArray(order, order.size());
  }

  int best = -1;
  double bestEst = 0.0;
  for (unsigned pred : order) {
    if (eligible(pred) && admissible(pred)) {
      double est = estimatedTotalAfter(pred);
      if (best < 0 || est < bestEst) {
        best = pred;
        bestEst = est;
      }
    }
  }
  return best;
}

Literal *PredicateElimination::findPredLiteral(Clause *cl, unsigned pred, bool polarity) const
{
  for (const auto& lit : *cl) {
    if (lit->functor() == pred && lit->isPositive() == polarity) {
      return lit;
    }
  }
  ASSERTION_VIOLATION;
  return nullptr;
}

void PredicateElimination::eliminate(Problem &prb, unsigned pred)
{
  ASS(eligible(pred));

  ClauseStack posCls;
  ClauseStack negCls;
  {
    for (const auto& cl : iterTraits(_preds[pred].pos.iter())) {
      posCls.push(cl);
    }
    for (const auto& cl : iterTraits(_preds[pred].neg.iter())) {
      negCls.push(cl);
    }
  }

  if (env.options->showPreprocessing()) {
    cout << "[PP] pel eliminating " << env.signature->predicateName(pred)
         << " (|S_P| = " << posCls.size() << ", |S_~P| = " << negCls.size() << ")" << endl;
  }

  // record the model-repairing definition while S_P is still at hand
  recordElimination(prb, pred, posCls, negCls);

  ClauseStack resolvents;
  for (Clause *c : posCls) {
    Literal *plitC = findPredLiteral(c, pred, true);
    for (Clause *d : negCls) {
      Literal *plitD = findPredLiteral(d, pred, false);
      Clause *r = buildResolvent(c, plitC, d, plitD);
      if (r && _useSubsumption) {
        r = forwardSimplify(r);
      }
      if (r) {
        resolvents.push(r);
        env.statistics->predicateEliminationResolvents++;
        if (env.options->showPreprocessing()) {
          cout << "[PP] pel resolvent: " << r->toString() << endl;
        }
      }
    }
  }

  for (Clause *cl : posCls) {
    handleClause</*add=*/false>(cl);
    if (_useSubsumption) {
      indexRemove(cl);
    }
    _deleted.insert(cl);
  }
  for (Clause *cl : negCls) {
    handleClause</*add=*/false>(cl);
    if (_useSubsumption) {
      indexRemove(cl);
    }
    _deleted.insert(cl);
  }
  _curTotal -= posCls.size() + negCls.size();

  for (Clause *r : resolvents) {
    _all.push(r);
    handleClause</*add=*/true>(r);
    if (_useSubsumption) {
      indexInsert(r);
    }
  }
  _curTotal += resolvents.size();

  _preds[pred].eliminated = true;
  ASS(_preds[pred].pos.isEmpty());
  ASS(_preds[pred].neg.isEmpty());

  _modified = true;
  env.statistics->eliminatedPredicates++;
}

Clause *PredicateElimination::buildResolvent(Clause *c, Literal *plitC, Clause *d, Literal *plitD)
{
  if (_equational) {
    return buildResolventEq(c, plitC, d, plitD);
  }
  else {
    return buildResolventMgu(c, plitC, d, plitD);
  }
}

Clause *PredicateElimination::buildResolventMgu(Clause *c, Literal *plitC, Clause *d, Literal *plitD)
{
  static RobSubstitution subst;
  subst.reset();
  if (!subst.unifyArgs(plitC, 0, plitD, 1)) {
    return nullptr; // sound to drop, since there is no equality (and no theories) around
  }

  static LiteralStack lits;
  lits.reset();
  for (const auto& lit : *c) {
    if (lit != plitC) {
      lits.push(subst.apply(lit, 0));
    }
  }
  for (const auto& lit : *d) {
    if (lit != plitD) {
      lits.push(subst.apply(lit, 1));
    }
  }
  return assembleClause(lits, c, d);
}

Clause *PredicateElimination::buildResolventEq(Clause *c, Literal *plitC, Clause *d, Literal *plitD)
{
  ASS_EQ(plitC->arity(), plitD->arity());

  VarShiftApplicator shift{c->maxVar() + 1};

  static LiteralStack lits;
  lits.reset();
  for (const auto& lit : *c) {
    if (lit != plitC) {
      lits.push(lit);
    }
  }
  for (const auto& lit : *d) {
    if (lit != plitD) {
      lits.push(SubstHelper::apply(lit, shift));
    }
  }
  // this is where the "virtual flattening" happens
  for (unsigned i = 0; i < plitC->arity(); i++) {
    lits.push(Literal::createEquality(false,
                                      *plitC->nthArgument(i),
                                      SubstHelper::apply(*plitD->nthArgument(i), shift),
                                      SortHelper::getArgSort(plitC, i)));
  }

  // exhaustive equality substitution (note: no decomposition, so this is weaker than unification)
  for (bool changed = true; changed;) {
    changed = false;
    for (unsigned idx = 0; idx < lits.size(); idx++) {
      Literal *l = lits[idx];
      if (!l->isEquality() || l->isPositive()) {
        continue;
      }
      auto [a0, a1] = l->eqArgs();
      if (a0 == a1) { // t != t is simply false
        lits.swapRemove(idx);
        changed = true;
        break;
      }
      TermList var, tgt;
      if (a0.isVar() && !a1.containsSubterm(a0)) {
        var = a0;
        tgt = a1;
      }
      else if (a1.isVar() && !a0.containsSubterm(a1)) {
        var = a1;
        tgt = a0;
      }
      else {
        continue; // a residual disequality (to be kept)
      }
      lits.swapRemove(idx);
      SingleVarApplicator app{var.var(), tgt};
      for (auto& lit : lits) {
        lit = SubstHelper::apply(lit, app);
      }
      changed = true;
      break;
    }
  }

  return assembleClause(lits, c, d);
}

Clause *PredicateElimination::assembleClause(LiteralStack &lits, Clause *c, Clause *d)
{
  static DHSet<Literal *, FnvHash, PtrIdentityHash> seen;
  seen.reset();

  static LiteralStack out;
  out.reset();

  bool keptDiseq = false;
  bool keptVarVarDiseq = false;

  for (const auto& l : lits) {
    if (EqHelper::isEqTautology(l)) { // s = s
      return nullptr;
    }
    if (l->isEquality() && l->isNegative() && *l->nthArgument(0) == *l->nthArgument(1)) {
      continue; // t != t is simply false
    }
    if (seen.contains(Literal::complementaryLiteral(l))) { // a tautology
      return nullptr;
    }
    if (!seen.insert(l)) {
      continue; // a duplicate literal
    }
    out.push(l);
    if (l->isEquality() && l->isNegative()) {
      keptDiseq = true;
      if (l->nthArgument(0)->isVar() && l->nthArgument(1)->isVar()) {
        keptVarVarDiseq = true;
      }
    }
  }

  _keptDisequality |= keptDiseq;
  _keptVarVarDisequality |= keptVarVarDiseq;

  return Clause::fromStack(out, NonspecificInference2(InferenceRule::PREDICATE_ELIMINATION, c, d));
}

void PredicateElimination::recordElimination(Problem &prb, unsigned pred,
                                             ClauseStack const &posCls, ClauseStack const &negCls)
{
  if (posCls.isEmpty()) { // P occurs only negatively; setting it to false satisfies all its clauses
    prb.addTrivialPredicate(pred, false);
    return;
  }
  if (negCls.isEmpty()) { // P occurs only positively
    prb.addTrivialPredicate(pred, true);
    return;
  }

  /* Following the model construction from the proof (cf. the paper):
   * P(x0,...,xn-1) <=> \/_{D \/ P(ts) in S_P} exists ys. (x0 = ts[0] /\ ... /\ xn-1 = ts[n-1] /\ ~D)
   * where each clause's variables ys are renamed away from the head variables x0,...,xn-1.
   */
  unsigned ar = env.signature->predicateArity(pred);

  TermStack hargs;
  for (unsigned v = 0; v < ar; v++) {
    hargs.push(TermList::var(v));
  }
  Literal *head = Literal::create(pred, ar, true, hargs.begin());

  VarShiftApplicator shift{ar}; // clause variables become >= ar, i.e. disjoint from the head's

  FormulaList *disjuncts = FormulaList::empty();
  for (const auto& c : iterTraits(ClauseStack::ConstIterator(posCls))) {
    Literal *plit = findPredLiteral(c, pred, true);

    FormulaList *conjuncts = FormulaList::empty();
    for (unsigned i = 0; i < ar; i++) {
      FormulaList::push(new AtomicFormula(Literal::createEquality(true,
                                                                  TermList::var(i),
                                                                  SubstHelper::apply(*plit->nthArgument(i), shift),
                                                                  SortHelper::getArgSort(plit, i))),
                        conjuncts);
    }
    for (const auto& lit : *c) {
      if (lit != plit) {
        FormulaList::push(new AtomicFormula(
                              Literal::complementaryLiteral(SubstHelper::apply(lit, shift))),
                          conjuncts);
      }
    }
    Formula *inner = JunctionFormula::generalJunction(AND, conjuncts);

    // existentially close over the (shifted) clause variables
    DHMap<unsigned, TermList, FnvHash, IdentityHash> varSorts;
    SortHelper::collectVariableSorts(inner, varSorts);
    VSList *vs = VSList::empty();
    for (const auto& [var, sort] : iterTraits(varSorts.items())) {
      if (var >= ar) { // skip the head variables
        VSList::push(VarSort(var, sort), vs);
      }
    }
    Formula *disjunct = vs ? (Formula *)new QuantifiedFormula(EXISTS, vs, inner) : inner;
    FormulaList::push(disjunct, disjuncts);
  }

  Formula *body = JunctionFormula::generalJunction(OR, disjuncts);
  prb.addEliminatedPredicate(pred, new BinaryFormula(IFF, new AtomicFormula(head), body));
}

Clause *PredicateElimination::forwardSimplify(Clause *cl)
{
  ASS(_useSubsumption);

  // every subsumption resolution step strictly shrinks the clause, so this terminates
  for (;;) {
    Clause *replacement = nullptr;
    if (forwardSubsumedOrResolved(cl, replacement)) {
      env.statistics->predicateEliminationSubsumed++;
      return nullptr;
    }
    if (!replacement) {
      return cl;
    }
    env.statistics->predicateEliminationSRs++;
    if (env.options->showPreprocessing()) {
      cout << "[PP] pel subsumption resolution: " << replacement->toString() << endl;
    }
    cl = replacement;
  }
}

// a port of CodeTreeForwardSubsumptionAndResolution::perform to our preprocessing setting;
// the code tree indexes whole clauses and performs the multi-literal matching itself
bool PredicateElimination::forwardSubsumedOrResolved(Clause *cl, Clause *&replacement)
{
  ASS(_useSubsumption);
  ASS(!replacement);

  // ClauseMatcher::init asserts on both of these
  if (_ct.isEmpty() || cl->length() == 0) {
    return false;
  }

  static ClauseCodeTree<false>::ClauseMatcher cm;
  cm.init(&_ct, cl, /*sres=*/true);

  bool subsumed = false;
  Clause *premise;
  int resolvedQueryLit;
  if ((premise = cm.next(resolvedQueryLit))) {
    if (resolvedQueryLit == -1) {
      subsumed = true;
    }
    else {
      LiteralStack res;
      for (unsigned i = 0; i < cl->length(); i++) {
        if (i != (unsigned)resolvedQueryLit) {
          res.push((*cl)[i]);
        }
      }
      replacement = Clause::fromStack(res,
          SimplifyingInference2(InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION, cl, premise));
    }
  }
  cm.reset();

  return subsumed;
}

void PredicateElimination::indexInsert(Clause *cl)
{
  ASS(_useSubsumption);

  if (cl->length() == 0) {
    return; // the empty clause subsumes everything, but saturation will pick it up immediately anyway
  }
  _ct.insert(cl);
}

void PredicateElimination::indexRemove(Clause *cl)
{
  ASS(_useSubsumption);

  if (cl->length() == 0) { // mirrors the guard in indexInsert; the code tree would not find it
    return;
  }
  _ct.remove(cl);
}

} // namespace Shell

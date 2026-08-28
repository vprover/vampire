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

/**
 * Add (@b add) or remove one clause's worth of occurrences to (from) one side of a PredInfo.
 */
static void updateSide(bool add, DHMap<Clause *, unsigned, UnitHash, UnitNumberHash> &side,
                       unsigned &multi, Clause *cl, unsigned count)
{
  ASS_G(count, 0);

  if (add) {
    ALWAYS(side.insert(cl, count));
    if (count > 1) {
      multi++;
    }
  }
  else {
    ALWAYS(side.remove(cl).isSome());
    if (count > 1) {
      ASS_G(multi, 0);
      multi--;
    }
  }
}

template<bool add>
void PredicateElimination::handleClause(Clause *cl)
{
  static DHMap<unsigned, std::pair<unsigned, unsigned>, FnvHash, IdentityHash> occ; // pred -> (positive, negative) count
  occ.reset();

  for (const auto& lit : *cl) {
    unsigned pred = lit->functor();
    if (env.signature->getPredicate(pred)->protectedSymbol()) {
      continue;
    }
    std::pair<unsigned, unsigned> *val;
    occ.getValuePtr(pred, val, {0, 0});
    (lit->isPositive() ? val->first : val->second)++;
  }

  for (const auto& [pred, counts] : iterTraits(occ.items())) {
    const auto& [p, n] = counts;
    PredInfo &info = _preds[pred];
    if (p > 0 && n > 0) { // occurs in both polarities: a hard blocker (condition 1)
      if constexpr (add) {
        info.blockers++;
      }
      else {
        ASS_G(info.blockers, 0);
        info.blockers--;
      }
    }
    else if (p > 0) {
      updateSide(add, info.pos, info.posMulti, cl, p);
    }
    else {
      updateSide(add, info.neg, info.negMulti, cl, n);
    }
  }
}

bool PredicateElimination::eligible(unsigned pred) const
{
  const PredInfo &info = _preds[pred];
  if (info.eliminated || info.rprSkipped || info.blockers > 0 || info.pos.size() + info.neg.size() == 0) {
    return false;
  }
  // condition 2: multi-occurrence clauses may only sit on one of the two sides
  // (without multiOccurrence, we insist on no multi-occurrence clause at all)
  return _multiOccurrence ? (info.posMulti == 0 || info.negMulti == 0)
                          : (info.posMulti == 0 && info.negMulti == 0);
}

/** @b base to the @b exp-th; cheaper (and more accurate) than std::pow for our small exponents */
static double dpow(double base, unsigned exp)
{
  double res = 1.0;
  while (exp--) {
    res *= base;
  }
  return res;
}

// each nucleus with k occurrences spawns |satellites|^k hyper-resolvents
double PredicateElimination::multiOccurrenceResolvents(PredInfo const &info, double sp, double sn) const
{
  bool posNucleus = (info.negMulti == 0);
  double sats = posNucleus ? sn : sp;

  double resolvents = 0.0;
  for (const auto& k : iterTraits((posNucleus ? info.pos : info.neg).range())) {
    resolvents += dpow(sats, k); // note: k >= 1, so no 0^0 here
  }
  return resolvents;
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
    if (!eligible(pred)) {
      continue;
    }
    // admissible(pred), but sharing the estimate with the comparison below rather
    // than computing it twice for every candidate of every round
    double est = estimatedTotalAfter(pred);
    if (est > (double)_origTotal * _totalLimit) {
      continue;
    }
    if (best < 0 || est < bestEst) {
      best = pred;
      bestEst = est;
    }
  }
  return best;
}

void PredicateElimination::collectPredLiterals(Clause *cl, unsigned pred, bool polarity,
                                               Stack<unsigned> &idxs) const
{
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    if (lit->functor() == pred && lit->isPositive() == polarity) {
      idxs.push(i);
    }
  }
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
    for (const auto& cl : iterTraits(_preds[pred].pos.domain())) {
      posCls.push(cl);
    }
    for (const auto& cl : iterTraits(_preds[pred].neg.domain())) {
      negCls.push(cl);
    }
  }

  // the side that may carry multi-occurrence clauses acts as the nuclei of the hyper-resolutions;
  // note that with all multiplicities equal to 1 this keeps the positives the outer loop, as before
  bool posNucleus = posIsNucleus(pred);
  ClauseStack const &nuclei = posNucleus ? posCls : negCls;
  ClauseStack const &satellites = posNucleus ? negCls : posCls;

  if (env.options->showPreprocessing()) {
    cout << "[PP] pel eliminating " << env.signature->predicateName(pred)
         << " (|S_P| = " << posCls.size() << ", |S_~P| = " << negCls.size() << ")" << endl;
  }

  // record the model-repairing definition while both sides are still at hand
  recordElimination(prb, pred, posCls, negCls);

  // each satellite holds exactly one pred-literal (of the polarity opposite to the nuclei')
  LiteralStack satelliteLits;
  for (Clause *d : satellites) {
    satelliteLits.push(findPredLiteral(d, pred, !posNucleus));
  }

  ClauseStack resolvents;
  // note: with no satellites around, pred is pure, there is nothing to derive,
  // and the nuclei (the only clauses pred occurs in) simply go away below
  if (satellites.isNonEmpty()) {
    Stack<unsigned> nucIdxs;
    DArray<unsigned> choice;
    for (Clause *c : nuclei) {
      nucIdxs.reset();
      collectPredLiterals(c, pred, posNucleus, nucIdxs);
      ASS_G(nucIdxs.size(), 0);

      // an odometer over all the |satellites|^|nucIdxs| assignments of satellites to occurrences
      choice.init(nucIdxs.size(), 0);
      for (;;) {
        Clause *r = buildResolvent(c, nucIdxs, satellites, satelliteLits, choice);
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

        unsigned j = 0;
        for (; j < choice.size(); j++) {
          if (++choice[j] < satellites.size()) {
            break;
          }
          choice[j] = 0;
        }
        if (j == choice.size()) {
          break;
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

Clause *PredicateElimination::buildResolvent(Clause *nucleus, Stack<unsigned> const &nucIdxs,
                                             ClauseStack const &sats, LiteralStack const &satLits,
                                             DArray<unsigned> const &choice)
{
  if (_equational) {
    return buildResolventEq(nucleus, nucIdxs, sats, satLits, choice);
  }
  else {
    return buildResolventMgu(nucleus, nucIdxs, sats, satLits, choice);
  }
}

/**
 * Push those literals of @b nucleus that are not among the resolved-upon ones
 * (@b nucIdxs, which collectPredLiterals delivers in increasing order) onto @b lits,
 * having applied @b transform to each.
 */
template<class Transform>
static void pushNucleusRest(LiteralStack &lits, Clause *nucleus, Stack<unsigned> const &nucIdxs,
                            Transform transform)
{
  unsigned next = 0;
  for (unsigned i = 0; i < nucleus->length(); i++) {
    if (next < nucIdxs.size() && nucIdxs[next] == i) {
      next++;
      continue;
    }
    lits.push(transform((*nucleus)[i]));
  }
  ASS_EQ(next, nucIdxs.size());
}

Clause *PredicateElimination::buildResolventMgu(Clause *nucleus, Stack<unsigned> const &nucIdxs,
                                                ClauseStack const &sats, LiteralStack const &satLits,
                                                DArray<unsigned> const &choice)
{
  ASS_EQ(nucIdxs.size(), choice.size());

  static RobSubstitution subst;
  subst.reset();
  // variable bank 0 is the nucleus', bank j+1 the j-th satellite's; picking the same satellite
  // twice thus automatically resolves against two variable-disjoint variants of it.
  // Each unification proceeds modulo the bindings accumulated so far, so chaining is correct.
  for (unsigned j = 0; j < choice.size(); j++) {
    if (!subst.unifyArgs((*nucleus)[nucIdxs[j]], 0, satLits[choice[j]], j + 1)) {
      return nullptr; // sound to drop, since there is no equality (and no theories) around
    }
  }

  static LiteralStack lits;
  lits.reset();
  pushNucleusRest(lits, nucleus, nucIdxs, [&](Literal *lit) { return subst.apply(lit, 0); });
  for (unsigned j = 0; j < choice.size(); j++) {
    Literal *plit = satLits[choice[j]];
    for (const auto& lit : *sats[choice[j]]) {
      if (lit != plit) {
        lits.push(subst.apply(lit, j + 1));
      }
    }
  }
  return assembleClause(lits, nucleus, sats, choice);
}

Clause *PredicateElimination::buildResolventEq(Clause *nucleus, Stack<unsigned> const &nucIdxs,
                                               ClauseStack const &sats, LiteralStack const &satLits,
                                               DArray<unsigned> const &choice)
{
  ASS_EQ(nucIdxs.size(), choice.size());

  static LiteralStack lits;
  lits.reset();
  pushNucleusRest(lits, nucleus, nucIdxs, [](Literal *lit) { return lit; });

  // each satellite gets a variable range of its own, disjoint from the nucleus's and the others'
  unsigned off = nucleus->maxVar() + 1;
  for (unsigned j = 0; j < choice.size(); j++) {
    Literal *nlit = (*nucleus)[nucIdxs[j]];
    Literal *plit = satLits[choice[j]];
    ASS_EQ(nlit->arity(), plit->arity());

    VarShiftApplicator shift{off};
    for (const auto& lit : *sats[choice[j]]) {
      if (lit != plit) {
        lits.push(SubstHelper::apply(lit, shift));
      }
    }
    // this is where the "virtual flattening" happens
    for (unsigned i = 0; i < nlit->arity(); i++) {
      lits.push(Literal::createEquality(false,
                                        *nlit->nthArgument(i),
                                        SubstHelper::apply(*plit->nthArgument(i), shift),
                                        SortHelper::getArgSort(nlit, i)));
    }
    if (j + 1 < choice.size()) { // the last satellite's successor offset is never used
      off += sats[choice[j]]->maxVar() + 1;
    }
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

  return assembleClause(lits, nucleus, sats, choice);
}

Clause *PredicateElimination::assembleClause(LiteralStack &lits, Clause *nucleus,
                                             ClauseStack const &sats, DArray<unsigned> const &choice)
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

  ASS_G(choice.size(), 0);
  if (choice.size() == 1) { // the classical binary case; keep its inference binary too
    return Clause::fromStack(out,
        NonspecificInference2(InferenceRule::PREDICATE_ELIMINATION, nucleus, sats[choice[0]]));
  }

  // a satellite picked more than once is still just one premise
  static DHSet<Clause *, UnitHash, UnitNumberHash> premiseSeen;
  premiseSeen.reset();
  UnitList *premises = UnitList::empty();
  for (unsigned j = 0; j < choice.size(); j++) {
    Clause *d = sats[choice[j]];
    if (premiseSeen.insert(d)) {
      UnitList::push(d, premises);
    }
  }
  UnitList::push(nucleus, premises);
  return Clause::fromStack(out, NonspecificInferenceMany(InferenceRule::PREDICATE_ELIMINATION, premises));
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

  unsigned ar = env.signature->predicateArity(pred);

  TermStack hargs;
  for (unsigned v = 0; v < ar; v++) {
    hargs.push(TermList::var(v));
  }
  Literal *head = Literal::create(pred, ar, true, hargs.begin());

  // the primal definition below needs every clause of S_P to be P-free apart from its
  // single P-literal; when that fails, condition 2) guarantees S_~P is all-single instead,
  // and we can build the dual definition from it
  bool fromPos = (_preds[pred].posMulti == 0);
  Formula *body = definitionBody(pred, fromPos ? posCls : negCls, fromPos);

  prb.addEliminatedPredicate(pred, new BinaryFormula(IFF, new AtomicFormula(head), body));
}

/**
 * Following the model construction from the proof (cf. the paper), with @b fromPos:
 *   P(x0,...,xn-1) <=> \/_{C \/ P(ts) in S_P} exists ys. (x0 = ts[0] /\ ... /\ xn-1 = ts[n-1] /\ ~C)
 * and, dually, with !fromPos:
 *   P(x0,...,xn-1) <=> /\_{D \/ ~P(ss) in S_~P} forall ys. (x0 != ss[0] \/ ... \/ xn-1 != ss[n-1] \/ D)
 * where each clause's variables ys are renamed away from the head variables x0,...,xn-1.
 *
 * The first makes P as false as satisfying S_P permits, the second as true as S_~P permits.
 * Correspondingly, the first is only correct when every clause of S_P holds exactly one
 * P-literal (so that the C above is P-free), the second dtto for S_~P; condition 2)
 * guarantees at least one of the two applies.
 */
Formula *PredicateElimination::definitionBody(unsigned pred, ClauseStack const &cls, bool fromPos)
{
  unsigned ar = env.signature->predicateArity(pred);

  VarShiftApplicator shift{ar}; // clause variables become >= ar, i.e. disjoint from the head's

  FormulaList *juncts = FormulaList::empty();
  for (const auto& c : iterTraits(ClauseStack::ConstIterator(cls))) {
    Literal *plit = findPredLiteral(c, pred, fromPos);

    FormulaList *inner = FormulaList::empty();
    for (unsigned i = 0; i < ar; i++) {
      FormulaList::push(new AtomicFormula(Literal::createEquality(fromPos,
                                                                  TermList::var(i),
                                                                  SubstHelper::apply(*plit->nthArgument(i), shift),
                                                                  SortHelper::getArgSort(plit, i))),
                        inner);
    }
    for (const auto& lit : *c) {
      if (lit != plit) {
        Literal *l = SubstHelper::apply(lit, shift);
        FormulaList::push(new AtomicFormula(fromPos ? Literal::complementaryLiteral(l) : l), inner);
      }
    }
    Formula *junct = JunctionFormula::generalJunction(fromPos ? AND : OR, inner);

    // existentially (resp. universally) close over the (shifted) clause variables
    DHMap<unsigned, TermList, FnvHash, IdentityHash> varSorts;
    SortHelper::collectVariableSorts(junct, varSorts);
    VSList *vs = VSList::empty();
    for (const auto& [var, sort] : iterTraits(varSorts.items())) {
      if (var >= ar) { // skip the head variables
        VSList::push(VarSort(var, sort), vs);
      }
    }
    if (vs) {
      junct = new QuantifiedFormula(fromPos ? EXISTS : FORALL, vs, junct);
    }
    FormulaList::push(junct, juncts);
  }

  return JunctionFormula::generalJunction(fromPos ? OR : AND, juncts);
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

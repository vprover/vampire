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
#include "Kernel/LiteralByMatchability.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Inferences/InferenceEngine.hpp"

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
  TermList apply(unsigned var) const { return TermList(var + off, false); }
};

/**
 * Replaces a single variable by a term, leaving other variables intact.
 */
struct SingleVarApplicator {
  unsigned var;
  TermList term;
  TermList apply(unsigned v) const { return v == var ? term : TermList(v, false); }
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

  if (_useSubsumption) {
    _subsIndex = new LiteralSubstitutionTree<LiteralClause>();
  }

  _preds.ensure(env.signature->predicates());

  // clauses may still contain duplicate literals at this stage of preprocessing;
  // besides making our occurrence counting needlessly conservative, they would,
  // more importantly, violate an invariant of SATSubsumptionAndResolution
  // (which in saturation is maintained by running this very simplification on every new clause)
  Inferences::DuplicateLiteralRemovalISE duplicateLiteralRemoval;

  Stack<Clause *> input;
  UnitList::Iterator uit(prb.units());
  while (uit.hasNext()) {
    Unit *u = uit.next();
    ASS(u->isClause());
    Clause *cl = static_cast<Clause *>(u);
    Clause *dedup = duplicateLiteralRemoval.simplify(cl);
    if (dedup != cl) {
      _modified = true;
      cl = dedup;
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
    registerClause(cl);
    if (_useSubsumption) {
      indexInsert(cl);
    }
  }
  _curTotal = _origTotal = _all.size();

  // under randomized preprocessing, each picked candidate predicate is with this
  // probability skipped: it gets marked as never-to-be-reconsidered, so it stays
  // in the problem for good (the loss is monotone; to be tuned)
  constexpr double RPR_SKIP_PROB = 0.2;
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
    Stack<Clause *>::Iterator it(_all);
    while (it.hasNext()) {
      Clause *cl = it.next();
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

  delete _subsIndex;
  _subsIndex = nullptr;
}

void PredicateElimination::registerClause(Clause *cl)
{
  // for each tracked predicate of cl: +1/-1 for a single positive/negative occurrence, 2 for more than one
  static DHMap<unsigned, int> occ;
  occ.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    unsigned pred = lit->functor();
    if (env.signature->getPredicate(pred)->protectedSymbol()) { // includes equality, interpreted and answer predicates
      continue;
    }
    ASS(pred); // equality predicate is protected
    int *val;
    if (occ.getValuePtr(pred, val)) {
      *val = lit->isPositive() ? 1 : -1;
    }
    else {
      *val = 2;
    }
  }

  DHMap<unsigned, int>::Iterator oit(occ);
  while (oit.hasNext()) {
    unsigned pred;
    int val;
    oit.next(pred, val);
    if (val == 2) {
      _preds[pred].blockers++;
    }
    else if (val == 1) {
      _preds[pred].pos.insert(cl);
    }
    else {
      _preds[pred].neg.insert(cl);
    }
  }
}

void PredicateElimination::unregisterClause(Clause *cl)
{
  static DHMap<unsigned, int> occ;
  occ.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
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

  DHMap<unsigned, int>::Iterator oit(occ);
  while (oit.hasNext()) {
    unsigned pred;
    int val;
    oit.next(pred, val);
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
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
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

  Stack<Clause *> posCls;
  Stack<Clause *> negCls;
  {
    DHSet<Clause *>::Iterator pit(_preds[pred].pos);
    while (pit.hasNext()) {
      posCls.push(pit.next());
    }
    DHSet<Clause *>::Iterator nit(_preds[pred].neg);
    while (nit.hasNext()) {
      negCls.push(nit.next());
    }
  }

  if (env.options->showPreprocessing()) {
    cout << "[PP] pel eliminating " << env.signature->predicateName(pred)
         << " (|S_P| = " << posCls.size() << ", |S_~P| = " << negCls.size() << ")" << endl;
  }

  // record the model-repairing definition while S_P is still at hand
  recordElimination(prb, pred, posCls, negCls);

  Stack<Clause *> resolvents;
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
    unregisterClause(cl);
    if (_useSubsumption) {
      indexRemove(cl);
    }
    _deleted.insert(cl);
  }
  for (Clause *cl : negCls) {
    unregisterClause(cl);
    if (_useSubsumption) {
      indexRemove(cl);
    }
    _deleted.insert(cl);
  }
  _curTotal -= posCls.size() + negCls.size();

  for (Clause *r : resolvents) {
    _all.push(r);
    registerClause(r);
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

  static Stack<Literal *> lits;
  lits.reset();
  for (unsigned i = 0; i < c->length(); i++) {
    Literal *lit = (*c)[i];
    if (lit != plitC) {
      lits.push(subst.apply(lit, 0));
    }
  }
  for (unsigned i = 0; i < d->length(); i++) {
    Literal *lit = (*d)[i];
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

  static Stack<Literal *> lits;
  lits.reset();
  for (unsigned i = 0; i < c->length(); i++) {
    Literal *lit = (*c)[i];
    if (lit != plitC) {
      lits.push(lit);
    }
  }
  for (unsigned i = 0; i < d->length(); i++) {
    Literal *lit = (*d)[i];
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
      TermList a0 = *l->nthArgument(0);
      TermList a1 = *l->nthArgument(1);
      if (a0 == a1) { // t != t is simply false
        swap(lits[idx], lits.top());
        lits.pop();
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
      swap(lits[idx], lits.top());
      lits.pop();
      SingleVarApplicator app{var.var(), tgt};
      for (unsigned j = 0; j < lits.size(); j++) {
        lits[j] = SubstHelper::apply(lits[j], app);
      }
      changed = true;
      break;
    }
  }

  return assembleClause(lits, c, d);
}

Clause *PredicateElimination::assembleClause(Stack<Literal *> &lits, Clause *c, Clause *d)
{
  static DHSet<Literal *> seen;
  seen.reset();

  static Stack<Literal *> out;
  out.reset();

  bool keptDiseq = false;
  bool keptVarVarDiseq = false;

  for (unsigned i = 0; i < lits.size(); i++) {
    Literal *l = lits[i];
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
                                             Stack<Clause *> const &posCls, Stack<Clause *> const &negCls)
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
  Stack<Clause *>::ConstIterator cit(posCls);
  while (cit.hasNext()) {
    Clause *c = cit.next();
    Literal *plit = findPredLiteral(c, pred, true);

    FormulaList *conjuncts = FormulaList::empty();
    for (unsigned i = 0; i < ar; i++) {
      FormulaList::push(new AtomicFormula(Literal::createEquality(true,
                                                                  TermList::var(i),
                                                                  SubstHelper::apply(*plit->nthArgument(i), shift),
                                                                  SortHelper::getArgSort(plit, i))),
                        conjuncts);
    }
    for (unsigned i = 0; i < c->length(); i++) {
      Literal *lit = (*c)[i];
      if (lit != plit) {
        FormulaList::push(new AtomicFormula(
                              Literal::complementaryLiteral(SubstHelper::apply(lit, shift))),
                          conjuncts);
      }
    }
    Formula *inner = JunctionFormula::generalJunction(AND, conjuncts);

    // existentially close over the (shifted) clause variables
    DHMap<unsigned, TermList> varSorts;
    SortHelper::collectVariableSorts(inner, varSorts);
    VSList *vs = VSList::empty();
    DHMap<unsigned, TermList>::Iterator vit(varSorts);
    while (vit.hasNext()) {
      unsigned var;
      TermList sort;
      vit.next(var, sort);
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

// a port of ForwardSubsumptionAndResolution::perform to our single-index setting
// (unit and multi-literal clauses share one tree, distinguished by their length)
bool PredicateElimination::forwardSubsumedOrResolved(Clause *cl, Clause *&replacement)
{
  ASS(_useSubsumption);
  ASS(!replacement);

  static DHSet<Clause *> checked; // shared by both passes below, as in FSAR
  checked.reset();

  Clause *conclusion = nullptr;

  // pass 1: subsumption (and cheap subsumption resolution setup on the side)
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    auto rit = _subsIndex->getGeneralizations(lit, /*complementary=*/false, /*retrieveSubstitutions=*/false);
    while (rit.hasNext()) {
      Clause *mcl = rit.next().data->clause;
      if (!checked.insert(mcl)) {
        continue;
      }
      if (mcl->length() == 1) {
        return true; // a unit generalization subsumes outright
      }
      bool checkS = mcl->length() <= cl->length();
      bool checkSR = !conclusion;
      if (checkS && _satSubs.checkSubsumption(mcl, cl, /*setSR=*/checkSR)) {
        return true;
      }
      if (checkSR) {
        // subsumption is preferred, so just remember the conclusion and keep scanning
        conclusion = _satSubs.checkSubsumptionResolution(mcl, cl, /*forward=*/true, /*usePreviousSetUp=*/checkS);
      }
    }
  }

  if (conclusion) {
    replacement = conclusion;
    return false;
  }

  // pass 2: subsumption resolution against complementary matches
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    auto rit = _subsIndex->getGeneralizations(lit, /*complementary=*/true, /*retrieveSubstitutions=*/false);
    while (rit.hasNext()) {
      Clause *mcl = rit.next().data->clause;
      if (mcl->length() == 1) { // the resolved literal is lit itself, no need to involve the SAT solver
        replacement = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, lit, mcl, /*forward=*/true);
        return false;
      }
      if (!checked.insert(mcl)) {
        continue;
      }
      conclusion = _satSubs.checkSubsumptionResolution(mcl, cl, /*forward=*/true, /*usePreviousSetUp=*/false);
      if (conclusion) {
        replacement = conclusion;
        return false;
      }
    }
  }

  return false;
}

void PredicateElimination::indexInsert(Clause *cl)
{
  ASS(_useSubsumption);

  if (cl->length() == 0) {
    return; // the empty clause subsumes everything, but saturation will pick it up immediately anyway
  }
  Literal *key = (cl->length() == 1) ? (*cl)[0] : LiteralByMatchability::find_least_matchable_in(cl).lit();
  ALWAYS(_indexedKey.insert(cl, key));
  _subsIndex->insert(LiteralClause{key, cl});
}

void PredicateElimination::indexRemove(Clause *cl)
{
  ASS(_useSubsumption);

  Literal *key;
  if (_indexedKey.pop(cl, key)) {
    _subsIndex->remove(LiteralClause{key, cl});
  }
}

} // namespace Shell

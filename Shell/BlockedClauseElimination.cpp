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
 * @file BlockedClauseElimination.cpp
 * Implements class Blocked Clause Elimination.
 */

#include "BlockedClauseElimination.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Indexing/TermSharing.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/Random.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/IntUnionFind.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Property.hpp"
#include "Shell/Options.hpp"

namespace Shell
{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;

void BlockedClauseElimination::apply(Problem& prb)
{
  TIME_TRACE("blocked clause elimination");

  bool modified = false;
  bool equationally = _forceEquationally || (prb.hasEquality() && prb.getProperty()->positiveEqualityAtoms());

  DArray<Stack<Candidate*>> positive(env.signature->predicates());
  DArray<Stack<Candidate*>> negative(env.signature->predicates());

  Stack<ClWrapper*> wrappers; // just to delete easily in the end

  // put the clauses into the index
  UnitList::Iterator uit(prb.units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS(u->isClause());
    Clause* cl=static_cast<Clause*>(u);

    ClWrapper* clw = new ClWrapper(cl);
    wrappers.push(clw);

    if (_useSubsumption) {
      indexInsert(clw);
    }

    for(unsigned i=0; i<cl->length(); i++) {
      Literal* lit = (*cl)[i];
      unsigned pred = lit->functor();
      if (!env.signature->getPredicate(pred)->protectedSymbol()) { // don't index on interpreted or otherwise protected predicates (=> the cannot be ``flipped'')
        ASS(pred); // equality predicate is protected

        (lit->isPositive() ? positive : negative)[pred].push(new Candidate(clw,i));
      }
    }
  }

  // cout << "Clauses indexed" << endl;

  typedef BinaryHeap<Candidate*, CandidateComparator> BlockClauseCheckPriorityQueue;
  BlockClauseCheckPriorityQueue queue;

  for (bool isPos : {false, true}) {
    DArray<Stack<Candidate*>>& one   = isPos ? positive : negative;
    DArray<Stack<Candidate*>>& other = isPos ? negative : positive;

    for (unsigned pred = 1; pred < one.size(); pred++) { // skipping 0, the empty slot for equality
      Stack<Candidate*>& predsCandidates = one[pred];
      unsigned predsRemaining = other[pred].size();
      for (unsigned i = 0; i < predsCandidates.size(); i++) {
        Candidate* cand = predsCandidates[i];
        cand->weight = predsRemaining;
        queue.insert(cand);
      }
    }
  }

  // cout << "Queue initialized" << endl;

  // under randomized preprocessing, each discovered blocking is with this probability
  // ignored: the candidate is dropped and never re-enqueued, so the clause can only
  // still get blocked via one of its other literals (the loss is monotone; to be tuned)
  constexpr double RPR_SKIP_PROB = 0.1;
  bool rpr = env.options->randomizedPreprocessing();

  RobSubstitution substMain; // holds the mgu of the two resolved literals, for buildResolvent to reuse

  while (!queue.isEmpty()) {
    Candidate* cand = queue.pop();
    ClWrapper* clw = cand->clw;

    if (clw->blocked) {
      continue;
    }

    // clause still undecided
    Clause* cl = clw->cl;
    Literal* lit = (*cl)[cand->litIdx];
    unsigned pred = lit->functor();
    Stack<Candidate*>& partners = (lit->isPositive() ? negative : positive)[pred];

    // The clause set only ever shrinks, and it only changes at the very end of a successful
    // scan. So a partner cleared by tautologyhood (or by already being blocked) stays cleared
    // forever, while one cleared by its resolvent being subsumed stays cleared only as long as
    // the subsumer is around. Hence the scan may not skip, via contFrom, over a partner cleared
    // by subsumption in an earlier, interrupted scan -- it has to redo those checks against the
    // current clause set. Conversely, a scan which does run to the end has just now, without
    // anything getting blocked in between, verified every one of its subsumption clearings.
    unsigned firstBySubsumption = partners.size();

    for (unsigned i = cand->contFrom; i < partners.size(); i++) {
      Candidate* partner = partners[i];
      ClWrapper* pclw = partner->clw;

      // don't need to check blockedness with itself
      if (pclw == clw) {
        continue;
      }

      if (pclw->blocked) {
        continue;
      }

      bool bySubsumption;
      if (!clearedBy(equationally,substMain,cand,partner,bySubsumption)) {
        // cand does not work, because of partner; need to wait for the partner to die
        cand->contFrom = min(i+1,firstBySubsumption);
        cand->weight = partners.size() - cand->contFrom;
        pclw->toResurrect.push(cand);
        goto next_candidate;
      }
      if (bySubsumption && i < firstBySubsumption) {
        firstBySubsumption = i;
      }
    }

    // resolves to tautology (or something subsumed) with all partners -- blocked!
    if (rpr && Random::getDouble(0.0,1.0) < RPR_SKIP_PROB) {
      goto next_candidate;
    }
    if (env.options->showPreprocessing()) {
      cout << "[PP] Blocked clause[" << cand->litIdx << "]: " << cl->toString() << endl;
    }
    prb.addEliminatedBlockedClause(cl,cand->litIdx);

    env.statistics->blockedClauses++;
    if (firstBySubsumption < partners.size()) {
      env.statistics->blockedClausesBySubsumption++;
    }
    modified = true;

    clw->blocked = true;
    if (clw->indexed) {
      indexRemove(clw);
    }
    for (unsigned i = 0; i< clw->toResurrect.size(); i++) {
      queue.insert(clw->toResurrect[i]);
    }
    clw->toResurrect.reset();

    next_candidate: ;
  }

  // delete candidates:
  for (bool isPos : {false, true}) {
    DArray<Stack<Candidate*>> & one   = isPos ? positive : negative;

    for (unsigned pred = 0; pred < one.size(); pred++) {
      Stack<Candidate*>& predsCandidates = one[pred];
      for (unsigned i = 0; i < predsCandidates.size(); i++) {
        delete predsCandidates[i];
      }
    }
  }

  // delete wrappers and update units in prob, if there were any blockings
  UnitList* res=0;

  Stack<ClWrapper*>::Iterator it(wrappers);
  while (it.hasNext()) {
    ClWrapper* clw = it.next();
    if (modified && !clw->blocked) {
      UnitList::push(clw->cl, res);
    }
    delete clw;
  }

  if (modified) {
    prb.units() = res;
    prb.invalidateProperty();
  }
}

bool BlockedClauseElimination::resolvesToTautology(bool equationally, RobSubstitution& subst, Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  if (equationally) {
    return resolvesToTautologyEq(cl,lit,pcl,plit);
  } else {
    return resolvesToTautologyUn(subst,cl,lit,pcl,plit);
  }
}

bool BlockedClauseElimination::clearedBy(bool equationally, RobSubstitution& subst, Candidate* cand, Candidate* partner, bool& bySubsumption)
{
  bySubsumption = false;

  Clause* cl = cand->clw->cl;
  Literal* lit = (*cl)[cand->litIdx];
  Clause* pcl = partner->clw->cl;
  Literal* plit = (*pcl)[partner->litIdx];

  if (resolvesToTautology(equationally,subst,cl,lit,pcl,plit)) {
    return true;
  }

  if (!_useSubsumption) {
    return false;
  }

  bool tautology = false;
  Clause* resolvent;
  {
    TIME_TRACE("bce resolvent construction");
    resolvent = equationally ?
      buildResolventEq(cl,cand->litIdx,pcl,partner->litIdx,tautology) :
      buildResolventUn(subst,cl,cand->litIdx,pcl,partner->litIdx,tautology);
  }
  if (!resolvent) {
    if (tautology && equationally) {
      // not something resolvesToTautologyEq could establish: it normalizes differently
      env.statistics->bceFlatResolventTautologies++;
    }
    return tautology;
  }

  bool subsumed;
  {
    TIME_TRACE("bce subsumption");
    // cl is the clause we are about to remove, so it may not justify its own removal
    // (any other clause of the set will do, the partner pcl included)
    subsumed = subsumedBy(resolvent,cl);
  }
  resolvent->destroy();

  // NB: only a subsumption clearing is reported back, tautologyhood being independent
  // of the clause set and thus safe for contFrom to skip over on a later scan
  bySubsumption = subsumed;
  return subsumed;
}

/**
 * Every literal of the resolvent must be one which is guaranteed false in the model repair
 * scenario the blockedness argument runs (a model of the current clause set minus cl, under
 * which cl's instance is false, so that lit gets flipped to true and some partner instance
 * might break). On cl's side that is every literal, cl's instance being false as a whole.
 * On pcl's side it is every literal *except* those which could be the resolved literal itself:
 * those are exactly the ones the flip falsifies, and are true before it. Dropping just the
 * plitIdx-th occurrence is not enough -- another literal can coincide with plit(subst) under a
 * further instantiation, and is then true, too. So drop everything unifiable with it, which is
 * the very same rule the subst_aux guard in resolvesToTautologyUn enforces.
 */
static bool couldBeTheResolvedLiteral(RobSubstitution& subst_aux, Literal* resolved, Literal* l)
{
  if (l->functor() != resolved->functor() || l->polarity() != resolved->polarity()) {
    return false;
  }
  subst_aux.reset();
  return subst_aux.unifyArgs(resolved,0,l,0);
}

Clause* BlockedClauseElimination::buildResolventUn(RobSubstitution& subst, Clause* cl, unsigned litIdx, Clause* pcl, unsigned plitIdx, bool& tautology)
{
  static RobSubstitution subst_aux;

  // plit under the mgu, i.e. the literal resolution removes from pcl
  Literal* resolved = subst.apply((*pcl)[plitIdx],1);

  static LiteralStack lits;
  lits.reset();

  for (unsigned bank = 0; bank < 2; bank++) {
    Clause* c = bank ? pcl : cl;

    for (unsigned i = 0; i < c->length(); i++) {
      if (!bank && i == litIdx) {
        continue;
      }
      Literal* l = subst.apply((*c)[i],bank);
      if (bank && couldBeTheResolvedLiteral(subst_aux,resolved,l)) {
        continue;
      }
      lits.push(l);
    }
  }

  return assembleResolvent(lits,tautology);
}

Clause* BlockedClauseElimination::buildResolventEq(Clause* cl, unsigned litIdx, Clause* pcl, unsigned plitIdx, bool& tautology)
{
  Literal* lit = (*cl)[litIdx];
  Literal* plit = (*pcl)[plitIdx];
  ASS_EQ(lit->arity(),plit->arity()); // the same predicate; and no type arguments, see below

  static LiteralStack lits;
  lits.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    if (i != litIdx) {
      lits.push((*cl)[i]);
    }
  }

  // pcl gets a variable range of its own, disjoint from cl's. As in buildResolventUn, every
  // literal which could be the resolved one has to go, not just the plitIdx-th occurrence --
  // only here "could coincide with plit" is meant modulo the model's equality, which no
  // syntactic test approximates, so the whole predicate/polarity class goes. That is exactly
  // the filter resolvesToTautologyEq applies to pcl, which is thus a soundness requirement
  // rather than the conservatism it looks like.
  VarShiftApplicator shift{cl->maxVar()+1};
  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* l = (*pcl)[i];
    if (l->functor() != plit->functor() || l->polarity() != plit->polarity()) {
      lits.push(SubstHelper::apply(l,shift));
    }
  }

  // this is where the "virtual flattening" happens. Note we are monomorphic here (_useSubsumption
  // is switched off for polymorphic and higher-order inputs), so arity() counts no type arguments
  // and the two arguments of each equality are guaranteed to have the same sort
  for (unsigned i = 0; i < lit->arity(); i++) {
    lits.push(Literal::createEquality(false,
                                      *lit->nthArgument(i),
                                      SubstHelper::apply(*plit->nthArgument(i),shift),
                                      SortHelper::getArgSort(lit,i)));
  }

  EqHelper::equalityResolutionWithDeletion(lits);

  return assembleResolvent(lits,tautology);
}

Clause* BlockedClauseElimination::assembleResolvent(LiteralStack& lits, bool& tautology)
{
  ASS(!tautology);

  static DHSet<Literal*, FnvHash, PtrIdentityHash> seen;
  seen.reset();

  static LiteralStack out;
  out.reset();

  for (const auto& l : lits) {
    if (EqHelper::isEqTautology(l)) { // s = s
      tautology = true;
      return nullptr;
    }
    // the complementary pair conditions in resolvesToTautologyUn are deliberately
    // conservative (c.f. the opslit business there), so this can genuinely fire
    if (seen.find(Literal::complementaryLiteral(l))) {
      tautology = true;
      return nullptr;
    }
    if (l->isEquality() && l->isNegative() && *l->nthArgument(0) == *l->nthArgument(1)) {
      continue; // t != t is simply false
    }
    if (seen.insert(l)) {
      out.push(l);
    }
  }

  if (out.isEmpty()) {
    return nullptr;
  }

  // the clause is a throwaway query for the index, so it does not record its actual parents
  // (which would make destroying it decrease their reference counts)
  return Clause::fromStack(out,FromInput(UnitInputType::AXIOM));
}

// a cousin of PredicateElimination::forwardSubsumedOrResolved: the code tree indexes whole
// clauses and performs the multi-literal matching for us. Subsumption resolution is off here:
// we need a clause implying the resolvent, not a way of strengthening it.
bool BlockedClauseElimination::subsumedBy(Clause* resolvent, Clause* exclude)
{
  ASS(_useSubsumption);
  ASS(resolvent->length() > 0);

  if (_ct.isEmpty()) { // ClauseMatcher::init asserts on this
    return false;
  }

  static ClauseCodeTree<false>::ClauseMatcher cm;
  cm.init(&_ct,resolvent,/*sres=*/false);

  bool res = false;
  Clause* premise;
  int resolvedQueryLit;
  while ((premise = cm.next(resolvedQueryLit))) {
    ASS_EQ(resolvedQueryLit,-1); // sres is off
    if (premise != exclude) {
      res = true;
      break;
    }
  }
  cm.reset();

  return res;
}

void BlockedClauseElimination::indexInsert(ClWrapper* clw)
{
  ASS(_useSubsumption);
  ASS(!clw->indexed);

  Clause* cl = clw->cl;

  if (cl->length() == 0) {
    return; // the empty clause subsumes everything, but then the problem is refuted anyway
  }

  // a duplicate literal would violate an invariant of the multi-literal matching in
  // ClauseCodeTree (in saturation, maintained by simplifying every new clause); a tautology
  // can never be a useful subsumer, as the resolvent would then be a tautology too
  static DHSet<Literal*, FnvHash, PtrIdentityHash> seen;
  seen.reset();
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* l = (*cl)[i];
    if (EqHelper::isEqTautology(l) || seen.find(Literal::complementaryLiteral(l)) || !seen.insert(l)) {
      return;
    }
  }

  if (!_indexed.insert(cl)) {
    return; // the same clause object listed twice; the index must stay a set
  }

  _ct.insert(cl);
  clw->indexed = true;
}

void BlockedClauseElimination::indexRemove(ClWrapper* clw)
{
  ASS(_useSubsumption);
  ASS(clw->indexed);

  _ct.remove(clw->cl);
  _indexed.remove(clw->cl);
  clw->indexed = false;
}

class VarMaxUpdatingNormalizer : public TermTransformer {
public:
  VarMaxUpdatingNormalizer(const Lib::DHMap<TermList, TermList>& replacements, int& varMax)
    : _repls(replacements), _varMax(varMax) {}
protected:
  TermList transformSubterm(TermList trm) override {
    TermList res;
    if (_repls.find(trm,res)) {
      return res;
    }
    if (trm.isVar()) {
      int var = trm.var();
      if (var > _varMax) {
        _varMax = var;
      }
    }
    return trm;
  }
private:
  const Lib::DHMap<TermList, TermList>& _repls;
  int& _varMax;
};

class RenanigApartNormalizer : public TermTransformer {
public:
  RenanigApartNormalizer(const Lib::DHMap<TermList, TermList>& replacements, int varMax, Lib::DHMap<unsigned, unsigned, FnvHash, IdentityHash>& varMap)
    : _repls(replacements), _varMax(varMax), _varMap(varMap) {}
protected:
  TermList transformSubterm(TermList trm) override {
    TermList res;
    if (_repls.find(trm,res)) {
      return res;
    }
    if (trm.isVar()) {
      unsigned varIn = trm.var();
      unsigned* varOut;
      if (_varMap.getValuePtr(varIn,varOut)) {
        *varOut = ++_varMax;
      }
      return TermList(*varOut,false);
    }
    return trm;
  }
private:
  const Lib::DHMap<TermList, TermList>& _repls;
  int _varMax;
  Lib::DHMap<unsigned, unsigned, FnvHash, IdentityHash>& _varMap;
};


bool BlockedClauseElimination::resolvesToTautologyEq(Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  // With polymorphism, some intermediate terms created here are not well sorted, but that's OK
  TermSharing::WellSortednessCheckingLocalDisabler disableInScope(env.sharing);
  // cout << "cl: " << cl->toString() << endl;
  // cout << "lit: " << lit->toString() << endl;
  // cout << "pcl: " << pcl->toString() << endl;
  // cout << "plit: " << plit->toString() << endl;

  ASS_EQ(lit->arity(),plit->arity());

  unsigned n = lit->arity();

  IntUnionFind uf(n ? 2*n : 1); // IntUnionFind does not like 0
  static Lib::DHMap<TermList, unsigned>  litArgIds;
  litArgIds.reset();
  static Lib::DHMap<TermList, unsigned> plitArgIds;
  plitArgIds.reset();

  int varMax = -1;

  for(unsigned i = 0; i<n; i++) {
    TermList arg = *lit->nthArgument(i);

    // computing varMax of cl's literals -- first in lit
    TermIterator vit = Term::getVariableIterator(arg);
    while (vit.hasNext()) {
      TermList vt = vit.next();
      ASS(vt.isVar());
      int var = vt.var();
      if (var > varMax) {
        varMax = var;
      }
    }

    // "unify" identical arguments' ids
    unsigned id1 = i;
    unsigned id2 = litArgIds.findOrInsert(arg,id1);
    if (id1 != id2) {
      uf.doUnion(id1,id2);
    }
  }

  for(unsigned i = 0; i<n; i++) {
    TermList arg = *plit->nthArgument(i);

    // "unify" identical arguments' ids
    unsigned id1 = n+i;
    unsigned id2 = plitArgIds.findOrInsert(arg,id1);
    if (id1 != id2) {
      uf.doUnion(id1,id2);
    }

    // also do the actual "unification" between lit and plit
    uf.doUnion(i,id1);
  }

  // to do replacements in cl, we need a mapping for all lit's arguments.
  // As a bonus we also allow ground arguments of plit
  static Lib::DHMap<TermList, TermList> replacements;
  replacements.reset();
  for(unsigned i = 0; i<n; i++) {
    TermList arg = *lit->nthArgument(i);
    unsigned id1 = i;
    unsigned id2 = uf.root(id1);
    ASS_L(id2,n);
    TermList target = *lit->nthArgument(id2);
    replacements.insert(arg,target);
  }

  for(unsigned i = 0; i<n; i++) {
    TermList arg = *plit->nthArgument(i);
    if (arg.isTerm() && arg.term()->ground()) {
      unsigned id1 = n+i;
      unsigned id2 = uf.root(id1);
      ASS_L(id2,n);
      TermList target = *lit->nthArgument(id2);
      replacements.insert(arg,target);
    }
  }

  VarMaxUpdatingNormalizer clNormalizer(replacements,varMax);

  static DHSet<Literal*, FnvHash, PtrIdentityHash> norm_lits;
  norm_lits.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curlit = (*cl)[i];

    if (curlit->functor() != lit->functor() || curlit->polarity() != lit->polarity()) {
      Literal* ncurlit = clNormalizer.transformLiteral(curlit);
      Literal* opncurlit = Literal::complementaryLiteral(ncurlit);

      if (norm_lits.find(opncurlit)) {
        return true;
      }

      if (EqHelper::isEqTautology(ncurlit)) {
        return true;
      }

      norm_lits.insert(ncurlit);
    }
  }

  //cout << "varMax: " << varMax << endl;

  // to do replacements in pcl, we need a mapping for all plit's arguments.
  replacements.reset();
  for(unsigned i = 0; i<n; i++) {
    TermList arg = *plit->nthArgument(i);
    unsigned id1 = n+i;
    unsigned id2 = uf.root(id1);
    ASS_L(id2,n);
    TermList target = *lit->nthArgument(id2);
    replacements.insert(arg,target);
  }

  // As a bonus we also allow ground arguments of lit
  for(unsigned i = 0; i<n; i++) {
    TermList arg = *lit->nthArgument(i);
    if (arg.isTerm() && arg.term()->ground()) {
      unsigned id1 = i;
      unsigned id2 = uf.root(id1);
      ASS_L(id2,n);
      TermList target = *lit->nthArgument(id2);
      replacements.insert(arg,target);
    }
  }

  static Lib::DHMap<unsigned, unsigned, FnvHash, IdentityHash> varMap;
  varMap.reset();
  RenanigApartNormalizer pclNormalizer(replacements,varMax,varMap);

  static DHSet<Literal*, FnvHash, PtrIdentityHash> pcl_lits;
  pcl_lits.reset();

  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* curlit = (*pcl)[i];

    if (curlit->functor() != plit->functor() || curlit->polarity() != plit->polarity()) {
      Literal* ncurlit = pclNormalizer.transformLiteral(curlit);
      Literal* opncurlit = Literal::complementaryLiteral(ncurlit);

      if (norm_lits.find(opncurlit)) {
        return true;
      }

      if (EqHelper::isEqTautology(ncurlit)) {
        return true;
      }

      norm_lits.insert(ncurlit);
    }
  }

  return false;
};


/* The solution with
 * DP::SimpleCongruenceClosure _cc;
 * was too expensive computationally:

struct TimesTwo {
  static TermList apply(unsigned var) {
    return TermList(2*var,false);
  }
};

struct TimesTwoPlusOne {
  static TermList apply(unsigned var) {
    return TermList(2*var+1,false);
  }
};

bool BlockedClauseElimination::resolvesToTautologyEq(Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  _cc.reset();

  // cout << "cl: " << cl->toString() << endl;
  // cout << "lit: " << lit->toString() << endl;
  // cout << "pcl: " << pcl->toString() << endl;
  // cout << "plit: " << plit->toString() << endl;

  // two variable normalizers:
  TimesTwo timesTwo;
  TimesTwoPlusOne timesTwoPlusOne;

  // insert complements of literals from cl, except those that could look like lit
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curlit = (*cl)[i];
    if (curlit->functor() != lit->functor() || curlit->polarity() != lit->polarity()) {
      Literal* oplit = Literal::complementaryLiteral(curlit);

      Literal* norm_oplit = SubstHelper::apply(oplit,timesTwo);

      // cout << "norm_oplit1: " << norm_oplit->toString() << endl;

      _cc.addLiteral(norm_oplit);
    }
  }

  // insert complements of literals from pcl, except those that could look like plit
  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* curlit = (*pcl)[i];
    if (curlit->functor() != plit->functor() || curlit->polarity() != plit->polarity()) {
      Literal* oplit = Literal::complementaryLiteral(curlit);

      Literal* norm_oplit = SubstHelper::apply(oplit,timesTwoPlusOne);

      // cout << "norm_oplit2: " << norm_oplit->toString() << endl;

      _cc.addLiteral(norm_oplit);
    }
  }

  // insert equalities describing the unifier
  ASS_EQ(lit->functor(),plit->functor());
  ASS_NEQ(lit->polarity(),plit->polarity());

  for(unsigned i = 0; i<lit->arity(); i++) {
    unsigned sort = SortHelper::getArgSort(lit,i);
    ASS_EQ(sort,SortHelper::getArgSort(plit,i));
    TermList left = SubstHelper::apply(*lit->nthArgument(i),timesTwo);
    TermList right = SubstHelper::apply(*plit->nthArgument(i),timesTwoPlusOne);

    Literal* eqLit = Literal::createEquality(true,left,right,sort);

    // cout << "eqLit: " << eqLit->toString() << endl;

    _cc.addLiteral(eqLit);
  }

  // is there a conflict?
  return (_cc.getStatus(false) == DP::DecisionProcedure::UNSATISFIABLE);
}
*/

// when this returns false, subst_main is left holding the mgu of lit and plit,
// which buildResolvent then uses to assemble the resolvent for the subsumption check
bool BlockedClauseElimination::resolvesToTautologyUn(RobSubstitution& subst_main, Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  // cout << "cl: " << cl->toString() << endl;
  // cout << "pcl: " << pcl->toString() << endl;
  // cout << "lit: " << lit->toString() << endl;
  // cout << "plit: " << plit->toString() << endl;

  subst_main.reset();
  if(!subst_main.unifyArgs(lit,0,plit,1)) {
    return true; // since they don't resolve
  }

  static DHSet<Literal*, FnvHash, PtrIdentityHash> cl_lits;
  cl_lits.reset();

  Literal* opslit = 0;

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curlit = (*cl)[i];
    Literal* scurlit = subst_main.apply(curlit,0);
    Literal* opscurlit = Literal::complementaryLiteral(scurlit);

    if (curlit == lit) {
      opslit = opscurlit;
    }

    if (cl_lits.find(opscurlit)) { // cl(subst_main) is a tautology
      return true;
    }
    cl_lits.insert(scurlit);

    // cout << "insert1(scurlit): " << scurlit->toString() << endl;
  }

  // cout << "opslit: " << opslit->toString() << endl;

  ASS_NEQ(opslit,0);

  static DHSet<Literal*, FnvHash, PtrIdentityHash> pcl_lits;
  pcl_lits.reset();

  static RobSubstitution subst_aux;
  subst_aux.reset();

  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* curlit = (*pcl)[i];
    Literal* scurlit = subst_main.apply(curlit,1);
    Literal* opscurlit = Literal::complementaryLiteral(scurlit);

    if (pcl_lits.find(opscurlit)) { // pcl(subst_main) is a tautology
      return true;
    }
    pcl_lits.insert(scurlit);

    // cout << "insert2(scurlit): " << scurlit->toString() << endl;

    if (curlit != plit && cl_lits.find(opscurlit)) {
      if (opslit->functor() != scurlit->functor() || !subst_aux.unifyArgs(opslit,0,scurlit,0)) { // opslit is the same thing as plit(subst_main)
        return true;
      } else {
        subst_aux.reset();
      }
    }
  }

  return false;
}

}

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
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Indexing/TermSharing.hpp"

#include "Lib/SmartPtr.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/IntUnionFind.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Property.hpp"
#include "Shell/Options.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

void BlockedClauseElimination::apply(Problem& prb)
{
  CALL("BlockedClauseElimination::apply(Problem&)");

  TimeCounter tc(TC_BCE);

  bool modified = false;
  bool equationally = prb.hasEquality() && prb.getProperty()->positiveEqualityAtoms();

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

    for(unsigned i=0; i<cl->length(); i++) {
      Literal* lit = (*cl)[i];
      unsigned pred = lit->functor();
      if (!env.signature->getPredicate(pred)->protectedSymbol()) { // don't index on interpreted or otherwise protected predicates (=> the cannot be ``flipped'')
        ASS(pred); // equality predicate is protected

        (lit->isPositive() ? positive : negative)[pred].push(new Candidate {clw,i,0,0});
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

    for (unsigned i = cand->contFrom; i < partners.size(); i++) {
      Candidate* partner = partners[i];
      ClWrapper* pclw = partner->clw;

      // don't need to check blockedness with itself
      if (pclw == clw) {
        continue;
      }

      Clause* pcl = pclw->cl;

      if (pclw->blocked) {
        continue;
      }

      if (!resolvesToTautology(equationally,cl,lit,pcl,(*pcl)[partner->litIdx])) {
        // cand does not work, because of partner; need to wait for the partner to die
        cand->contFrom = i+1;
        cand->weight = partners.size() - cand->contFrom;
        pclw->toResurrect.push(cand);
        goto next_candidate;
      }
    }

    // resolves to tautology with all partners -- blocked!
    if (env.options->showPreprocessing()) {
      cout << "[PP] Blocked clause[" << cand->litIdx << "]: " << cl->toString() << endl;
    }

    env.statistics->blockedClauses++;
    modified = true;

    clw->blocked = true;
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

bool BlockedClauseElimination::resolvesToTautology(bool equationally, Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  CALL("BlockedClauseElimination::resolvesToTautology");

  if (equationally) {
    return resolvesToTautologyEq(cl,lit,pcl,plit);
  } else {
    return resolvesToTautologyUn(cl,lit,pcl,plit);
  }
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
  RenanigApartNormalizer(const Lib::DHMap<TermList, TermList>& replacements, int varMax, Lib::DHMap<unsigned, unsigned>& varMap)
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
  Lib::DHMap<unsigned, unsigned>& _varMap;
};


bool BlockedClauseElimination::resolvesToTautologyEq(Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  CALL("BlockedClauseElimination::resolvesToTautologyEq");

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

  static DHSet<Literal*> norm_lits;
  norm_lits.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curlit = (*cl)[i];

    if (curlit->functor() != lit->functor() || curlit->polarity() != lit->polarity()) {
      Literal* ncurlit = clNormalizer.transform(curlit);
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

  static Lib::DHMap<unsigned, unsigned> varMap;
  varMap.reset();
  RenanigApartNormalizer pclNormalizer(replacements,varMax,varMap);

  static DHSet<Literal*> pcl_lits;
  pcl_lits.reset();

  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* curlit = (*pcl)[i];

    if (curlit->functor() != plit->functor() || curlit->polarity() != plit->polarity()) {
      Literal* ncurlit = pclNormalizer.transform(curlit);
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
  CALL("BlockedClauseElimination::resolvesToTautologyEq");

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

bool BlockedClauseElimination::resolvesToTautologyUn(Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  CALL("BlockedClauseElimination::resolvesToTautologyUn");

  // cout << "cl: " << cl->toString() << endl;
  // cout << "pcl: " << pcl->toString() << endl;
  // cout << "lit: " << lit->toString() << endl;
  // cout << "plit: " << plit->toString() << endl;

  static RobSubstitution subst_main;
  subst_main.reset();
  if(!subst_main.unifyArgs(lit,0,plit,1)) {
    return true; // since they don't resolve
  }

  static DHSet<Literal*> cl_lits;
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

  static DHSet<Literal*> pcl_lits;
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

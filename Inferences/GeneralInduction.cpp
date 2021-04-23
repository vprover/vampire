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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "Lib/Array.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Shell/InductionSchemeGenerator.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Inferences/BinaryResolution.hpp"

#include "GeneralInduction.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Lib;
using namespace Shell;

ClauseIterator GeneralInduction::generateClauses(Clause* premise)
{
  CALL("GeneralInduction::generateClauses");

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static unsigned maxD = env.options->maxInductionDepth();
  static bool unitOnly = env.options->inductionUnitOnly();

  // auto res = ClauseIterator::getEmpty();
  InductionClauseIterator res;
  if((!unitOnly || premise->length()==1) && 
     (all || ( (goal || goal_plus) && premise->derivedFromGoal())) &&
     (maxD == 0 || premise->inference().inductionDepth() < maxD)
    )
  {
    for(unsigned i=0;i<premise->length();i++){
      process(res, premise, (*premise)[i]);
    }
  }

  return pvi(res);
}

inline bool skolem(TermList t) {
  return !t.isVar() && env.signature->getFunction(t.term()->functor())->skolem();
}

void GeneralInduction::process(InductionClauseIterator& res, Clause* premise, Literal* literal)
{
  CALL("GeneralInduction::process");

  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << *literal << " in " << *premise << endl;
    env.endOutput();
  }

  static bool negOnly = env.options->inductionNegOnly();
  if((!negOnly || literal->isNegative() || 
      (theory->isInterpretedPredicate(literal) && theory->isInequality(theory->interpretPredicate(literal)))
    ) && literal->ground())
  {
    SLQueryResult qr(literal, premise);
    vset<pair<Literal*,Clause*>> sides;
    vset<TermList> skolems;
    SubtermIterator stit(literal);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (skolem(st)) {
        skolems.insert(st);
      }
    }
    unsigned sigMain;
    bool hypMain, revMain;
    qr.clause->isInductionLiteral(qr.literal, sigMain, hypMain, revMain);
    for (const auto& sk : skolems) {
      auto it = _index->getGeneralizations(sk);
      while (it.hasNext()) {
        auto sqr = it.next();
        unsigned sig;
        bool hyp, rev;
        if (qr.literal != sqr.literal &&
            qr.clause != sqr.clause &&
            !sqr.clause->isInductionLiteral(sqr.literal, sig, hyp, rev) &&
            //sqr.literal->isPositive() &&
            sqr.literal->ground() &&
            (sqr.clause->inference().inductionDepth() == 0 ||
            (sig == sigMain && hyp && !hypMain))) {
          // cout << *sqr.literal << " " << *sqr.clause << endl;
          sides.emplace(sqr.literal, sqr.clause);
        }
      }
    }

    // StructuralInductionSchemeGenerator gen;
    RecursionInductionSchemeGenerator2 gen;
    static vvector<pair<InductionScheme, OccurrenceMap>> schOccMap;
    schOccMap.clear();
    gen.generate(qr, sides, schOccMap);
    static vvector<pair<InductionScheme, OccurrenceMap>> generalizedSchOccMap;
    generalizedSchOccMap.clear();
    vvector<Literal*> schLits;
    for (const auto& kv : schOccMap) {
      schLits.push_back(nullptr);
      if (alreadyDone(literal, kv.first, schLits.back())) {
        continue;
      }
      // InductionGeneralizationIterator g(kv.second);
      HeuristicGeneralizationIterator g(kv.second);
      while (g.hasNext()) {
        auto eg = g.next();
        generalizedSchOccMap.push_back(make_pair(kv.first, eg));
      }
    }
    for (const auto& schLit : schLits) {
      _done.insert(schLit);
    }
    for (const auto& kv : generalizedSchOccMap) {
      generateClauses(kv.first, kv.second, qr, sides, res._clauses);
    }
  }
}

void GeneralInduction::attach(SaturationAlgorithm* salg)
{
  CALL("GeneralInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _splitter=_salg->getSplitter();
  _index = static_cast<DemodulationSubtermIndex *>(
      _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE));
}

void GeneralInduction::detach()
{
  CALL("GeneralInduction::detach");

  _index = 0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  _splitter=0;
  GeneratingInferenceEngine::detach();
}

Literal* replaceLit(const vmap<TermList,TermList>& r, const OccurrenceMap& occurrences, Literal* lit, const vset<pair<Literal*,Clause*>>& sideLits,
  const vmap<TermList,TermList>& v2sk, const vvector<LiteralStack>& lits, vvector<LiteralStack>& newLits,
  unsigned& var, bool hypothesis = false)
{
  TermOccurrenceReplacement2 tr(r, occurrences, lit);
  auto newLit = tr.transform(lit);
  if (newLit != lit) {
    TermReplacement2 tr2(v2sk);
    newLit = tr2.transform(newLit);
    if (hypothesis) {
      newLit = Literal::complementaryLiteral(newLit);
    }
    for (auto st : lits) {
      st.push(newLit);
      if (hypothesis) {
        for (const auto& kv : sideLits) {
          TermOccurrenceReplacement2 trs(r, occurrences, kv.first);
          auto newLitS = trs.transform(kv.first);
          TermReplacement2 trs2(v2sk);
          newLitS = Literal::complementaryLiteral(trs2.transform(newLitS));
          st.push(newLitS);
        }
      }
      newLits.push_back(st);
    }
  }
  return newLit;
}

void GeneralInduction::generateClauses(
  const Shell::InductionScheme& scheme,
  const OccurrenceMap& occurrences,
  const SLQueryResult& mainLit,
  const vset<pair<Literal*,Clause*>>& sideLits,
  ClauseStack& clauses)
{
  CALL("GeneralInduction::generateClauses");

  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] generating from scheme " << scheme
              << " with occurrences ";
    for (const auto& kv : occurrences) {
      env.out() << kv.first.second << " " << kv.second.toString() << " in " << *kv.first.first << ", ";
    }
    env.out() << endl;
    env.endOutput();
  }

  unsigned var = scheme._maxVar;
  vvector<LiteralStack> lits(1);
  vmap<Literal*, Literal*> hypToConcMap;
  vmap<Literal*, bool> reversedLitMap;

  for (const auto& c : scheme._cases) {
    vvector<LiteralStack> newLits;

    auto v2sk = skolemizeCase(c);
    auto newMainLit = replaceLit(c._step, occurrences, mainLit.literal, sideLits, v2sk, lits, newLits, var);
    ASS_NEQ(newMainLit, mainLit.literal);
    reversedLitMap.insert(make_pair(newMainLit, newMainLit->isOrientedReversed()));

    for (const auto& kv : sideLits) {
      replaceLit(c._step, occurrences, kv.first, sideLits, v2sk, lits, newLits, var);
    }

    for (const auto& r : c._recursiveCalls) {
      auto newHypLit = replaceLit(r, occurrences, mainLit.literal, sideLits, v2sk, lits, newLits, var, true);
      ASS_NEQ(newHypLit, mainLit.literal);
      reversedLitMap.insert(make_pair(newHypLit, newHypLit->isOrientedReversed()));
      if (env.options->inductionHypRewriting()) {
        hypToConcMap.insert(make_pair(newHypLit, newMainLit));
      }
    }
    lits = newLits;
  }

  vmap<TermList, TermList> r;
  for (const auto& c : scheme._cases) {
    for (const auto& kv : c._step) {
      if (r.count(kv.first) > 0) {
        continue;
      }
      r.insert(make_pair(kv.first, TermList(var++,false)));
    }
  }
  vvector<pair<Literal*, SLQueryResult>> conclusionToLitMap;
  TermOccurrenceReplacement2 tr(r, occurrences, mainLit.literal);
  auto newMainLit = tr.transform(mainLit.literal);
  ASS(mainLit.literal != newMainLit);
  newMainLit = Literal::complementaryLiteral(newMainLit);
  for (auto& st : lits) {
    st.push(newMainLit);
  }
  conclusionToLitMap.push_back(make_pair(newMainLit, mainLit));

  for (const auto& kv : sideLits) {
    TermOccurrenceReplacement2 tr(r, occurrences, kv.first);
    auto newLit = tr.transform(kv.first);
    if (kv.first != newLit) {
      newLit = Literal::complementaryLiteral(newLit);
      for (auto& st : lits) {
        st.push(newLit);
      }
      conclusionToLitMap.push_back(make_pair(newLit, SLQueryResult(kv.first, kv.second)));
    }
  }

  ClauseStack temp;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,_rule);
  unsigned maxDepth = 0;
  for (const auto& kv : conclusionToLitMap) {
    maxDepth = max(maxDepth, kv.second.clause->inference().inductionDepth());
  }
  inf.setInductionDepth(maxDepth+1);
  for (const auto& st : lits) {
    temp.push(Clause::fromStack(st, inf));
  }
  for (const auto& kv : hypToConcMap) {
    auto h = Hash::hash(kv);
    for (auto& c : temp) {
      if (c->contains(kv.first)) {
        c->markInductionLiteral(h, kv.first, true, reversedLitMap[kv.first]);
      }
      if (c->contains(kv.second)) {
        c->markInductionLiteral(h, kv.second, false, reversedLitMap[kv.second]);
      }
    }
  }

  ClauseStack::Iterator cit(temp);
  RobSubstitutionSP subst(new RobSubstitution());
  for (const auto& kv : conclusionToLitMap) {
    auto conclusion = kv.first;
    auto qr = kv.second;
    if (!subst->match(TermList(conclusion), 0, TermList(qr.literal), 1)) {
      ASS_REP(conclusion->isEquality() && qr.literal->isEquality(), conclusion->toString() + qr.literal->toString());
      // direct match did not succeed, so we match one literal with the other reversed
      ALWAYS(subst->match(*kv.first->nthArgument(0), 0, *kv.second.literal->nthArgument(1), 1)
        && subst->match(*kv.first->nthArgument(1), 0, *kv.second.literal->nthArgument(0), 1));
    }
  }
  auto it = conclusionToLitMap.begin();
  it++;
  for (; it != conclusionToLitMap.end(); it++) {
    it->first = subst->apply(it->first, 0);
  }
  auto resSubst = ResultSubstitution::fromSubstitution(subst.ptr(), 0, 1);
  while(cit.hasNext()){
    Clause* c = cit.next();
    unsigned i = 0;
    for (const auto& kv : conclusionToLitMap) {
      auto conclusion = kv.first;
      auto qr = kv.second;
      qr.substitution = resSubst;
      auto store = qr.clause->store();
      qr.clause->setStore(Clause::ACTIVE);
      c = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
      qr.clause->setStore(store);
      ASS(c);
      if (_splitter && ++i < conclusionToLitMap.size()) {
        _splitter->onNewClause(c);
      }
    }
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl;
      env.endOutput();
    }
    clauses.push(c);
  }
  env.statistics->induction++;
}

vmap<TermList, TermList> GeneralInduction::skolemizeCase(const InductionScheme::Case& c)
{
  vmap<TermList, TermList> varToSkolemMap;
  for (auto kv : c._step) {
    DHMap<unsigned,unsigned> varSorts;
    auto sort = SortHelper::getResultSort(kv.first.term());
    SortHelper::collectVariableSorts(kv.second,sort,varSorts);

    auto it = varSorts.items();
    while (it.hasNext()) {
      auto v = it.next();
      TermList var(v.first,false);
      ASS(!varToSkolemMap.count(var));

      auto skFun = Skolem::addSkolemFunction(0,nullptr,v.second);
      varToSkolemMap.insert(make_pair(var, Term::create(skFun, 0, nullptr)));
    }
  }
  return varToSkolemMap;
}

bool GeneralInduction::alreadyDone(Literal* mainLit, const InductionScheme& sch, Literal*& schLit)
{
  CALL("GeneralInduction::alreadyDone");

  static DHMap<pair<unsigned,unsigned>,TermList> blanks;
  vmap<unsigned,unsigned> srts;
  vmap<TermList, TermList> replacements;
  for (const auto& t : sch._inductionTerms) {
    unsigned srt = env.signature->getFunction(t.term()->functor())->fnType()->result();
    auto it = srts.find(srt);
    if (it == srts.end()) {
      it = srts.insert(make_pair(srt,0)).first;
    } else {
      it->second++;
    }
    const auto p = make_pair(srt, it->second);
    if (!blanks.find(p)) {
      unsigned fresh = env.signature->addFreshFunction(0,"blank",to_string(it->second).c_str());
      env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
      TermList blank = TermList(Term::createConstant(fresh));
      blanks.insert(p,blank);
    }
    replacements.insert(make_pair(t, blanks.get(p)));
  }

  TermReplacement2 cr(replacements);
  schLit = cr.transform(mainLit);

  if (_done.contains(schLit)) {
    // cout << *mainLit << " is skipped (" << *rep << ")" << endl;
    return true;
  }
  return false;
}

}
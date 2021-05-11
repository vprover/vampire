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

  auto pairs = selectMainSidePairs(literal, premise);

  for (const auto& kv : pairs) {
    const auto& main = kv.first;
    const auto& sides = kv.second;
    static vvector<pair<InductionScheme, OccurrenceMap>> schOccMap;
    schOccMap.clear();
    RecursionInductionSchemeGenerator gen;
    gen.generate(main, sides, schOccMap);
    vvector<pair<Literal*, vset<Literal*>>> schLits;
    for (const auto& kv : schOccMap) {
      vset<pair<Literal*, Clause*>> sidesFiltered;
      for (const auto& s : sides) {
        bool filter = true;
        for (const auto& indTerm : kv.first.inductionTerms()) {
          if (s.first->containsSubterm(indTerm) && (!skolem(indTerm) || !s.second->inference().inductionDepth())) {
            filter = false;
            break;
          }
        }
        if (!filter) {
          sidesFiltered.insert(s);
        }
      }
      schLits.emplace_back(nullptr, vset<Literal*>());
      if (alreadyDone(literal, sidesFiltered, kv.first, schLits.back())) {
        continue;
      }
      static const bool heuristic = env.options->inductionGenHeur();
      GeneralizationIterator g(kv.second, heuristic);
      while (g.hasNext()) {
        auto eg = g.next();
        generateClauses(kv.first, eg, main, sidesFiltered, res._clauses);
      }
    }
    for (const auto& schLit : schLits) {
      _done.insert(schLit.first, schLit.second);
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
  const vmap<TermList,TermList>& v2sk, const vvector<LiteralStack>& lits, vvector<LiteralStack>& newLits, bool hypothesis = false)
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
          if (newLitS != kv.first) {
            TermReplacement2 trs2(v2sk);
            newLitS = Literal::complementaryLiteral(trs2.transform(newLitS));
            st.push(newLitS);
          }
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

  vvector<LiteralStack> lits(1);
  vmap<Literal*, Literal*> hypToConcMap;
  vmap<Literal*, bool> reversedLitMap;

  for (const auto& c : scheme.cases()) {
    vvector<LiteralStack> newLits;

    auto v2sk = skolemizeCase(c);
    auto newMainLit = replaceLit(c._step, occurrences, mainLit.literal, sideLits, v2sk, lits, newLits);
    ASS_NEQ(newMainLit, mainLit.literal);
    reversedLitMap.insert(make_pair(newMainLit, newMainLit->isOrientedReversed()));

    for (const auto& kv : sideLits) {
      replaceLit(c._step, occurrences, kv.first, sideLits, v2sk, lits, newLits);
    }

    for (const auto& r : c._recursiveCalls) {
      auto newHypLit = replaceLit(r, occurrences, mainLit.literal, sideLits, v2sk, lits, newLits, true);
      ASS_NEQ(newHypLit, mainLit.literal);
      reversedLitMap.insert(make_pair(newHypLit, newHypLit->isOrientedReversed()));
      if (env.options->inductionHypRewriting()) {
        hypToConcMap.insert(make_pair(newHypLit, newMainLit));
      }
    }
    lits = newLits;
  }

  vmap<TermList, TermList> r;
  unsigned var = 0;
  for (const auto& c : scheme.cases()) {
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
  RobSubstitution subst;
  for (const auto& kv : conclusionToLitMap) {
    auto conclusion = kv.first;
    auto qr = kv.second;
    if (!subst.match(TermList(conclusion), 0, TermList(qr.literal), 1)) {
      ASS_REP(conclusion->isEquality() && qr.literal->isEquality(), conclusion->toString() + qr.literal->toString());
      // direct match did not succeed, so we match one literal with the other reversed
      ALWAYS(subst.match(*conclusion->nthArgument(0), 0, *qr.literal->nthArgument(1), 1)
        && subst.match(*conclusion->nthArgument(1), 0, *qr.literal->nthArgument(0), 1));
    }
  }
  auto it = conclusionToLitMap.begin();
  it++;
  for (; it != conclusionToLitMap.end(); it++) {
    it->first = subst.apply(it->first, 0);
  }
  auto resSubst = ResultSubstitution::fromSubstitution(&subst, 0, 1);
  while(cit.hasNext()){
    Clause* c = cit.next();
    unsigned i = 0;
    for (const auto& kv : conclusionToLitMap) {
      auto conclusion = kv.first;
      auto qr = kv.second;
      qr.substitution = resSubst;
      c = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
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

void mapVarsToSkolems(vmap<TermList, TermList>& varToSkolemMap, pair<TermList, TermList> kv) {
  DHMap<unsigned,unsigned> varSorts;
  auto sort = SortHelper::getResultSort(kv.first.term());
  SortHelper::collectVariableSorts(kv.second,sort,varSorts);

  auto it = varSorts.items();
  while (it.hasNext()) {
    auto v = it.next();
    TermList var(v.first,false);
    if (varToSkolemMap.count(var)) {
      continue;
    }

    auto skFun = Skolem::addSkolemFunction(0,nullptr,v.second);
    varToSkolemMap.insert(make_pair(var, Term::create(skFun, 0, nullptr)));
  }
}

vmap<TermList, TermList> GeneralInduction::skolemizeCase(const InductionScheme::Case& c)
{
  vmap<TermList, TermList> varToSkolemMap;
  for (const auto& kv : c._step) {
    mapVarsToSkolems(varToSkolemMap, kv);
  }
  for (const auto& recCall : c._recursiveCalls) {
    for (const auto& kv : recCall) {
      mapVarsToSkolems(varToSkolemMap, kv);
    }
  }
  return varToSkolemMap;
}

vmap<TermList, TermList> createBlanksForScheme(const InductionScheme& sch, DHMap<pair<unsigned,unsigned>,TermList>& blanks)
{
  vmap<unsigned,unsigned> srts;
  vmap<TermList, TermList> replacements;
  for (const auto& t : sch.inductionTerms()) {
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
  return replacements;
}

bool GeneralInduction::alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
  const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res)
{
  CALL("GeneralInduction::alreadyDone");

  static DHMap<pair<unsigned,unsigned>,TermList> blanks;
  auto replacements = createBlanksForScheme(sch, blanks);

  TermReplacement2 cr(replacements);
  res.first = cr.transform(mainLit);

  for (const auto& kv : sides) {
    res.second.insert(cr.transform(kv.first));
  }
  // TODO(mhajdu): the reason we check this is to avoid
  // "induction loops" when we induct on the step immediately
  // after creating it. This means we usually want to exclude
  // schemes with complex terms, but this is an ugly workaround
  bool containsComplex = true;
  for (const auto& indTerm : sch.inductionTerms()) {
    if (skolem(indTerm)) {
      containsComplex = false;
      break;
    }
  }
  if (!_done.find(res.first) || !containsComplex) {
    return false;
  }
  auto s = _done.get(res.first);
  if (includes(s.begin(), s.end(), res.second.begin(), res.second.end())) {
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] already inducted on " << *mainLit << " in " << *res.first << " form" << endl;
      env.endOutput();
    }
    return true;
  }
  return false;
}

inline bool mainLitCondition(Literal* literal) {
  static bool negOnly = env.options->inductionNegOnly();
  return (!negOnly || literal->isNegative() || 
      (theory->isInterpretedPredicate(literal) && theory->isInequality(theory->interpretPredicate(literal)))
    ) && literal->ground();
}

inline bool sideLitCondition(Literal* main, Clause* mainCl, Literal* side, Clause* sideCl) {
  vset<unsigned> sig, sigOther;
  bool hyp, rev, hypOther, revOther;
  return side->ground() &&
    // side->isPositive() &&
    env.options->inductionMultiClause() &&
    main != side &&
    mainCl != sideCl &&
    ((!mainCl->inference().inductionDepth() && !sideCl->inference().inductionDepth()) ||
    (sideCl->isInductionLiteral(side, sigOther, hypOther, revOther) &&
      mainCl->isInductionLiteral(main, sig, hyp, rev) &&
      includes(sig.begin(), sig.end(), sigOther.begin(), sigOther.end()) && !hyp && hypOther && !main->isEquality()));
}

vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> GeneralInduction::selectMainSidePairs(Literal* literal, Clause* premise)
{
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> res;

  TermQueryResultIterator it = TermQueryResultIterator::getEmpty();
  SubtermIterator stit(literal);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (skolem(st)) {
      it = pvi(getConcatenatedIterator(it, _index->getGeneralizations(st)));
    }
  }

  if (mainLitCondition(literal))
  {
    res.emplace_back(SLQueryResult(literal, premise), vset<pair<Literal*,Clause*>>());
    while (it.hasNext()) {
      auto qr = it.next();
      if (qr.clause->store() == Clause::ACTIVE && sideLitCondition(literal, premise, qr.literal, qr.clause)) {
        res.back().second.emplace(qr.literal, qr.clause);
      }
    }
  } else {
    while (it.hasNext()) {
      auto qr = it.next();
      if (qr.clause->store() == Clause::ACTIVE && mainLitCondition(qr.literal) && sideLitCondition(qr.literal, qr.clause, literal, premise)) {
        res.emplace_back(SLQueryResult(qr.literal, qr.clause), vset<pair<Literal*,Clause*>>());
        res.back().second.emplace(literal, premise);
      }
    }
  }
  return res;
}

}
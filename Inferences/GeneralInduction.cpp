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
    vvector<SLQueryResult> sides;

    // StructuralInductionSchemeGenerator gen;
    RecursionInductionSchemeGenerator gen;
    static vvector<pair<InductionScheme, OccurrenceMap>> schOccMap;
    schOccMap.clear();
    gen.generate(qr, sides, schOccMap);
    static vvector<pair<InductionScheme, OccurrenceMap>> generalizedSchOccMap;
    generalizedSchOccMap.clear();
    for (const auto& kv : schOccMap) {
      if (alreadyDone(literal, kv.first)) {
        continue;
      }
      // InductionGeneralizationIterator g(false, kv.second);
      // InductionGeneralizationIterator g(true, kv.second);
      HeuristicGeneralizationIterator g(true, kv.second);
      while (g.hasNext()) {
        auto eg = g.next();
        generalizedSchOccMap.push_back(make_pair(kv.first, eg));
      }
    }
    vvector<SLQueryResult> lits;
    for (const auto& kv : generalizedSchOccMap) {
      generateClauses(kv.first, kv.second, qr, lits, res._clauses);
    }
  }
}

void GeneralInduction::attach(SaturationAlgorithm* salg)
{
  CALL("GeneralInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _splitter=_salg->getSplitter();
}

void GeneralInduction::detach()
{
  CALL("GeneralInduction::detach");

  _splitter=0;
  GeneratingInferenceEngine::detach();
}

Literal* replaceLit(const vmap<TermList,TermList>& r, const OccurrenceMap& occurrences, Literal* lit,
  const vmap<TermList,TermList>& v2sk, const vvector<LiteralStack>& lits, vvector<LiteralStack>& newLits,
  unsigned& var, bool hypothesis = false)
{
  const bool strengthen = env.options->inductionStrengthen();
  TermOccurrenceReplacement2 tr(r, occurrences, lit);
  auto newLit = tr.transform(lit);
  if (newLit != lit) {
    if (hypothesis && strengthen) {
      InductionHypothesisStrengthening ihs(var, newLit);
      // newLit = ihs.transform(newLit);
    }
    TermReplacement2 tr2(v2sk);
    newLit = tr2.transform(newLit);
    if (hypothesis) {
      newLit = Literal::complementaryLiteral(newLit);
    }
    for (auto st : lits) {
      st.push(newLit);
      newLits.push_back(st);
    }
  }
  return newLit;
}

void GeneralInduction::generateClauses(
  const Shell::InductionScheme& scheme,
  const OccurrenceMap& occurrences,
  const SLQueryResult& mainLit,
  const vvector<SLQueryResult>& sideLits,
  ClauseStack& clauses)
{
  CALL("GeneralInduction::generateClauses");

  unsigned var = scheme._maxVar;
  vvector<LiteralStack> lits(1);

  for (const auto& c : scheme._cases) {
    vvector<LiteralStack> newLits;

    auto v2sk = skolemizeCase(c);
    auto newMainLit = replaceLit(c._step, occurrences, mainLit.literal, v2sk, lits, newLits, var);
    ASS_NEQ(newMainLit, mainLit.literal);

    for (const auto& qr : sideLits) {
      replaceLit(c._step, occurrences, qr.literal, v2sk, lits, newLits, var);
    }

    unsigned cnt = 0;
    for (const auto& r : c._recursiveCalls) {
      auto newHypLit = replaceLit(r, occurrences, mainLit.literal, v2sk, lits, newLits, var, true);
      ASS_NEQ(newHypLit, mainLit.literal);
      newHypLit->_indInductionHypothesis = ++cnt;
    }
    newMainLit->_numInductionHypothesis = cnt;

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
  vmap<Literal*, SLQueryResult> conclusionToLitMap;
  TermOccurrenceReplacement2 tr(r, occurrences, mainLit.literal);
  auto newMainLit = tr.transform(mainLit.literal);
  ASS(mainLit.literal != newMainLit);
  newMainLit = Literal::complementaryLiteral(newMainLit);
  for (auto& st : lits) {
    st.push(newMainLit);
  }
  conclusionToLitMap.insert(make_pair(newMainLit, mainLit));

  for (const auto& qr : sideLits) {
    TermOccurrenceReplacement2 tr(r, occurrences, qr.literal);
    auto newLit = tr.transform(qr.literal);
    newLit = Literal::complementaryLiteral(newLit);
    if (qr.literal != newLit) {
      for (auto& st : lits) {
        st.push(newLit);
      }
      conclusionToLitMap.insert(make_pair(newLit, qr));
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

  ClauseStack::Iterator cit(temp);
  while(cit.hasNext()){
    Clause* c = cit.next();
    for (const auto& kv : conclusionToLitMap) {
      auto conclusion = kv.first;
      auto qr = kv.second;
      RobSubstitutionSP subst(new RobSubstitution());
      if (!subst->match(TermList(kv.first), 0, TermList(kv.second.literal), 1)) {
        ASS(kv.first->isEquality() && kv.second.literal->isEquality());
        subst->reset();
        // direct match did not succeed, so we match one literal with the other reversed
        ALWAYS(subst->match(*kv.first->nthArgument(0), 0, *kv.second.literal->nthArgument(1), 1)
          && subst->match(*kv.first->nthArgument(1), 0, *kv.second.literal->nthArgument(0), 1));
      }
      qr.substitution = ResultSubstitution::fromSubstitution(subst.ptr(), 1, 0);
      c = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
      ASS(c);
      if (_splitter && cit.hasNext()) {
        _splitter->onNewClause(c);
      }
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

bool GeneralInduction::alreadyDone(Literal* mainLit, const InductionScheme& sch)
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
  Literal* rep = cr.transform(mainLit);

  if (_done.contains(rep)) {
    // cout << *mainLit << " is skipped (" << *rep << ")" << endl;
    return true;
  }

  _done.insert(rep);
  return false;
}

}
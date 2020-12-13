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
#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/FormulaVarIterator.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Shell/InductionSchemeFilter.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Inferences/BinaryResolution.hpp"

#include "MultiClauseInduction.hpp"

namespace Inferences
{
using namespace Kernel;
using namespace Lib;

bool canDoInductionOn(Clause* cl) {
  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static unsigned maxD = env.options->maxInductionDepth();
  static bool unitOnly = env.options->inductionUnitOnly();
  return (!unitOnly || cl->length()==1) && 
     (all || ( (goal || goal_plus) && cl->derivedFromGoal())) &&
     (maxD == 0 || cl->inference().inductionDepth() < maxD);
}

class MultiClauseInduction::InductionClauseIterator
{
public:
  CLASS_NAME(InductionClauseIterator);
  USE_ALLOCATOR(InductionClauseIterator);
  DECL_ELEMENT_TYPE(Clause*);

  InductionClauseIterator(Splitter* splitter) : _splitter(splitter) {}

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next() { 
    Clause* c = _clauses.pop();
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl; 
      env.endOutput();
    }
    return c; 
  }

  void produceClauses(Formula* hypothesis, const vmap<Literal*, pair<Literal*, Clause*>>& conclusionToOrigLitClauseMap, InferenceRule rule)
  {
    CALL("InductionClauseIterator::produceClauses");
    NewCNF cnf(0);
    cnf.setForInduction();
    Stack<Clause*> hyp_clauses;
    Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
    unsigned maxDepth = 0;
    for (const auto& kv : conclusionToOrigLitClauseMap) {
      maxDepth = max(maxDepth, kv.second.second->inference().inductionDepth());
    }
    inf.setInductionDepth(maxDepth+1);
    FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
    cnf.clausify(NNF::ennf(fu), hyp_clauses);

    // Now perform resolution between origLit and the hyp_clauses on conclusion if conclusion in the clause
    // If conclusion not in the clause then the clause is a definition from clausification and just keep
    Stack<Clause*>::Iterator cit(hyp_clauses);
    static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
    while(cit.hasNext()){
      Clause* c = cit.next();
      for (const auto& kv : conclusionToOrigLitClauseMap) {
        Literal* conclusion = kv.first;
        Literal* origLit = kv.second.first;
        if(c->contains(conclusion)){
          auto premise = kv.second.second;
          SLQueryResult qr(origLit,premise,identity);
          c = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
          if (_splitter) {
            _splitter->onNewClause(c);
          }
        }
      }
      _clauses.push(c);
    }
    env.statistics->induction++;
  }

private:
  Stack<Clause*> _clauses;
  Splitter* _splitter;
};

ClauseIterator MultiClauseInduction::generateClauses(Clause* premise)
{
  CALL("MultiClauseInduction::generateClauses");

  if (premise->containsFunctionDefinition()) {
    return ClauseIterator::getEmpty();
  }

  ASS(env.options->induction() == Options::Induction::BOTH ||
      env.options->induction() == Options::Induction::STRUCTURAL);
  ASS(env.options->structInduction() == Options::StructuralInductionKind::FOUR ||
      env.options->structInduction() == Options::StructuralInductionKind::ALL);

  InductionClauseIterator clIt(_splitter);
  if(canDoInductionOn(premise))
  {
    for(unsigned i=0;i<premise->length();i++){
      auto lit = (*premise)[i];
      if (!lit->ground()) {
        continue;
      }
      vset<TermList> skolems;
      SubtermIterator stit(lit);
      while (stit.hasNext()) {
        auto st = stit.next();
        if (isSkolem(st)) {
          skolems.insert(st);
        }
      }
      auto it = Indexing::TermQueryResultIterator::getEmpty();
      for (const auto& sk : skolems) {
        it = pvi(getConcatenatedIterator(it, _index->getInstances(sk, false)));
      }
      InductionSchemeGenerator mainGen;
      mainGen.generatePrimary(premise, lit);
      if (mainGen._primarySchemes.empty()) {
        continue;
      }
      if (lit->isNegative()) {
        while (it.hasNext()) {
          auto qr = it.next();
          if (qr.clause->store() != Clause::ACTIVE
              || premise==qr.clause || !canDoInductionOn(qr.clause)
              || qr.literal->isNegative() || !qr.literal->ground()) {
            continue;
          }
          bool subset = true;
          SubtermIterator stit(qr.literal);
          while (stit.hasNext()) {
            auto st = stit.next();
            if (isSkolem(st) && !skolems.count(st)) {
              subset = false;
              break;
            }
          }
          if (!subset) {
            continue;
          }
          mainGen.generateSecondary(qr.clause, qr.literal);
        }
        for (const auto& kv : mainGen.instantiateSchemes()) {
          clIt.produceClauses(kv.first, kv.second, InferenceRule::MAIN_MULTICLAUSE_INDUCTION_AXIOM);
        }
      } else {
        while (it.hasNext()) {
          auto qr = it.next();
          if (qr.clause->store() != Clause::ACTIVE
              || premise==qr.clause || !canDoInductionOn(qr.clause)
              || qr.literal->isPositive() || !qr.literal->ground()) {
            continue;
          }
          vset<TermList> mainSkolems;
          SubtermIterator stit(qr.literal);
          while (stit.hasNext()) {
            auto st = stit.next();
            if (isSkolem(st)) {
              mainSkolems.insert(st);
            }
          }
          if (!includes(mainSkolems.begin(), mainSkolems.end(), skolems.begin(), skolems.end())) {
            continue;
          }
          InductionSchemeGenerator sideGen;
          sideGen.generatePrimary(premise, lit);
          sideGen.generateSecondary(qr.clause, qr.literal);
          for (const auto& kv : sideGen.instantiateSchemes()) {
            clIt.produceClauses(kv.first, kv.second, InferenceRule::SIDE_MULTICLAUSE_INDUCTION_AXIOM);
          }
        }
      }
    }
  }

  return pvi(clIt);
}

void MultiClauseInduction::attach(SaturationAlgorithm* salg)
{
  CALL("MultiClauseInduction::attach");
  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
  _splitter=_salg->getSplitter();
}

void MultiClauseInduction::detach()
{
  CALL("MultiClauseInduction::detach");
  _splitter=0;
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

}

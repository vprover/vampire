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

  auto res = ClauseIterator::getEmpty();
  if((!unitOnly || premise->length()==1) && 
     (all || ( (goal || goal_plus) && premise->derivedFromGoal())) &&
     (maxD == 0 || premise->inference().inductionDepth() < maxD)
    )
  {
    for(unsigned i=0;i<premise->length();i++){
      res = pvi(getConcatenatedIterator(res, process(premise,(*premise)[i])));
    }
  }

  return res;
}

ClauseIterator GeneralInduction::process(Clause* premise, Literal* literal)
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
    ) && literal->ground()) {

    SLQueryResult qr(literal, premise);
    vvector<SLQueryResult> sides;

    auto it = (*_schemeGenerator)(qr, sides);
    auto it2 = getMapAndFlattenIterator(it, *_generalization);

    vvector<SLQueryResult> lits;
    lits.push_back(qr);
    return pvi(getMapAndFlattenIterator(it2, InductionFormulaGenerator(lits, _rule, _splitter)));
  }
  return ClauseIterator::getEmpty();
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

InductionFormulaIterator::InductionFormulaIterator(
  const InductionScheme& scheme,
  const OccurrenceMap& occurrences,
  const vvector<SLQueryResult>& lits,
  const InferenceRule& rule,
  Splitter* splitter)
{
  CALL("InductionFormulaGenerator::InductionFormulaGenerator");

  FormulaList* formulas = FormulaList::empty();
  unsigned var = scheme._maxVar;
  const bool strengthen = env.options->inductionStrengthen();

  for (auto& desc : scheme._rDescriptionInstances) {
    // We replace all induction terms with the corresponding step case terms
    FormulaList* stepFormulas = FormulaList::empty();
    for (const auto& kv : lits) {
      TermOccurrenceReplacement2 tr(desc._step, occurrences, kv.literal);
      auto newLit = tr.transform(kv.literal);
      if (newLit != kv.literal) {
        stepFormulas = new FormulaList(new AtomicFormula(Literal::complementaryLiteral(newLit)), stepFormulas);
      }
    }
    auto right = JunctionFormula::generalJunction(Connective::OR, stepFormulas);

    FormulaList* hyp = FormulaList::empty();

    // Then we replace the arguments of the term with the
    // corresponding recursive cases for this step case (if not base case)
    for (const auto& r : desc._recursiveCalls) {
      FormulaList* innerHyp = FormulaList::empty();
      for (const auto& kv : lits) {
        TermOccurrenceReplacement2 tr(r, occurrences, kv.literal);
        auto newLit = tr.transform(kv.literal);
        if (newLit != kv.literal) {
          //TODO(mhajdu): strengthen
          innerHyp = new FormulaList(new AtomicFormula(Literal::complementaryLiteral(newLit)), innerHyp);
        }
      }
      hyp = new FormulaList(JunctionFormula::generalJunction(Connective::OR,innerHyp),hyp);
    }

    Formula* res = nullptr;
    if (hyp == 0) {
      // base case
      res = right;
    } else {
      auto left = JunctionFormula::generalJunction(Connective::AND,hyp);
      // there may be free variables present only in the conditions or
      // hypoheses, quantify these first so that they won't be skolemized away
      auto leftVarLst = left->freeVariables();
      FormulaVarIterator fvit(right);
      while(fvit.hasNext()) {
        auto v = fvit.next();
        if (Formula::VarList::member(v, leftVarLst)) {
          leftVarLst = Formula::VarList::remove(v, leftVarLst);
        }
      }
      if (leftVarLst) {
        left = new QuantifiedFormula(FORALL, leftVarLst, 0, left);
      }
      res = new BinaryFormula(Connective::IMP,left,right);
    }
    formulas = new FormulaList(Formula::quantify(res), formulas);
  }
  ASS(formulas != 0);
  Formula* indPremise = JunctionFormula::generalJunction(Connective::AND,formulas);

  // After creating all cases, we need the main implicant to be resolved with
  // the literal. For this, we use new variables starting from the max. var of
  // the scheme.
  vmap<TermList, TermList> r;
  for (const auto& desc : scheme._rDescriptionInstances) {
    for (const auto& kv : desc._step) {
      if (r.count(kv.first) > 0) {
        continue;
      }
      r.insert(make_pair(kv.first, TermList(var++,false)));
    }
  }
  vmap<Literal*, SLQueryResult> conclusionToLitMap;
  FormulaList* conclusionList = FormulaList::empty();
  for (const auto& kv : lits) {
    TermOccurrenceReplacement2 tr(r, occurrences, kv.literal);
    auto newLit = tr.transform(kv.literal);
    if (newLit != kv.literal) {
      auto conclusion = Literal::complementaryLiteral(newLit);
      conclusionToLitMap.insert(make_pair(conclusion, kv));
      conclusionList = new FormulaList(new AtomicFormula(conclusion), conclusionList);
    }
  }
  Formula* conclusions = JunctionFormula::generalJunction(Connective::OR, conclusionList);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(indPremise),
                            Formula::quantify(conclusions));

  // cout << hypothesis->toString() << endl << endl;

  // return make_pair(hypothesis, conclusionToLitMap);
  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  unsigned maxDepth = 0;
  for (const auto& kv : conclusionToLitMap) {
    maxDepth = max(maxDepth, kv.second.clause->inference().inductionDepth());
  }
  inf.setInductionDepth(maxDepth+1);
  FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  // Now perform resolution between origLit and the hyp_clauses on conclusion if conclusion in the clause
  // If conclusion not in the clause then the clause is a definition from clausification and just keep
  Stack<Clause*>::Iterator cit(hyp_clauses);
  // TODO(mhajdu): here technically the substitution should contain
  // the inductionterm -> variable mappings but this now works as we
  // know exactly what to resolve in the call below. This, however,
  // should be fixed later.

  // create substitutions to use during binary resolution
  for (auto& kv : conclusionToLitMap) {
    ScopedPtr<RobSubstitution> subst(new RobSubstitution());
    ALWAYS(subst->unify(TermList(kv.first), 0, TermList(kv.second.literal), 1));
    kv.second.substitution = ResultSubstitution::fromSubstitution(subst.ptr(), 1, 0);
  }

  while(cit.hasNext()){
    Clause* c = cit.next();
    bool contains = false;
    for (const auto& kv : conclusionToLitMap) {
      auto conclusion = kv.first;
      auto qr = kv.second;
      if (c->contains(conclusion)) {
        contains = true;
      }
      if (contains) {
        c = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
        if (splitter) {
          splitter->onNewClause(c);
        }
      }
    }
    _clauses.push(c);
  }
  env.statistics->induction++;
}

}
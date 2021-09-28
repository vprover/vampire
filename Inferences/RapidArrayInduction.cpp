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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/RapidHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/EqHelper.hpp"

#include "Inferences/BinaryResolution.hpp"

#include "Lib/DHSet.hpp"

#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "RapidArrayInduction.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void RapidArrayInduction::attach(SaturationAlgorithm* salg)
{
  CALL("RapidArrayInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _densityIndex=static_cast<RapidDensityClauseIndex*> (
    _salg->getIndexManager()->request(RAPID_DENSITY_CLAUSE_INDEX) );

  _arrayIndex=static_cast<RapidArrayIndex*> (
    _salg->getIndexManager()->request(RAPID_ARRAY_INDEX) );
}

void RapidArrayInduction::detach()
{
  CALL("RapidArrayInduction::detach");

  _densityIndex=0;
  _salg->getIndexManager()->release(RAPID_DENSITY_CLAUSE_INDEX);

  _arrayIndex=0;
  _salg->getIndexManager()->release(RAPID_ARRAY_INDEX);  
  GeneratingInferenceEngine::detach();
}

void RapidArrayInduction::createConclusions(ClauseStack& conclusions, bool increasing, 
  Literal* subLit, TermList freshVar, TermList arrayAtNextIt, TermList concRHS,
  TermList index, TermList indexAtNextIter)
{
  CALL("RapidArrayInduction::createConclusions");

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);

  subLit = Literal::Literal::complementaryLiteral(subLit);
 
  TermList nlTerm = RapidHelper::getFinalCountFromSubLit(subLit);
  TermList arr    = RapidHelper::arrAtPrevIt(arrayAtNextIt);
  TermList arrAtLastIt = RapidHelper::arrAtLastIt(arr, nlTerm);
  TermList arrAtFirstIt = RapidHelper::arrAtFirstIt(arr);
  TermList itVar = *subLit->nthArgument(0);
  ASS(itVar.isVar());

  TermList bound1 = RapidHelper::intVarAtFirstIt(index);
  TermList bound2 = RapidHelper::intVarAtLastIt(index, nlTerm);

  Formula* indHypothesis1;
  Formula* indHypothesis2;
  {
    
    Literal* l1 = Literal::create2(less, false, (increasing ? freshVar : bound1), 
                                              (increasing ? bound1 : freshVar));
    Literal* l2 = Literal::create2(less, true, (increasing ? freshVar : bound1), 
                                              (increasing ? bound1 : freshVar));
    Literal* l3 = Literal::createEquality(true, arrAtFirstIt, concRHS, Term::intSort());

    Formula* leftOfImp0 = new JunctionFormula(Connective::AND,
                          new FormulaList(new AtomicFormula(l1),
                          new FormulaList(new AtomicFormula(l2))));
    Formula* rightOfImp0 = new AtomicFormula(l3);
    Formula* imp0 = new BinaryFormula(Connective::IMP, leftOfImp0, rightOfImp0);

    Formula* baseCase = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp0);

    l2 = Literal::create2(less, true, (increasing ? freshVar : index), 
                                              (increasing ? index : freshVar));
    l3 = Literal::createEquality(true, arr, concRHS, Term::intSort());

    Formula* leftOfImp1 = new JunctionFormula(Connective::AND,
                          new FormulaList(new AtomicFormula(l1),
                          new FormulaList(new AtomicFormula(l2))));
    Formula* rightOfImp1 = new AtomicFormula(l3);
    Formula* imp1 = new BinaryFormula(Connective::IMP, leftOfImp1, rightOfImp1);

    Formula* quant1 = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp1);


    l2 = Literal::create2(less, false, (increasing ? index : freshVar ), 
                                        (increasing ? freshVar : index));
    l3 = Literal::createEquality(true, arrayAtNextIt, concRHS, Term::intSort());

    Formula* leftOfImp2 = new JunctionFormula(Connective::AND,
                          new FormulaList(new AtomicFormula(l1),
                          new FormulaList(new AtomicFormula(l2))));
    Formula* rightOfImp2 = new AtomicFormula(l3);
    Formula* imp2 = new BinaryFormula(Connective::IMP, leftOfImp2, rightOfImp2);

    Formula* quant2 = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp2);

    l2 = Literal::create2(less, true, (increasing ? freshVar : bound2), 
                                      (increasing ? bound2 : freshVar));
    l3 = Literal::createEquality(true, arrAtLastIt, concRHS, Term::intSort());

    Formula* leftOfImp3 = new JunctionFormula(Connective::AND,
                          new FormulaList(new AtomicFormula(l1),
                          new FormulaList(new AtomicFormula(l2))));
    Formula* rightOfImp3 = new AtomicFormula(l3);
    Formula* imp3 = new BinaryFormula(Connective::IMP, leftOfImp3, rightOfImp3);

    Formula* conclusion = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp3);


    Formula* subFormula = new AtomicFormula(subLit);
    Formula* leftOfImp4 = new JunctionFormula(Connective::AND,
                          new FormulaList(subFormula,
                          new FormulaList(quant1)));
    
    Formula* imp4 = new BinaryFormula(Connective::IMP, leftOfImp4, quant2);
    Formula* stepCase = new QuantifiedFormula(Connective::FORALL, 
      new VList(itVar.var()), 0, imp4);

    Formula* premise = new JunctionFormula(Connective::AND,
                       new FormulaList(baseCase,
                       new FormulaList(stepCase)));

    indHypothesis1 = new BinaryFormula(Connective::IMP, premise, conclusion);
  }

  {
    Literal* l1 = Literal::create2(less, false, 
      (increasing ?  freshVar : index), (increasing ? index : freshVar));
    Literal* l2 = Literal::createEquality(true, arr, arrAtFirstIt, Term::intSort());

    Formula* imp1 = new BinaryFormula(Connective::IMP, 
      new AtomicFormula(l1), new AtomicFormula(l2));

    Formula* quant1 = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp1);


    l1 = Literal::create2(less, false, 
      (increasing ? freshVar : indexAtNextIter), (increasing ? indexAtNextIter : freshVar));
    l2 = Literal::createEquality(true, arrayAtNextIt, arrAtFirstIt, Term::intSort());

    Formula* imp2 = new BinaryFormula(Connective::IMP, 
      new AtomicFormula(l1), new AtomicFormula(l2));

    Formula* quant2 = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var()), 0, imp2);

    l1 = Literal::create2(less, false, 
      (increasing ? freshVar : index), (increasing ? index : freshVar));
    l2 = Literal::createEquality(true, arr, arrAtFirstIt, Term::intSort());


    Formula* leftOfImp = new JunctionFormula(Connective::AND,
                          new FormulaList(new AtomicFormula(subLit),
                          new FormulaList(new AtomicFormula(l1))));
    Formula* rightOfImp = new AtomicFormula(l2);
    Formula* imp3 = new BinaryFormula(Connective::IMP, leftOfImp, rightOfImp);

    Formula* quant3 = new QuantifiedFormula(Connective::FORALL, 
      new VList(freshVar.var(), new VList(itVar.var())), 0, imp3);


    Formula* subFormula = new AtomicFormula(subLit);
    Formula* leftOfImp4 = new JunctionFormula(Connective::AND,
                          new FormulaList(subFormula,
                          new FormulaList(quant1)));
    
    Formula* imp4 = new BinaryFormula(Connective::IMP, leftOfImp4, quant2);
    Formula* quant4 = new QuantifiedFormula(Connective::FORALL, 
      new VList(itVar.var()), 0, imp4);

    indHypothesis2 = new BinaryFormula(Connective::IMP, quant4, quant3);
  }

  //cout << "naming " << env.options->naming() << endl;

  NewCNF cnf(0);  
  //TODO make special name
  InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
  Inference inf1 = NonspecificInference0(UnitInputType::AXIOM,rule);
  FormulaUnit* fu1 = new FormulaUnit(indHypothesis1,inf1);
  fu1 = Rectify::rectify(fu1);

  Inference inf2 = NonspecificInference0(UnitInputType::AXIOM,rule);
  FormulaUnit* fu2 = new FormulaUnit(indHypothesis2,inf2);
  fu2 = Rectify::rectify(fu2);

  static unsigned counter = 0;

  if(counter > 1){
    return;
  }
  counter = counter + 1;

  //cout << fu1->toString() << endl;
  //cout << fu2->toString() << endl;


  cnf.clausify(NNF::ennf(fu1), conclusions); 
  cnf.clausify(NNF::ennf(fu2), conclusions);   

  /*cout << "\n-----------------------\n" << endl;
  for(unsigned i = 0; i < conclusions.size(); i++){
    cout << conclusions[i]->toString() << endl;
  }
  cout << "\n-----------------------\n" << endl;*/ 
}

ClauseIterator RapidArrayInduction::generateClauses(Clause* premise)
{
  CALL("RapidArrayInduction::generateClauses");
  
  unsigned litPos, termPos;
  //TODO perhaps we ought to trigger on finding a dnsity clause as well?
  //in most situations, this si likely to occur afterwards.
  if(RapidHelper::isArrayAccessClause(premise, litPos, termPos)){
    Literal* lit = (*premise)[litPos];
    TermList arr = *lit->nthArgument(termPos);
    TermList arrTransformed = *lit->nthArgument(!termPos);
    
    ASS(arr.isTerm() && arr.term()->arity() == 2);
    TermList index = *arr.term()->nthArgument(1);
    TermList indexAtNextIter = RapidHelper::intVarAtNextIt(index);

    auto it = _densityIndex->getUnifications(indexAtNextIter,false);
    if(it.hasNext()){
      ClauseStack results;

      TermQueryResult res = it.next(); 
      Literal* lit = res.literal;
      bool increasing = RapidHelper::increasing(lit, res.term);

      unsigned maxVar = premise->maxVar();
      TermList freshVar = TermList(maxVar + 1, false);

      TermList arrAtPrevIt = RapidHelper::arrAtPrevIt(arr);
      TermList concRHS = RapidHelper::arrAtFirstIt(arr);
      concRHS = RapidHelper::changeArrIndex(concRHS, freshVar);
      concRHS = TermList(EqHelper::replace(arrTransformed.term(), arrAtPrevIt, concRHS));

      arr = RapidHelper::changeArrIndex(arr, freshVar);

      createConclusions(results, increasing, (*premise)[!litPos], freshVar, arr, 
        concRHS, index, indexAtNextIter);
      return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
    }

  }
  return ClauseIterator::getEmpty();
}

}
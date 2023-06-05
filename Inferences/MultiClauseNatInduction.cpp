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
#include "Kernel/Theory.hpp"

#include "Inferences/BinaryResolution.hpp"

#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "MultiClauseNatInduction.hpp"

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

void MultiClauseNatInduction::attach(SaturationAlgorithm* salg)
{
  CALL("MultiClauseNatInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<MultiClauseNatInductionIndex*> (
    _salg->getIndexManager()->request(MULTI_CLAUSE_NAT_IND_INDEX) );
}

void MultiClauseNatInduction::detach()
{
  CALL("MultiClauseNatInduction::detach");

  _index=0;
  _salg->getIndexManager()->release(MULTI_CLAUSE_NAT_IND_INDEX);
  GeneratingInferenceEngine::detach();
}

Formula* TermReplacingFormulaTransformer::applyLiteral(Formula* f)
{
  CALL ("TermReplacingFormulaTransformer::applyLiteral")

  Literal* lit = f->literal();
  Literal* res = EqHelper::replace(lit, _toBeReplaced, _replacer);
  if(lit==res) { return f; }
  return new AtomicFormula(res);  
}

void MultiClauseNatInduction::createConclusions(ClauseStack& premises, 
      TermList inductionTerm, TermList limit, ClauseStack& conclusions, 
      bool multiLiterals, bool allGround)
{
  Clause* c;
  Literal* lit;
  
  bool inductionIsLimit = inductionTerm == limit;

  TermList zeroTerm;
  auto natTA = env.signature->getNat();
  if(natTA){
    zeroTerm = natTA->createZero();
  } else {
    zeroTerm = TermList(theory->representConstant(IntegerConstantType(0)));
  }

  unsigned maxVar = 0;

  static Stack<Formula*> disjuncts;

  for(unsigned i = 0; i < premises.size(); i++){
    c = premises[i];

    //cout << "premise: " + c->toString() << endl;
    //cout << "premise goal age " << c->inference().distanceFromGoal() << endl;

    if(c->maxVar() > maxVar){
      maxVar = c->maxVar();
    }
    FormulaList* formulas = FormulaList::empty();
    for(unsigned j = 0; j < c->length(); j++){
      lit = (*c)[j];
      FormulaList::push(new AtomicFormula(lit),formulas);
    }
    Formula* negatedDisjunct = NegatedFormula::negate(Formula::quantify(
      JunctionFormula::generalJunction(Connective::OR, formulas)));
    disjuncts.push(negatedDisjunct);
  }

  FormulaList* bases = FormulaList::empty();
  for(unsigned i = 0; i < disjuncts.size(); i++){
    Formula* f = disjuncts[i]; 
    TermReplacingFormulaTransformer trft(inductionTerm, zeroTerm);
    f = trft.transform(f);
    FormulaList::push(f,bases);
  }

  Formula* baseCase = JunctionFormula::generalJunction(Connective::OR, bases);

  TermList freshVar = TermList(maxVar + 1, false);
  TermList succVar;
  if(natTA){
    succVar = natTA->createSucc(freshVar);
  } else {
    // TODO Theory code can be made more concise with helper functions! 
    TermList one(theory->representConstant(IntegerConstantType(1)));
    unsigned plusFun = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
    succVar = TermList(Term::create2(plusFun,freshVar,one));
  }

  FormulaList* lefts = FormulaList::empty();
  for(unsigned i = 0; i < disjuncts.size(); i++){
    Formula* f = disjuncts[i]; 
    TermReplacingFormulaTransformer trft(inductionTerm, freshVar);
    f = trft.transform(f);    
    FormulaList::push(f,lefts);
  }
  Formula* left = JunctionFormula::generalJunction(Connective::OR, lefts);
  Formula* bounds; 
  if(natTA){
    bounds = new AtomicFormula(natTA->createLess(true, freshVar, limit));
  } else {
    unsigned lessPred = env.signature->getInterpretingSymbol(Theory::INT_LESS);
    Formula* b1 = new AtomicFormula(Literal::create2(lessPred,true,freshVar,limit));
    Formula* b2 = new AtomicFormula(Literal::create2(lessPred,false,freshVar, zeroTerm));
    bounds = new JunctionFormula(Connective::AND, new FormulaList(b1, new FormulaList(b2)));
  }
  Formula* leftOfImp = new JunctionFormula(Connective::AND,
                       new FormulaList(bounds,new FormulaList(left)));


  FormulaList* rights = FormulaList::empty();
  for(unsigned i = 0; i < disjuncts.size(); i++){
    Formula* f = disjuncts[i]; 
    TermReplacingFormulaTransformer trft(inductionTerm, succVar);
    f = trft.transform(f); 
    FormulaList::push(f,rights);
  }
  Formula* rightOfImp = JunctionFormula::generalJunction(Connective::OR, rights);
  Formula* stepCase = Formula::quantify(new BinaryFormula(Connective::IMP, leftOfImp, rightOfImp));

  Formula* hypotheses = new JunctionFormula(Connective::AND,
                        new FormulaList(baseCase,new FormulaList(stepCase))); 

  FormulaList* concs = FormulaList::empty();
  for(unsigned i = 0; i < disjuncts.size(); i++){
    Formula* f = disjuncts[i]; 
    if(!inductionIsLimit){
      TermReplacingFormulaTransformer trft(inductionTerm, freshVar);
      f = trft.transform(f);
    }   
    FormulaList::push(f,concs);
  }
  Formula* conclusion = JunctionFormula::generalJunction(Connective::OR, concs);
  if(!inductionIsLimit){
    conclusion = Formula::quantify(new BinaryFormula(Connective::IMP, bounds,conclusion));
  }


  Formula* inductionFormula = new BinaryFormula(Connective::IMP, hypotheses, conclusion);

  NewCNF cnf(0); 
  cnf.setForInduction();
  InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  FormulaUnit* fu = new FormulaUnit(inductionFormula,inf);
  fu = Rectify::rectify(fu);

  //if(!inductionIsLimit){
    cout << "FU: " << fu->toString() << endl;
  //}

  ClauseStack clausifiedHyps;
  cnf.clausify(NNF::ennf(fu), clausifiedHyps);

  if(!multiLiterals && allGround && inductionIsLimit){
    // In the case where some of the original clauses
    // are non-ground, the resolution step is more complicated.
    // perhaps this can be supported later
    while(!clausifiedHyps.isEmpty()){
      Clause* cls = clausifiedHyps.pop();

      bool resolved = false;

      while(!premises.isEmpty()){
        Clause* prem = premises.pop();
        Formula* f = disjuncts.pop();
        lit = f->literal();
        Literal* negatedLit = Literal::complementaryLiteral(lit);

        if(cls->contains(negatedLit)){
          static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
          SLQueryResult res((*prem)[0], prem, identity);       
           
          if(resolved){
            static bool splitting = env.options->splitting();
            if(splitting){
              auto splitter = _salg->getSplitter();
              splitter->onNewClause(cls); 
            }          
          }

          //at this point resolve
          cls = BinaryResolution::generateClause(cls,negatedLit,res,*env.options);
          resolved = true;
        }
      }
      cout << "ADDING " + cls->toString() << endl;
      conclusions.push(cls);    
    }
  } else {
    disjuncts.reset();
    while(!clausifiedHyps.isEmpty()){
      Clause* cls = clausifiedHyps.pop();
      cout << "ADDING " + cls->toString() << endl;
      conclusions.push(cls);
    }
  }

}

bool MultiClauseNatInduction::ground(Clause* c)
{
  CALL("MultiClauseNatInduction::ground");

  for(unsigned i = 0; i < c->length(); i++){
    if(!(*c)[i]->ground()) return false;
  }
  return true;
}

void MultiClauseNatInduction::getFinalLoopIters(Clause* c, 
  TermStack& iterations, unsigned& numberOfIters)
{
  CALL("MultiClauseNatInduction::tryGetFinalLoopCount");

  static DHSet<TermList> loopEndsAdded;
  loopEndsAdded.reset();
  numberOfIters = 0;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    SubtermIterator sit(lit);
    while (sit.hasNext()) {  
      TermList tl = sit.next();
      if (RapidHelper::isFinalLoopCount(tl)){
        numberOfIters++;
        if(loopEndsAdded.insert(tl)){
          iterations.push(tl);
        }
      }
    }    
  }

}


void MultiClauseNatInduction::getNonFinalLoopIters(Clause* c, TermStack& iterations)
{
  CALL("MultiClauseNatInduction::getNonFinalLoopIters");

  static DHSet<TermList> iterationsSeen;
  iterationsSeen.reset();

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    SubtermIterator sit(lit);
    while (sit.hasNext()) {  
      TermList tl = sit.next();
      if(RapidHelper::isTimePoint(tl)){
        Term* tlTerm = tl.term();
        if(tlTerm->arity()){
          TermList lastArg = *tlTerm->nthArgument(tlTerm->arity() - 1);
          if(env.signature->getFunction(lastArg.term()->functor())->skolem()){
            if(iterationsSeen.insert(lastArg)){
              iterations.push(lastArg);
            }            
          }
        }
      }
    }    
  }

}

void MultiClauseNatInduction::getNonFinalLoopIters2(Literal* lit, TermStrStack& iterations)
{
  CALL("MultiClauseNatInduction::getNonFinalLoopIters2");

  static DHMap<TermList,unsigned> iterationsSeen;
  iterationsSeen.reset();

  SubtermIterator sit(lit);
  while (sit.hasNext()) {  
    TermList tl = sit.next();
    if(RapidHelper::isTimePoint(tl) && tl.term()->arity() == 1){ // doesn't work for nested loops
      unsigned* occs = iterationsSeen.findPtr(tl);
      if(occs){
        (*occs)++;
        if(*occs >= 0){ // arbitrary bound 2 here
          TermList it = *tl.term()->nthArgument(0); 
          // TODO make exclusive to Skolems?
          //if(it.isTerm() && env.signature->getFunction(it.term()->functor())->skolem())
          vstring tpName = env.signature->getFunction(tl.term()->functor())->name();          
          iterations.push(std::make_pair(it, tpName));
        }
      } else {
        iterationsSeen.insert(tl,0);
      }
    }
  }    

}

bool MultiClauseNatInduction::alreadyAddedAxiom(vset<unsigned>& premises)
{
  CALL("MultiClauseNatInduction::alreadyAddedAxiom");
  
  for(unsigned i = 0; i < _inductionsCarriedOut.size(); i++){
    if(_inductionsCarriedOut[i] == premises){
      return true;
    }
  }
  return false;

}

ClauseIterator MultiClauseNatInduction::generateClauses(Clause* premise)
{
  CALL("MultiClauseNatInduction::generateClauses");

  static bool multiLiterals = env.options->multiLiteralClauses();
  static bool allLoopCounts = env.options->inductAllLoopCounts();
  static int MAX_DIS = (int)env.options->maxDistanceFromGoal();

  if((premise->length() != 1 && !multiLiterals)){
    //Is this condition too restrictive?
    return ClauseIterator::getEmpty();
  }

  bool allGround = ground(premise);
  ClauseStack results;

  if(premise->derivedFromGoal() &&
     !(premise->inference().distanceFromGoal() > MAX_DIS)){

    if(allLoopCounts && premise->length() == 1 && allGround){
      static TermStrStack iters;

      cout << premise->toString() << endl;

      Literal* lit = (*premise)[0];

  //    vstring tpName;
  //    if(RapidHelper::isSuitableForInduction(lit, tpName)){    
  // TODO keep both versions (or find a middle line)

      getNonFinalLoopIters2(lit, iters);


      while(!iters.isEmpty()){
        auto it = iters.pop();
        auto tpName = it.second;
        auto iter   = it.first;

        

        unsigned nlFun;
        // WARNING below is very limiting...
        if(env.signature->tryGetFunctionNumber("n" + tpName, 0, nlFun)){
          TermList limit = TermList(Term::createConstant(nlFun));  

          // an arbitrary variable to ensure that we do not create 
          // the same induction formula twice.       
          TermList zeroVar = TermList(0, false);
          Literal* replacedByZero = EqHelper::replace(lit, iter, zeroVar);

          if(_premisesUsed.insert(replacedByZero)){
            static ClauseStack premises;
            premises.reset();
            premises.push(premise);
            
            cout << "prem " <<  premise << endl;
            cout << "iter " << iter << endl;
            createConclusions(premises, iter, limit, results, false, true);
          }
        }
      }

      iters.reset();
    }
 
  }

  static TermStack iterations;
  iterations.reset();

  unsigned numberOfIters = 0;
  getFinalLoopIters(premise, iterations, numberOfIters);

  if(iterations.size() == 1 && numberOfIters >= 3 && premise->derivedFromGoal() && 
     premise->length() == 1 && allGround){

    static ClauseStack premises;
    premises.reset();
    premises.push(premise);

    TermList nlTerm = iterations.top();

    createConclusions(premises, nlTerm, nlTerm, results, false, true);
  }

  if(premise->derivedFromGoal() &&
     !(premise->inference().distanceFromGoal() > MAX_DIS)){
    
    //cout << premise->toString() << endl;

    while(!iterations.isEmpty()){
      TermList nlTerm = iterations.pop();
      //no need for the unifier
      auto it = _index->getUnifications(nlTerm,false);
      
      static ClauseStack premises;
      premises.reset();
      premises.push(premise);
      
      vset<unsigned> premisesSeen;
      premisesSeen.insert(premise->number());

      while(it.hasNext()){
        TermQueryResult res = it.next();  
        Clause* c = res.clause;

        if(premisesSeen.insert(c->number()).second){
          allGround = allGround && ground(c);
          premises.push(c);
        }
      }
      
      //if(premises.size() > 1 || (multiLiterals && premises[0]->length() > 1)){
        if(!alreadyAddedAxiom(premisesSeen)){
          _inductionsCarriedOut.push(premisesSeen);
          createConclusions(premises, nlTerm, nlTerm, results, multiLiterals, allGround);
        }
     // }
    }
  }

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
}

}
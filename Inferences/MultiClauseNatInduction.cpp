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

  auto natTA = env.signature->getNat();
  ASS(natTA);
  TermList zeroTerm = natTA->createZero();

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
  TermList succVar = natTA->createSucc(freshVar);

  FormulaList* lefts = FormulaList::empty();
  for(unsigned i = 0; i < disjuncts.size(); i++){
    Formula* f = disjuncts[i]; 
    TermReplacingFormulaTransformer trft(inductionTerm, freshVar);
    f = trft.transform(f);    
    FormulaList::push(f,lefts);
  }
  Formula* left = JunctionFormula::generalJunction(Connective::OR, lefts);
  Formula* less = new AtomicFormula(natTA->createLess(true, freshVar, limit));
  Formula* leftOfImp = new JunctionFormula(Connective::AND,
                       new FormulaList(less,new FormulaList(left)));


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
    conclusion = Formula::quantify(new BinaryFormula(Connective::IMP, less,conclusion));
  }


  Formula* inductionFormula = new BinaryFormula(Connective::IMP, hypotheses, conclusion);

  NewCNF cnf(0); 
  cnf.setForInduction();
  InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  FormulaUnit* fu = new FormulaUnit(inductionFormula,inf);
  fu = Rectify::rectify(fu);

  if(!inductionIsLimit){
    //cout << fu->toString() << endl;
  }

  ClauseStack clausifiedHyps;
  cnf.clausify(NNF::ennf(fu), clausifiedHyps);

  if(!multiLiterals && allGround && inductionIsLimit){
    // In the case where some of the original clauses
    // are non-ground, the resolution step is more complicated.
    // perhaps this can be supported later
    while(!clausifiedHyps.isEmpty()){
      Clause* cls = clausifiedHyps.pop();

      while(!premises.isEmpty()){
        Clause* prem = premises.pop();
        Formula* f = disjuncts.pop();
        lit = f->literal();
        Literal* negatedLit = Literal::complementaryLiteral(lit);

        bool resolved = false;

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
      conclusions.push(cls);    
    }
  } else {
    disjuncts.reset();
    while(!clausifiedHyps.isEmpty()){
      Clause* cls = clausifiedHyps.pop();
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

void MultiClauseNatInduction::getFinalLoopIters(Clause* c, TermStack& iterations)
{
  CALL("MultiClauseNatInduction::tryGetFinalLoopCount");

  static DHSet<TermList> loopEndsAdded;
  loopEndsAdded.reset();

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    SubtermIterator sit(lit);
    while (sit.hasNext()) {  
      TermList tl = sit.next();
      if (RapidHelper::isFinalLoopCount(tl)){
        if(loopEndsAdded.insert(tl)){
          iterations.push(tl);
        }
      }
    }    
  }

}


void MultiClauseNatInduction::getNonFinalLoopIters(Clause* c, TermStack& iterations)
{
  CALL("MultiClauseNatInduction::tryGetFinalLoopCount");

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

  /*if(premise->length() == 1){
    if((*premise)[0]->toString() == "$less(i(l14(sK4)),0)"){
      cout << premise->toString() << endl;
      cout << "frim goal " << premise->derivedFromGoal() << endl;
      cout << "distance " << premise->inference().distanceFromGoal() << endl;
    }
  }*/

  if((premise->length() != 1 && !multiLiterals)){
    //Is this condition too restrictive?
    return ClauseIterator::getEmpty();
  }


  bool allGround = ground(premise);
  ClauseStack results;


  static TermStack iterations;
  if(allLoopCounts && premise->length() == 1 && allGround && premise->derivedFromGoal()){

    Literal* lit = (*premise)[0];
    vstring tpName;
    if(RapidHelper::isSuitableForInduction(lit, tpName)){    
      unsigned nlFun;
      ALWAYS(env.signature->tryGetFunctionNumber("n" + tpName, 0, nlFun));
      TermList limit = TermList(Term::createConstant(nlFun));  

      getNonFinalLoopIters(premise, iterations);
      while(!iterations.isEmpty()){
        TermList iter = iterations.pop();
        // an arbitrary variable to ensure that we do not created 
        // the same induction formula twice.       
        TermList zeroVar = TermList(0, false);
        Literal* skReplacedByZero = EqHelper::replace(lit, iter, zeroVar);

        if(_premisesUsed.insert(skReplacedByZero)){
          static ClauseStack premises;
          premises.reset();
          premises.push(premise);

          createConclusions(premises, iter, limit, results, false, true);
        }
      }

      iterations.reset();
    }
  }
   
  if(premise->derivedFromGoal() &&
     !(premise->inference().distanceFromGoal() > MAX_DIS)){
    getFinalLoopIters(premise, iterations);
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
      

      if(premises.size() > 1 || (multiLiterals && premises[0]->length() > 1)){
        if(!alreadyAddedAxiom(premisesSeen)){
          _inductionsCarriedOut.push(premisesSeen);
          createConclusions(premises, nlTerm, nlTerm, results, multiLiterals, allGround);
        }
      }
    }
  }

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
}

}
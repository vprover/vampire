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
 * @file LambdaElimination.cpp
 * converts a term from namaed lambda representation to 
 * a nameless one
 */
 

#if VHOL

#include "Indexing/TermSharing.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Deque.hpp"
#include "Lib/Sort.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Skolem.hpp"
#include "Options.hpp"

#include "LambdaConversion.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

typedef ApplicativeHelper AH;

TermList LambdaConversion::convertLambda(Formula* formula)
{
  CALL("LambdaConversion::convertLambda(Formula*)");

  // remove top level universal type quantifiers.
  if(formula->connective() == FORALL){
    VList* vars  = formula->vars();
    SList* sorts = formula->sorts(); 
    Formula* f = formula->qarg();
    TermList s;

    bool typeVarFound;
    while(vars){
      SortHelper::tryGetVariableSort(vars->head(), f, s);      
      if(s == AtomicSort::superSort()){
        typeVarFound = true;
        vars  = vars->tail();
        if(sorts)
          sorts = sorts->tail();
      } else {
        break;
      }
    }

    if(typeVarFound){
      if(vars) {
        formula = new QuantifiedFormula(FORALL,vars,sorts,f);
      } else {
        formula = f;
      }
    }
  }

  VarToIndexMap map;
  return convertLambda(formula, map);
}

TermList LambdaConversion::convertLambda(Formula* formula, VarToIndexMap& map)
{
  CALL("LambdaConversion::convertLambda(Formula*)/2");

  TermList appTerm; //The resulting term

  Connective conn = formula->connective();
               
  switch(conn){
    case LITERAL: {
      Literal* lit = formula->literal();
      ASS(lit->isEquality()); //Is this a valid assumption?
    
      TermList lhs = convertLambda(*lit->nthArgument(0), map);
      TermList rhs = convertLambda(*lit->nthArgument(1), map);           
                
      TermList equalsSort = SortHelper::getEqualityArgumentSort(lit);
             
      appTerm = AH::app2(AH::equality(equalsSort), lhs, rhs);
      
      return lit->polarity() ? appTerm : AH::app(AH::neg(), appTerm);
    }
    case IFF:
    case IMP:
    case XOR:{
      Formula* lhs = formula->left();
      Formula* rhs = formula->right();
                    
      vstring name = (conn == IFF ? "vIFF" : (conn == IMP ? "vIMP" : "vXOR"));
      TermList constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));

      TermList form1 = convertLambda(lhs, map);
      TermList form2 = convertLambda(rhs, map);

      return AH::app2(constant, form1, form2);;
    }
    case AND:
    case OR:{
      FormulaList::Iterator argsIt(formula->args());
      
      vstring name = (conn == AND ? "vAND" : "vOR");
      TermList constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));
      
      TermList form;
      unsigned count = 1;
      while(argsIt.hasNext()){
        Formula* arg = argsIt.next();
        form = convertLambda(arg, map);
        if(count == 1){
          appTerm = AH::app(constant, form);
        }else if(count == 2){
          appTerm = AH::app(appTerm, form);
        }else{
          appTerm = AH::app2(constant, appTerm, form);
        }
        count++;
      }
      return appTerm;                           
    }
    case NOT: {
      TermList form = convertLambda(formula->uarg(), map);
      return  AH::app(AH::neg(), form);                                                    
    }
    case FORALL:
    case EXISTS: {
      VList* vars = formula->vars();
      VList::Iterator vit(vars);

      TermList form = TermList(Term::createFormula(formula->qarg()));
      bool pi = conn == FORALL;

      TermList s;
      while(vit.hasNext()){
        int v = vit.next();
        ALWAYS(SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        if(s == AtomicSort::superSort()){
          USER_ERROR("Vampire does not support full TH1. This benchmark is either outside of the TH1 fragment, or outside of the fragment supported by Vampire");
        }
        VList* var = VList::singleton(v);        
        SList* sort = SList::singleton(s); 
        auto t = TermList(Term::createLambda(form, var, sort, AtomicSort::boolSort()));  
        form = AH::app((pi ? AH::pi(s) : AH::sigma(s)), t);
      }
      return convertLambda(form, map);
    }
    case BOOL_TERM:
      return convertLambda(formula->getBooleanTerm(), map);
    case TRUE:
      return TermList(Term::foolTrue());
    case FALSE:
      return TermList(Term::foolFalse());
    default:
      ASSERTION_VIOLATION;
    
  }//switch conn             
}   

TermList LambdaConversion::convertLambda(TermList term)
{
  CALL("LambdaConversion::convertLambda(TermList)");

  VarToIndexMap map;
  return convertLambda(term, map);
}

TermList LambdaConversion::convertLambda(TermList term, VarToIndexMap& map)
{
  CALL("LambdaConversion::convertLambda(TermList)/2");

  if(term.isVar()){   
    IndexSortPair p;
    if(map.find(term.var(), p)){
      return AH::getDeBruijnIndex(p.first,p.second);  
    }
    return term;
  }

  Term* t = term.term();
  if(t->isSpecial()){   
    switch(t->functor()){
      case Term::SF_FORMULA: 
        return convertLambda(t->getSpecialData()->getFormula(), map);

      case Term::SF_LAMBDA:{
        Term::SpecialTermData* sd = t->getSpecialData();
        SList* sorts = sd->getLambdaVarSorts();
        VList* vars = sd->getLambdaVars();
        
        TermList eliminated = convertLambda(vars, sorts, sd->getLambdaExp(), sd->getLambdaExpSort(), map);
        ASS_REP2(eliminated.isVar() || sortOf(eliminated) == sd->getSort(), t->toString(), eliminated.toString())
        return eliminated;
      }

      default:
        ASSERTION_VIOLATION;    
    }
  }

  if(!t->isApplication()){
    return term;
  }

  //must be of the form app(s1, s2, arg1, arg2)
  TermList s1 = *t->nthArgument(0);
  TermList s2 = *t->nthArgument(1);  
  TermList arg1 = *t->nthArgument(2);
  TermList arg2 = *t->nthArgument(3);

  return AH::app(s1, s2, convertLambda(arg1, map), convertLambda(arg2, map));
}


TermList LambdaConversion::convertLambda(VList* vars, SList* sorts, 
  TermList body, TermList bodySort, VarToIndexMap& map)
{
  CALL("LambdaConversion::LambdaConversion(VList* vars...)");

  TermList converted;

  unsigned v = (unsigned)vars->head();
  TermList s = sorts->head();
  vars = vars->tail();
  sorts = sorts->tail();

  VarToIndexMap newMap(map);
  newMap.mapValues([](IndexSortPair p){ return make_pair(p.first + 1, p.second); });
  newMap.insert(v, make_pair(0, s));

  if(vars){
    converted = convertLambda(vars, sorts, body, bodySort, newMap);
  } else {
    converted = convertLambda(body, newMap);
  }

  bodySort = converted.isVar() ? bodySort : sortOf(converted);
  return AH::lambda(s, bodySort, converted);
}

TermList LambdaConversion::convertLambda(Term* lambdaTerm)
{
  CALL("LambdaConversion::convertLambda");
  
  return convertLambda(TermList(lambdaTerm));
}


TermList LambdaConversion::sortOf(TermList t)
{
  CALL("LambdaConversion::sortOf");
  
  ASS(t.isTerm());
  return SortHelper::getResultSort(t.term());
}

void LambdaConversion::addFunctionExtensionalityAxiom(Problem& prb)
{
  CALL("LambdaConversion::addFunctionExtensionalityAxiom"); 

  TermList alpha = TermList(0, false);
  TermList beta = TermList(1, false);
  TermList x = TermList(2, false);
  TermList y = TermList(3, false);
  unsigned diff = env.signature->getDiff();

  TermList diffT = TermList(Term::create2(diff, alpha, beta));
  TermList diffTApplied = AH::app2(diffT, x, y);
  TermList lhs = AH::app(alpha, beta, x, diffTApplied);
  TermList rhs = AH::app(alpha, beta, y, diffTApplied);

  Clause* funcExtAx = new(2) Clause(2,  NonspecificInference0(UnitInputType::AXIOM,InferenceRule::FUNC_EXT_AXIOM));
  (*funcExtAx)[0] = Literal::createEquality(false, lhs, rhs, beta);
  (*funcExtAx)[1] = Literal::createEquality(true, x, y, AtomicSort::arrowSort(alpha, beta));
  UnitList::push(funcExtAx, prb.units());


  if (env.options->showPreprocessing()) {
    env.out() << "Added functional extensionality axiom: " << std::endl;
    env.out() << funcExtAx->toString() << std::endl;       
  }
}

void LambdaConversion::addChoiceAxiom(Problem& prb)
{
  CALL("LambdaConversion::addChoiceAxiom"); 
 
  TermList alpha = TermList(0, false);
  TermList boolS = AtomicSort::boolSort();
  TermList alphaBool = AtomicSort::arrowSort(alpha, AtomicSort::boolSort());
  TermList p = TermList(1, false);
  TermList x = TermList(2, false);
  unsigned choice = env.signature->getChoice();

  TermList choiceT = TermList(Term::create1(choice, alpha));
  TermList choiceTApplied = AH::app(alphaBool, alpha, choiceT, p);
  TermList px = AH::app(alpha, boolS, p, x);
  TermList pchoiceT = AH::app(alpha, boolS, p, choiceTApplied);

  Clause* choiceAx = new(2) Clause(2, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::CHOICE_AXIOM));
  (*choiceAx)[0] = Literal::createEquality(true, px, AH::bottom(), boolS);
  (*choiceAx)[1] = Literal::createEquality(true, pchoiceT, AH::top(), boolS);
  UnitList::push(choiceAx, prb.units());


  if (env.options->showPreprocessing()) {
    env.out() << "Added Hilbert choice axiom: " << std::endl;
    env.out() << choiceAx->toString() << std::endl;       
  }
}

void LambdaConversion::addProxyAxioms(Problem& prb)
{
  CALL("LambdaConversion::addProxyAxioms");

  TermList s1 = TermList(0, false);  
  TermList x = TermList(1, false);
  TermList y = TermList(2, false);

  TermList choiceSort = AtomicSort::arrowSort(AtomicSort::arrowSort(s1, AtomicSort::boolSort()), s1);
  unsigned skolem1 = Skolem::addSkolemFunction(1,1,0, choiceSort);
  unsigned skolem2 = Skolem::addSkolemFunction(1,1,0, choiceSort);
  TermList sk1 = TermList(Term::create1(skolem1, s1));
  TermList sk2 = TermList(Term::create1(skolem2, s1));

  Clause* eqAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  (*eqAxiom1)[0] = toEquality(AH::app2(AH::equality(s1), x, y), true);
  (*eqAxiom1)[1] = Literal::createEquality(false,x,y,s1); 
  eqAxiom1->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(eqAxiom1, prb.units());

  Clause* eqAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  (*eqAxiom2)[0] = toEquality(AH::app2(AH::equality(s1), x, y), false);
  (*eqAxiom2)[1] = Literal::createEquality(true,x,y,s1); 
  eqAxiom2->inference().setProxyAxiomsDescendant(true);   
  UnitList::push(eqAxiom2, prb.units());

  Clause* notAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  (*notAxiom1)[0] = toEquality(AH::app(AH::neg(), x), true);
  (*notAxiom1)[1] = toEquality(x, true);
  notAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom1, prb.units());

  Clause* notAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  (*notAxiom2)[0] = toEquality(AH::app(AH::neg(), x), false);
  (*notAxiom2)[1] = toEquality(x, false);
  notAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom2, prb.units());  

  Clause* piAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  (*piAxiom1)[0] = toEquality(AH::app(AH::pi(s1), x), true);
  (*piAxiom1)[1] = toEquality(AH::app(s1, AtomicSort::boolSort(), x, AH::app(sk1, x)), false);
  piAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(piAxiom1, prb.units());

  Clause* piAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  (*piAxiom2)[0] = toEquality(AH::app(AH::pi(s1), x), false);
  (*piAxiom2)[1] = toEquality(AH::app(s1, AtomicSort::boolSort(), x, y), true);
  piAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(piAxiom2, prb.units());  

  Clause* sigmaAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  (*sigmaAxiom1)[0] = toEquality(AH::app(AH::sigma(s1), x), true); 
  (*sigmaAxiom1)[1] = toEquality(AH::app(s1, AtomicSort::boolSort(), x, y), false);
  sigmaAxiom1->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(sigmaAxiom1, prb.units());

  Clause* sigmaAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  (*sigmaAxiom2)[0] = toEquality(AH::app(AH::sigma(s1), x), false);
  (*sigmaAxiom2)[1] = toEquality(AH::app(s1, AtomicSort::boolSort(), x, AH::app(sk2, x)), true);
  sigmaAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(sigmaAxiom2, prb.units()); 

  Clause* impAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom1)[0] = toEquality(AH::app2(AH::imp(), x, y), true);
  (*impAxiom1)[1] = toEquality(x, true);
  impAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(impAxiom1, prb.units());

  Clause* impAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom2)[0] = toEquality(AH::app2(AH::imp(), x, y), true);
  (*impAxiom2)[1] = toEquality(y, false);
  impAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(impAxiom2, prb.units());

  Clause* impAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom3)[0] = toEquality(AH::app2(AH::imp(), x, y), false);  
  (*impAxiom3)[1] = toEquality(x, false);
  (*impAxiom3)[2] = toEquality(y, true);
  impAxiom3->inference().setProxyAxiomsDescendant(true);
  UnitList::push(impAxiom3, prb.units());

  Clause* andAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom1)[0] = toEquality(AH::app2(AH::conj(), x, y), false);
  (*andAxiom1)[1] = toEquality(x, true);
  andAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom1, prb.units());

  Clause* andAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom2)[0] = toEquality(AH::app2(AH::conj(), x, y), false);
  (*andAxiom2)[1] = toEquality(y, true);
  andAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom2, prb.units());

  Clause* andAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom3)[0] = toEquality(AH::app2(AH::conj(), x, y), true);  
  (*andAxiom3)[1] = toEquality(x, false);
  (*andAxiom3)[2] = toEquality(y, false);
  andAxiom3->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(andAxiom3, prb.units());

  Clause* orAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom1)[0] = toEquality(AH::app2(AH::disj(), x, y), true);
  (*orAxiom1)[1] = toEquality(x, false);
  orAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom1, prb.units());

  Clause* orAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom2)[0] = toEquality(AH::app2(AH::disj(), x, y), true);
  (*orAxiom2)[1] = toEquality(y, false);
  orAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom2, prb.units());

  Clause* orAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom3)[0] = toEquality(AH::app2(AH::disj(), x, y), false);  
  (*orAxiom3)[1] = toEquality(x, true);
  (*orAxiom3)[2] = toEquality(y, true);
  orAxiom3->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom3, prb.units()); 
  

  //TODO iff and xor

  if (env.options->showPreprocessing()) {
    env.out() << "Added proxy axioms: " << std::endl;
    env.out() << eqAxiom1->toString() << std::endl;
    env.out() << eqAxiom2->toString() << std::endl;
    env.out() << notAxiom1->toString() << std::endl;
    env.out() << notAxiom2->toString() << std::endl;  
    env.out() << piAxiom1->toString() << std::endl;
    env.out() << piAxiom2->toString() << std::endl;            
    env.out() << sigmaAxiom1->toString() << std::endl;
    env.out() << sigmaAxiom2->toString() << std::endl;
    env.out() << impAxiom1->toString() << std::endl;  
    env.out() << impAxiom2->toString() << std::endl;
    env.out() << impAxiom3->toString() << std::endl;  
    env.out() << andAxiom1->toString() << std::endl;  
    env.out() << andAxiom2->toString() << std::endl;
    env.out() << andAxiom3->toString() << std::endl;   
    env.out() << orAxiom1->toString() << std::endl;  
    env.out() << orAxiom2->toString() << std::endl;
    env.out() << orAxiom3->toString() << std::endl;      
  }
    
}
 
Literal* LambdaConversion::toEquality(TermList booleanTerm, bool polarity) {
  TermList boolVal = polarity ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
  return Literal::createEquality(true, booleanTerm, boolVal, AtomicSort::boolSort());
}

#endif

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

  VarToIndexMap map;
  return convertLambda(formula, map);
}

TermList LambdaConversion::convertLambda(Formula* formula, VarToIndexMap& map)
{
  CALL("LambdaConversion::convertLambda(Formula*)/2");

  TermList appTerm; //The resulting term to be pushed onto _toBeProcessed 
  TermList constant; //The HOL constant for various connectives

  Connective conn = formula->connective();
                                        
  switch(conn){
    case LITERAL: {
      Literal* lit = formula->literal();
      ASS(lit->isEquality()); //Is this a valid assumption?
    
      TermList lhs = convertLambda(*lit->nthArgument(0), map);
      TermList rhs = convertLambda(*lit->nthArgument(1), map);           
                
      TermList equalsSort = SortHelper::getEqualityArgumentSort(lit);
      
      unsigned eqProxy = env.signature->getEqualityProxy();
      constant = TermList(Term::create1(eqProxy, equalsSort));             
      appTerm = AH::createAppTerm3(sortOf(constant), constant, lhs, rhs);
      
      if(!lit->polarity()){
        constant = TermList(Term::createConstant(env.signature->getNotProxy()));
        appTerm = AH::createAppTerm(sortOf(constant), constant, appTerm);
      }
      return appTerm;
    }
    case IFF:
    case IMP:
    case XOR:{
      Formula* lhs = formula->left();
      Formula* rhs = formula->right();
                    
      vstring name = (conn == IFF ? "vIFF" : (conn == IMP ? "vIMP" : "vXOR"));
      constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));

      TermList form1 = convertLambda(lhs, map);
      TermList form2 = convertLambda(rhs, map);

      return AH::createAppTerm3(sortOf(constant), constant, form1, form2);;
    }
    case AND:
    case OR:{
      FormulaList::Iterator argsIt(formula->args());
      
      vstring name = (conn == AND ? "vAND" : "vOR");
      constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));
      
      TermList form;
      unsigned count = 1;
      while(argsIt.hasNext()){
        Formula* arg = argsIt.next();
        form = convertLambda(arg, map);
        if(count == 1){
          appTerm = AH::createAppTerm(sortOf(constant), constant, form);
        }else if(count == 2){
          appTerm = AH::createAppTerm(sortOf(appTerm), appTerm, form);
        }else{
          appTerm = AH::createAppTerm3(sortOf(constant), constant, appTerm, form);
        }
        count++;
      }
      return appTerm;                           
    }
    case NOT: {
      constant = TermList(Term::createConstant(env.signature->getNotProxy()));
      TermList form = convertLambda(formula->uarg(), map);
      return  AH::createAppTerm(sortOf(constant), constant, form);                                                    
    }
    case FORALL:
    case EXISTS: {
      VList* vars = formula->vars();
      VList::Iterator vit(vars);
      SList* sort = SList::singleton(TermList(0, true)); //dummy data
      VList* var = VList::singleton(0);

      TermList form = convertLambda(formula->qarg(), map);
      vstring name = (conn == FORALL ? "vPI" : "vSIGMA");
      unsigned proxy = env.signature->getPiSigmaProxy(name);

      TermList s;
      while(vit.hasNext()){
        int v = vit.next();
        ALWAYS(SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        var->setHead(v);
        sort->setHead(s);
        form = convertLambda(TermList(Term::createLambda(form, var, sort, AtomicSort::boolSort())), map); 
        constant = TermList(Term::create1(proxy, s));
        form = AH::createAppTerm(sortOf(constant), constant, form);
      }
      return form;
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

  return AH::createAppTerm(s1, s2, convertLambda(arg1, map), convertLambda(arg2, map));
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
  return AH::createLambdaTerm(s, bodySort, converted);
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
 
  auto srtOf = [] (TermList t) { 
     ASS(t.isTerm());
     return SortHelper::getResultSort(t.term());
  };

  TermList alpha = TermList(0, false);
  TermList beta = TermList(1, false);
  TermList x = TermList(2, false);
  TermList y = TermList(3, false);
  unsigned diff = env.signature->getDiff();

  TermList diffT = TermList(Term::create2(diff, alpha, beta));
  TermList diffTApplied = AH::createAppTerm3(srtOf(diffT), diffT, x, y);
  TermList lhs = AH::createAppTerm(alpha, beta, x, diffTApplied);
  TermList rhs = AH::createAppTerm(alpha, beta, y, diffTApplied);

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
  TermList choiceTApplied = AH::createAppTerm(alphaBool, alpha, choiceT, p);
  TermList px = AH::createAppTerm(alpha, boolS, p, x);
  TermList pchoiceT = AH::createAppTerm(alpha, boolS, p, choiceTApplied);

  Clause* choiceAx = new(2) Clause(2, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::CHOICE_AXIOM));
  (*choiceAx)[0] = Literal::createEquality(true, px, TermList(Term::foolFalse()), boolS);
  (*choiceAx)[1] = Literal::createEquality(true, pchoiceT, TermList(Term::foolTrue()), boolS);
  UnitList::push(choiceAx, prb.units());


  if (env.options->showPreprocessing()) {
    env.out() << "Added Hilbert choice axiom: " << std::endl;
    env.out() << choiceAx->toString() << std::endl;       
  }
}

void LambdaConversion::addProxyAxioms(Problem& prb)
{
  CALL("LambdaConversion::addProxyAxioms");   

  auto srtOf = [] (TermList t) { 
    ASS(t.isTerm());
    return SortHelper::getResultSort(t.term());
  };

  TermList s1 = TermList(0, false);  
  TermList x = TermList(1, false);
  TermList y = TermList(2, false);

  TermList choiceSort = AtomicSort::arrowSort(AtomicSort::arrowSort(s1, AtomicSort::boolSort()), s1);
  unsigned skolem1 = Skolem::addSkolemFunction(1,1,0, choiceSort);
  unsigned skolem2 = Skolem::addSkolemFunction(1,1,0, choiceSort);
  TermList sk1 = TermList(Term::create1(skolem1, s1));
  TermList sk2 = TermList(Term::create1(skolem2, s1));

  unsigned eqProxy = env.signature->getEqualityProxy();
  TermList constant = TermList(Term::create1(eqProxy, s1));

  Clause* eqAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  (*eqAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*eqAxiom1)[1] = Literal::createEquality(false,x,y,s1); 
  eqAxiom1->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(eqAxiom1, prb.units());

  Clause* eqAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  (*eqAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*eqAxiom2)[1] = Literal::createEquality(true,x,y,s1); 
  eqAxiom2->inference().setProxyAxiomsDescendant(true);   
  UnitList::push(eqAxiom2, prb.units());

  unsigned notProxy = env.signature->getNotProxy();
  constant = TermList(Term::createConstant(notProxy));

  Clause* notAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  (*notAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true);
  (*notAxiom1)[1] = toEquality(x, true);
  notAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom1, prb.units());

  Clause* notAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  (*notAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*notAxiom2)[1] = toEquality(x, false);
  notAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom2, prb.units());  

  unsigned piProxy = env.signature->getPiSigmaProxy("vPI");
  constant = TermList(Term::create1(piProxy, s1));

  Clause* piAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  (*piAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true);
  (*piAxiom1)[1] = toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, AH::createAppTerm(srtOf(sk1), sk1, x)), false);
  piAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(piAxiom1, prb.units());

  Clause* piAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  (*piAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*piAxiom2)[1] = toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, y), true);
  piAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(piAxiom2, prb.units());  

  unsigned sigmaProxy = env.signature->getPiSigmaProxy("vSIGMA");
  constant = TermList(Term::create1(sigmaProxy, s1));

  Clause* sigmaAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  (*sigmaAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true); 
  (*sigmaAxiom1)[1] = toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, y), false);
  sigmaAxiom1->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(sigmaAxiom1, prb.units());

  Clause* sigmaAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  (*sigmaAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*sigmaAxiom2)[1] = toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, AH::createAppTerm(srtOf(sk2), sk2, x)), true);
  sigmaAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(sigmaAxiom2, prb.units()); 

  unsigned impProxy = env.signature->getBinaryProxy("vIMP");
  constant = TermList(Term::createConstant(impProxy));

  Clause* impAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*impAxiom1)[1] = toEquality(x, true);
  impAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(impAxiom1, prb.units());

  Clause* impAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*impAxiom2)[1] = toEquality(y, false);
  impAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(impAxiom2, prb.units());

  Clause* impAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  (*impAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);  
  (*impAxiom3)[1] = toEquality(x, false);
  (*impAxiom3)[2] = toEquality(y, true);
  impAxiom3->inference().setProxyAxiomsDescendant(true);
  UnitList::push(impAxiom3, prb.units());

  unsigned andProxy = env.signature->getBinaryProxy("vAND");
  constant = TermList(Term::createConstant(andProxy));

  Clause* andAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*andAxiom1)[1] = toEquality(x, true);
  andAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom1, prb.units());

  Clause* andAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*andAxiom2)[1] = toEquality(y, true);
  andAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom2, prb.units());

  Clause* andAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  (*andAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);  
  (*andAxiom3)[1] = toEquality(x, false);
  (*andAxiom3)[2] = toEquality(y, false);
  andAxiom3->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(andAxiom3, prb.units());

  unsigned orProxy = env.signature->getBinaryProxy("vOR");
  constant = TermList(Term::createConstant(orProxy));

  Clause* orAxiom1 = new(2) Clause(2, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*orAxiom1)[1] = toEquality(x, false);
  orAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom1, prb.units());

  Clause* orAxiom2 = new(2) Clause(2, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*orAxiom2)[1] = toEquality(y, false);
  orAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom2, prb.units());

  Clause* orAxiom3 = new(3) Clause(3, TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  (*orAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);  
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

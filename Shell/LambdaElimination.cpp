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
 * Takes a single lambda term and eliminates the lambda(s)
 * from the term by translating to combinatory logic.
 * A term of the form ^[X, Y, Z]:exp is interpreted as:
 * ^[X]:(^[Y]:(^[Z]:exp)). I.e. as three lambdas in a single term.
 */
 

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
#include "Kernel/SKIKBO.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"

#include "Skolem.hpp"
#include "Options.hpp"
//#include "Shell/SymbolOccurrenceReplacement.hpp"


#include "LambdaElimination.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

typedef ApplicativeHelper AH;


/**
 * Return true if t1 is less than t2 in some arbitrary
 * total ordering.
 *
 * Is used just for normalization of commutative term and
 * literal arguments.
 */
bool LambdaElimination::TermListComparator::lessThan(TermList t1, TermList t2)
{
  if(t1.tag()!=t2.tag()) {
    return t1.tag() < t2.tag();
  }
  if(!t2.isTerm()) {
    return t2.content() > t1.content();
  }
  Term* trm1=t1.term();
  Term* trm2=t2.term();
  if(trm1->functor()!=trm2->functor()) {
    return trm1->functor()<trm2->functor();
  }
  if(trm1->weight()!=trm2->weight()) {
    return trm1->weight()<trm2->weight();
  }
  if(trm1->numVarOccs()!=trm2->numVarOccs()) {
    return trm1->numVarOccs()<trm2->numVarOccs();
  }

  //To avoid non-determinism, now we'll compare the terms lexicographicaly.
  static DisagreementSetIterator dsit;
  dsit.reset(trm1, trm2, false);

  if(!dsit.hasNext()) {
    ASS_EQ(trm1,trm2);
    return false;
  }

  pair<TermList, TermList> diff=dsit.next();
  TermList st1=diff.first;
  TermList st2=diff.second;
  if(st1.isTerm()) {
    if(st2.isTerm()) {
      unsigned f1=st1.term()->functor();
      unsigned f2=st2.term()->functor();
      ASS_NEQ(f1,f2);
      return f1<f2;
    } else {
      return false;
    }
  } else {
    if(st2.isTerm()) {
      return true;
    } else {
      ASS_NEQ(st1.var(),st2.var());
      return st1.var()<st2.var();
    }
  }
  ASSERTION_VIOLATION;
  return false;
}


TermList LambdaElimination::elimLambda(Formula* formula)
{
  TermList appTerm; //The resulting term to be pushed onto _toBeProcessed 
  TermList constant; //The HOL constant for various connectives

  Connective conn = formula->connective();
                                        
  switch(conn){
    case LITERAL: {
      Literal* lit = formula->literal();
      ASS(lit->isEquality()); //Is this a valid assumption?
    
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);                                

      if (lhs.isTerm()) { lhs = elimLambda(lhs); }
      if (rhs.isTerm()) { rhs = elimLambda(rhs); }            
                
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
                    
      std::string name = (conn == IFF ? "vIFF" : (conn == IMP ? "vIMP" : "vXOR"));
      constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));

      TermList form1 = elimLambda(lhs);
      TermList form2 = elimLambda(rhs);

      /*TermListComparator tlc;
      if((conn == IFF || conn == XOR) && tlc.lessThan(form2, form1)){
        TermList temp = form1;
        form1 = form2;
        form2 = temp;
      }*/

      return AH::createAppTerm3(sortOf(constant), constant, form1, form2);;
    }
    case AND:
    case OR:{
      FormulaList::Iterator argsIt(formula->args());
      
      std::string name = (conn == AND ? "vAND" : "vOR");
      constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));
      
      /*TermListComparator tlc;
      unsigned length = FormulaList::length(formula->args());
      Sort<TermList,TermListComparator> srt(length, tlc);
      while(argsIt.hasNext()){
        srt.add(processBeyondLambda(argsIt.next()));
      }
      srt.sort();

      appTerm = AH::createAppTerm3(sortOf(constant), constant, srt[0], srt[1]);
      for(unsigned i = 2; i < length; i++){
        appTerm = AH::createAppTerm3(sortOf(constant), constant, appTerm, srt[i]);
      }*/
      TermList form;
      unsigned count = 1;
      while(argsIt.hasNext()){
        Formula* arg = argsIt.next();
        form = elimLambda(arg);
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
      TermList form = elimLambda(formula->uarg());
      return  AH::createAppTerm(sortOf(constant), constant, form);                                                    
    }
    case FORALL:
    case EXISTS: {
      VList* vars = formula->vars();
      VList::Iterator vit(vars);
      SList* sort = SList::singleton(TermList(0, true)); //dummy data
      VList* var = VList::singleton(0);

      TermList form = elimLambda(formula->qarg());
      std::string name = (conn == FORALL ? "vPI" : "vSIGMA");
      unsigned proxy = env.signature->getPiSigmaProxy(name);

      TermList s;
      while(vit.hasNext()){
        int v = vit.next();
        ALWAYS(SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        var->setHead(v);
        sort->setHead(s);
        form = elimLambda(Term::createLambda(form, var, sort, AtomicSort::boolSort())); 
        constant = TermList(Term::create1(proxy, s));
        form = AH::createAppTerm(sortOf(constant), constant, form);
      }
      return form;
    }
    case BOOL_TERM:
      return elimLambda(formula->getBooleanTerm());
    case TRUE:
      return TermList(Term::foolTrue());
    case FALSE:
      return TermList(Term::foolFalse());
    default:
      ASSERTION_VIOLATION;
    
  }//switch conn             
}   

TermList LambdaElimination::elimLambda(TermList term)
{
  if(term.isVar()){
    return term;
  }

  Term* t = term.term();
  if(t->isSpecial()){   
    switch(t->specialFunctor()){
      case SpecialFunctor::FORMULA: 
        return elimLambda(t->getSpecialData()->getFormula());

      case SpecialFunctor::LAMBDA:{
        Stack<int> vars;
        TermStack sorts;
        Term::SpecialTermData* sd = t->getSpecialData();
        SList* srts = sd->getLambdaVarSorts();
        VList* vrs = sd->getLambdaVars();
        
        VList::Iterator vlit(vrs);
        SList::Iterator slit(srts);

        while(vlit.hasNext()){
          vars.push(vlit.next());
          sorts.push(slit.next());
        }
        TermList eliminated = elimLambda(vars, sorts, sd->getLambdaExp(), sd->getLambdaExpSort());
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

  return AH::createAppTerm(s1, s2, elimLambda(arg1), elimLambda(arg2));
}


TermList LambdaElimination::elimLambda(Stack<int>& vars, TermStack& sorts, 
                                       TermList body, TermList sort)
{
  TermList bodye = elimLambda(body);
  // Lambda elimination should not change the sort
  // of a term
  ASS(bodye.isVar() || sortOf(bodye) == sort);

  while(vars.size()){
    int v = vars.pop();
    TermList s = sorts.pop();
    bodye = elimLambda(v, s, bodye, sort);
    sort = AtomicSort::arrowSort(s, sort);
  }

  return bodye;
}


TermList LambdaElimination::elimLambda(int var, TermList varSort,
                                       TermList body, TermList sort)
{
  using Kernel::isFreeVariableOf;

  if(!isFreeVariableOf(body,var)){
    return createKTerm(sort, varSort, body);
  }

  if(body.isVar()){
    ASS(body.var() == (unsigned)var);
    return TermList(Term::create1(env.signature->getCombinator(Signature::I_COMB), varSort));
  }

  Term* t = body.term();
  // Specials should already have been removed via earlier
  // recursive calls
  ASS_REP(!t->isSpecial(), t->toString());

  //must be of the form app(s1, s2, arg1, arg2)
  TermList s1 = *t->nthArgument(0);
  TermList s2 = *t->nthArgument(1);
  TermList arg1 = *t->nthArgument(2);
  TermList arg2 = *t->nthArgument(3);
  TermList a1sort = AtomicSort::arrowSort(s1, s2);
  TermList a2sort = s1;

  bool freeInArg1 = isFreeVariableOf(arg1,var);
  bool freeInArg2 = isFreeVariableOf(arg2,var);

  if(arg2.isVar() && (arg2.var() == (unsigned)var) && !freeInArg1){
    //This is the case [\x. exp @ x] wehere x is not free in exp.
    return arg1;
  }

  if (freeInArg1 && freeInArg2){
    TermList arg1e = elimLambda(var, varSort, arg1, a1sort);
    TermList s1e = AtomicSort::arrowSort(varSort, a1sort);
    TermList arg2e = elimLambda(var, varSort, arg2, a2sort);
    TermList s2e = AtomicSort::arrowSort(varSort, a2sort);
    return createSCorBTerm(arg1e, s1e, arg2e, s2e, Signature::S_COMB);
  } else if (freeInArg1) {
    TermList arg1e = elimLambda(var, varSort, arg1, a1sort);
    TermList s1e = AtomicSort::arrowSort(varSort, a1sort);
    return createSCorBTerm(arg1e, s1e, arg2, a2sort, Signature::C_COMB);
  } else{
    ASS(freeInArg2);
    TermList arg2e = elimLambda(var, varSort, arg2, a2sort); 
    TermList s2e = AtomicSort::arrowSort(varSort, a2sort);     
    return createSCorBTerm(arg1, a1sort, arg2e, s2e, Signature::B_COMB);
  }
}

TermList LambdaElimination::elimLambda(Term* lambdaTerm)
{
  return elimLambda(TermList(lambdaTerm));
}

TermList LambdaElimination::createKTerm(TermList s1, TermList s2, TermList arg1)
{
  unsigned kcomb = env.signature->getCombinator(Signature::K_COMB);
  TermList res = TermList(Term::create2(kcomb, s1, s2));
  return AH::createAppTerm(sortOf(res), res, arg1);             
}   
    
TermList LambdaElimination::createSCorBTerm(TermList arg1, TermList arg1sort, 
                                            TermList arg2, TermList arg2sort, Signature::Combinator comb)
{
  TermList s1, s2, s3;
  unsigned cb = env.signature->getCombinator(comb);
  
  if(comb == Signature::S_COMB || comb == Signature::C_COMB){
    s1 = AH::getNthArg(arg1sort, 1);
    s2 = AH::getNthArg(arg1sort, 2);
    s3 = AH::getResultApplieadToNArgs(arg1sort, 2);
  } else {
    s1 = AH::getNthArg(arg2sort, 1);
    s2 = AH::getNthArg(arg1sort, 1);
    s3 = AH::getResultApplieadToNArgs(arg1sort, 1);
  }
  
  TermList args[] = {s1, s2, s3};
  TermList c = TermList(Term::create(cb, 3, args));
  return AH::createAppTerm3(sortOf(c), c, arg1, arg2); 
}

TermList LambdaElimination::sortOf(TermList t)
{
  ASS(t.isTerm());
  return SortHelper::getResultSort(t.term());
}

void LambdaElimination::addCombinatorAxioms(Problem& prb)
{
  auto srtOf = [] (TermList t) { 
     ASS(t.isTerm());
     return SortHelper::getResultSort(t.term());
  };

  TermList s1 = TermList(0, false);  
  TermList s2 = TermList(1, false);
  TermList s3 = TermList(2, false);
  TermList x = TermList(3, false);
  TermList y = TermList(4, false);
  TermList z = TermList(5, false);
  TermList args[] = {s1, s2, s3};
  
  unsigned s_comb = env.signature->getCombinator(Signature::S_COMB);
  TermList constant = TermList(Term::create(s_comb, 3, args));
  TermList lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  TermList rhs = AH::createAppTerm3(AtomicSort::arrowSort(s1, s2, s3), x, z, AH::createAppTerm(AtomicSort::arrowSort(s1, s2), y, z));

  Clause* sAxiom = Clause::fromLiterals({Literal::createEquality(true, lhs, rhs, s3)},
      TheoryAxiom(InferenceRule::COMBINATOR_AXIOM) );
  sAxiom->inference().setCombAxiomsDescendant(true);
  UnitList::push(sAxiom, prb.units());

  unsigned c_comb = env.signature->getCombinator(Signature::C_COMB);
  constant = TermList(Term::create(c_comb, 3, args));
  lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  rhs = AH::createAppTerm3(AtomicSort::arrowSort(s1, s2, s3), x, z, y);

  Clause* cAxiom = Clause::fromLiterals({ Literal::createEquality(true, lhs, rhs, s3) },
    TheoryAxiom(InferenceRule::COMBINATOR_AXIOM));
  cAxiom->inference().setCombAxiomsDescendant(true);
  UnitList::push(cAxiom, prb.units());
     
  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  constant = TermList(Term::create(b_comb, 3, args));
  lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  rhs = AH::createAppTerm(AtomicSort::arrowSort(s2, s3), x, AH::createAppTerm(AtomicSort::arrowSort(s1, s2), y, z));

  Clause* bAxiom = Clause::fromLiterals({Literal::createEquality(true, lhs, rhs, s3)}, 
      TheoryAxiom(InferenceRule::COMBINATOR_AXIOM));
  bAxiom->inference().setCombAxiomsDescendant(true);
  UnitList::push(bAxiom, prb.units());

  unsigned k_comb = env.signature->getCombinator(Signature::K_COMB);
  constant = TermList(Term::create2(k_comb, s1, s2));
  lhs = AH::createAppTerm3(srtOf(constant), constant, x, y);
  
  Clause* kAxiom = Clause::fromLiterals({ Literal::createEquality(true, lhs, x, s1) }, 
      TheoryAxiom(InferenceRule::COMBINATOR_AXIOM));
  bAxiom->inference().setCombAxiomsDescendant(true);
  UnitList::push(kAxiom, prb.units());

  unsigned i_comb = env.signature->getCombinator(Signature::I_COMB);
  constant = TermList(Term::create1(i_comb, s1));
  lhs = AH::createAppTerm(srtOf(constant), constant, x);
  
  Clause* iAxiom = Clause::fromLiterals({ Literal::createEquality(true, lhs, x, s1) }, 
      TheoryAxiom(InferenceRule::COMBINATOR_AXIOM));
  iAxiom->inference().setCombAxiomsDescendant(true);  
  UnitList::push(iAxiom, prb.units());

  if (env.options->showPreprocessing()) {
    std::cout << "Added combinator axioms: " << std::endl;
    std::cout << sAxiom->toString() << std::endl;
    std::cout << cAxiom->toString() << std::endl;
    std::cout << bAxiom->toString() << std::endl;
    std::cout << kAxiom->toString() << std::endl;
    std::cout << iAxiom->toString() << std::endl;
  }
}


void LambdaElimination::addFunctionExtensionalityAxiom(Problem& prb)
{
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

  Clause* funcExtAx = Clause::fromLiterals(
      { Literal::createEquality(false, lhs, rhs, beta),
        Literal::createEquality(true, x, y, AtomicSort::arrowSort(alpha, beta)) },
      NonspecificInference0(UnitInputType::AXIOM,InferenceRule::FUNC_EXT_AXIOM));
  UnitList::push(funcExtAx, prb.units());


  if (env.options->showPreprocessing()) {
    std::cout << "Added functional extensionality axiom: " << std::endl;
    std::cout << funcExtAx->toString() << std::endl;
  }
}

void LambdaElimination::addChoiceAxiom(Problem& prb)
{
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

  Clause* choiceAx = Clause::fromLiterals(
      { Literal::createEquality(true, px, TermList(Term::foolFalse()), boolS),
        Literal::createEquality(true, pchoiceT, TermList(Term::foolTrue()), boolS) },
      NonspecificInference0(UnitInputType::AXIOM,InferenceRule::CHOICE_AXIOM));
  UnitList::push(choiceAx, prb.units());


  if (env.options->showPreprocessing()) {
    std::cout << "Added Hilbert choice axiom: " << std::endl;
    std::cout << choiceAx->toString() << std::endl;
  }
}

void LambdaElimination::addProxyAxioms(Problem& prb)
{
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

  Clause* eqAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      Literal::createEquality(false,x,y,s1) },
    TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  eqAxiom1->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(eqAxiom1, prb.units());

  Clause* eqAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false),
      Literal::createEquality(true,x,y,s1) },
    TheoryAxiom(InferenceRule::EQUALITY_PROXY_AXIOM));
  eqAxiom2->inference().setProxyAxiomsDescendant(true);   
  UnitList::push(eqAxiom2, prb.units());

  unsigned notProxy = env.signature->getNotProxy();
  constant = TermList(Term::createConstant(notProxy));

  Clause* notAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), true),
      toEquality(x, true) },
    TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  notAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom1, prb.units());

  Clause* notAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), false),
      toEquality(x, false) },
    TheoryAxiom(InferenceRule::NOT_PROXY_AXIOM));
  notAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom2, prb.units());  

  unsigned piProxy = env.signature->getPiSigmaProxy("vPI");
  constant = TermList(Term::create1(piProxy, s1));

  Clause* piAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), true),
      toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, AH::createAppTerm(srtOf(sk1), sk1, x)), false) },
    TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  piAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(piAxiom1, prb.units());

  Clause* piAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), false),
      toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, y), true) },
    TheoryAxiom(InferenceRule::PI_PROXY_AXIOM));
  piAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(piAxiom2, prb.units());  

  unsigned sigmaProxy = env.signature->getPiSigmaProxy("vSIGMA");
  constant = TermList(Term::create1(sigmaProxy, s1));

  Clause* sigmaAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), true),
      toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, y), false) },
    TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  sigmaAxiom1->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(sigmaAxiom1, prb.units());

  Clause* sigmaAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm(srtOf(constant), constant, x), false),
      toEquality(AH::createAppTerm(s1, AtomicSort::boolSort(), x, AH::createAppTerm(srtOf(sk2), sk2, x)), true) },
    TheoryAxiom(InferenceRule::SIGMA_PROXY_AXIOM));
  sigmaAxiom2->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(sigmaAxiom2, prb.units()); 

  unsigned impProxy = env.signature->getBinaryProxy("vIMP");
  constant = TermList(Term::createConstant(impProxy));

  Clause* impAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      toEquality(x, true) },
    TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  impAxiom1->inference().setProxyAxiomsDescendant(true);    
  UnitList::push(impAxiom1, prb.units());

  Clause* impAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      toEquality(y, false) },
    TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  impAxiom2->inference().setProxyAxiomsDescendant(true);      
  UnitList::push(impAxiom2, prb.units());

  Clause* impAxiom3 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false),
      toEquality(x, false) ,
      toEquality(y, true) },
    TheoryAxiom(InferenceRule::IMPLIES_PROXY_AXIOM));
  impAxiom3->inference().setProxyAxiomsDescendant(true);
  UnitList::push(impAxiom3, prb.units());

  unsigned andProxy = env.signature->getBinaryProxy("vAND");
  constant = TermList(Term::createConstant(andProxy));

  Clause* andAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false),
      toEquality(x, true) },
    TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  andAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom1, prb.units());

  Clause* andAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false),
      toEquality(y, true) },
    TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  andAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom2, prb.units());

  Clause* andAxiom3 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      toEquality(x, false),
      toEquality(y, false) },
    TheoryAxiom(InferenceRule::AND_PROXY_AXIOM));
  andAxiom3->inference().setProxyAxiomsDescendant(true);  
  UnitList::push(andAxiom3, prb.units());

  unsigned orProxy = env.signature->getBinaryProxy("vOR");
  constant = TermList(Term::createConstant(orProxy));

  Clause* orAxiom1 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      toEquality(x, false) },
    TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  orAxiom1->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom1, prb.units());

  Clause* orAxiom2 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true),
      toEquality(y, false) },
    TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  orAxiom2->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom2, prb.units());

  Clause* orAxiom3 = Clause::fromLiterals(
    { toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false),
      toEquality(x, true),
      toEquality(y, true) },
    TheoryAxiom(InferenceRule::OR_PROXY_AXIOM));
  orAxiom3->inference().setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom3, prb.units()); 
  

  //TODO iff and xor

  if (env.options->showPreprocessing()) {
    std::cout << "Added proxy axioms: " << std::endl;
    std::cout << eqAxiom1->toString() << std::endl;
    std::cout << eqAxiom2->toString() << std::endl;
    std::cout << notAxiom1->toString() << std::endl;
    std::cout << notAxiom2->toString() << std::endl;
    std::cout << piAxiom1->toString() << std::endl;
    std::cout << piAxiom2->toString() << std::endl;
    std::cout << sigmaAxiom1->toString() << std::endl;
    std::cout << sigmaAxiom2->toString() << std::endl;
    std::cout << impAxiom1->toString() << std::endl;
    std::cout << impAxiom2->toString() << std::endl;
    std::cout << impAxiom3->toString() << std::endl;
    std::cout << andAxiom1->toString() << std::endl;
    std::cout << andAxiom2->toString() << std::endl;
    std::cout << andAxiom3->toString() << std::endl;
    std::cout << orAxiom1->toString() << std::endl;
    std::cout << orAxiom2->toString() << std::endl;
    std::cout << orAxiom3->toString() << std::endl;
  }
}

Literal* LambdaElimination::toEquality(TermList booleanTerm, bool polarity) {
  TermList boolVal = polarity ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
  return Literal::createEquality(true, booleanTerm, boolVal, AtomicSort::boolSort());
}

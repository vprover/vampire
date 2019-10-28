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

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/SKIKBO.hpp"

#include "Skolem.hpp"
#include "Options.hpp"
//#include "Shell/SymbolOccurrenceReplacement.hpp"


#include "LambdaElimination.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

typedef ApplicativeHelper AH;


/*void LambdaElimination::addFunctionExtensionalityAxioms(UnitList*& units){
  CALL("LambdaElimination::addFunctionExtensionalityAxioms");


}*/

/*void LambdaElimination::addBooleanExtensionalityAxiom(UnitList*& units){
  CALL("LambdaElimination::addBooleanExtensionalityAxiom");
   
  Formula* boolExtAxiom;  
  
  TermList var1 = TermList(0, false);
  TermList var2 = TermList(1, false);
  List<int>* varList = new List<int>(var1.var());
  List<unsigned>* sortList = new List<unsigned>(Sorts::SRT_BOOL);
  varList = varList->addLast(varList, var2.var());
  sortList = sortList->addLast(sortList, Sorts::SRT_BOOL);

  boolExtAxiom = new BinaryFormula(IFF, toEquality(var1) , toEquality(var2));
  boolExtAxiom = new BinaryFormula(IMP, boolExtAxiom , createEquality(var1, var2, Sorts::SRT_BOOL));
  boolExtAxiom = new QuantifiedFormula(FORALL, varList,sortList, boolExtAxiom); 

  Inference* boolExtInf;
  boolExtInf = new Inference(Inference::BOOL_EXT_AXIOM);
  
  addAxiom(new FormulaUnit(boolExtAxiom, boolExtInf, Unit::AXIOM), true);  
  
  addAxiomsToUnits(units);
  return;  
  
}*/


TermList LambdaElimination::processBeyondLambda(Formula* formula)
{
  CALL("LambdaElimination::processBeyondLambda(Formula*)");

  TermList appTerm; //The resulting term to be pushed onto _toBeProcessed 
  TermList constant; //The HOL constant for various connectives

  Connective conn = formula->connective();
                                        
  switch(conn){
    case LITERAL: {
      Literal* lit = formula->literal();
      ASS(lit->isEquality()); //Is this a valid assumption?
    
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);                                

      if (lhs.isTerm()) { lhs = processBeyondLambda(lhs.term()); }
      if (rhs.isTerm()) { rhs = processBeyondLambda(rhs.term()); }            
                
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

      TermList form1 = processBeyondLambda(lhs);
      TermList form2 = processBeyondLambda(rhs);
 
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
        form = processBeyondLambda(arg);
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
      TermList form = processBeyondLambda(formula->uarg());
      return  AH::createAppTerm(sortOf(constant), constant, form);                                                    
    }
    case FORALL:
    case EXISTS: {
      Formula::VarList* vars = formula->vars();
      Formula::VarList::Iterator vit(vars);
      SList* sort = new SList(TermList(0, true)); //dummy data
      IntList* var = new IntList(0);

      TermList form = processBeyondLambda(formula->qarg());
      vstring name = (conn == FORALL ? "vPI" : "vSIGMA");
      unsigned proxy = env.signature->getPiSigmaProxy(name);

      TermList s;
      while(vit.hasNext()){
        int v = vit.next();
        ALWAYS(SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        var->setHead(v);
        sort->setHead(s);
        form = elimLambda(Term::createLambda(form, var, sort, Term::boolSort())); 
        constant = TermList(Term::create1(proxy, s));
        form = AH::createAppTerm(sortOf(constant), constant, form);
      }
      return form;
    }
    case BOOL_TERM:
      return processBeyondLambda(formula->getBooleanTerm());
    case TRUE:
      return TermList(Term::foolTrue());
    case FALSE:
      return TermList(Term::foolFalse());
    default:
      ASSERTION_VIOLATION;
    
  }//switch conn             
}   

/** Function removes all apps, lambdas and top level connectives from
  * a lambda expression via 
  */  
  
TermList LambdaElimination::processBeyondLambda(Term* term)
{
  CALL("LambdaElimination::processBeyondLambda(Term*)");

  TermList appTerm; //The resulting term to be pushed onto _toBeProcessed 

  if(term->isSpecial()){   
    switch(term->functor()){
      case Term::SF_FORMULA: 
        return processBeyondLambda(term->getSpecialData()->getFormula());
      case Term::SF_LAMBDA:
        return elimLambda(term);
      default:
        ASSERTION_VIOLATION;    
    }
  }
  
  if(env.signature->getFunction(term->functor())->app()){
    TermList s1 = *(term->nthArgument(0));
    TermList s2 = *(term->nthArgument(1));
    TermList arg1 = *(term->nthArgument(2));
    TermList arg2 = *(term->nthArgument(3));
    arg1 = processBeyondLambda(arg1);
    arg2 = processBeyondLambda(arg2);
    return AH::createAppTerm(s1, s2, arg1, arg2);
  } 
   
  return TermList(term); 
}   

TermList LambdaElimination::processBeyondLambda(TermList term)
{
  CALL("LambdaElimination::processBeyondLambda(TermList)");

  if(term.isVar()){
    return term;
  }
  return processBeyondLambda(term.term());
}


TermList LambdaElimination::elimLambda(Term* lambdaTerm)
{
  CALL("LambdaElimination::elimLambda");
  
  Stack<int> vars;
  TermStack sorts;
  TermStack toBeProcessed;

  ASS(lambdaTerm->isSpecial());
  Term::SpecialTermData* sd = lambdaTerm->getSpecialData();
  ASS_EQ(sd->getType(), Term::SF_LAMBDA);
  
  TermList lambdaExp;
  SList* srts = sd->getLambdaVarSorts();
  IntList* vrs = sd->getLambdaVars();
  
  IntList::Iterator vlit(vrs);
  SList::Iterator slit(srts);

  while(vlit.hasNext()){
    vars.push(vlit.next());
    sorts.push(slit.next());
  }

  lambdaExp = sd->getLambdaExp();
  toBeProcessed.push(lambdaExp);

  process(vars, sorts, toBeProcessed);    

  return _processed.pop();   
}


void LambdaElimination::process(Stack<int>& vars, TermStack& sorts, TermStack &toBeProcessed){
   
  CALL("LambdaElimination::process");   
  
  TermList processing;
  int lambdaVar;
  TermList lambdaVarSort;
  Stack<unsigned> argNums;
   
  while(!vars.isEmpty()){
    lambdaVar = vars.pop();
    lambdaVarSort = sorts.pop();
    
    while (!toBeProcessed.isEmpty()){  
   
      processing = toBeProcessed.pop(); 
      
      if (processing.isTerm()){ 
        
        Term* lExpTerm = processing.term();
        IntList* freeVars = lExpTerm->freeVariables();
        
        if(IntList::member(lambdaVar, freeVars)){
          if(lExpTerm->isSpecial()){ 
            toBeProcessed.push(processBeyondLambda(lExpTerm));   
          }
          else //not special. Of form app(s1, s2, t1, t2).
          {
            TermList arg1 = *lExpTerm->nthArgument(2);
            TermList arg2 = *lExpTerm->nthArgument(3);
            dealWithApp(arg1, arg2, lambdaVar, toBeProcessed, argNums);                
          }
        }
        else //In the case \x.exp where x is not free in exp.
        {
          TermList arg1 = processBeyondLambda(processing);
          addToProcessed(createKTerm(sortOf(arg1), lambdaVarSort, arg1), argNums);                  
        }
      }else{//lambda expression is a variable. If it is the lambda var, then this will be translated to I     
        if(processing.var() == (unsigned)lambdaVar){ //an expression of the form \x.x
          TermList ts = TermList(Term::create1(env.signature->getCombinator(Signature::I_COMB), lambdaVarSort));
          addToProcessed(ts, argNums);
        }else{ //an expression of the form \x.y 
          addToProcessed(createKTerm(sortOf(processing), lambdaVarSort, processing), argNums);
        }       
       //freeVars = List<unsigned>(sd->getLambdaExp().var());
      }
    }//of while
   
    if(!vars.isEmpty()){
      toBeProcessed.push(_processed.pop());     
    }

  }//outer while      
}


void LambdaElimination::addToProcessed(TermList ts, Stack<unsigned> &_argNums){
    CALL("LambdaElimination::addToProcessed");
  
    unsigned numOfArgs;
    _processed.push(ts);
    if(!_argNums.isEmpty()){
      numOfArgs = _argNums.pop();
      numOfArgs +=1;
    }else{
      return;
    }
    
    if(numOfArgs == 1){
      _argNums.push(numOfArgs);
      return;
    }else{
      while(true){
        Signature::Combinator comb = _combinators.pop();

        TermList arg1 = _processed.pop();   
        TermList arg2 = _processed.pop();
    
        if(comb == Signature::B_COMB){
          _processed.push(createSCorBTerm(arg2, arg1, comb));
        }else{
          _processed.push(createSCorBTerm(arg1, arg2, comb));
        }
        if(!_argNums.isEmpty()){
          numOfArgs = _argNums.pop();
          numOfArgs +=1;
          if(numOfArgs != 2){
            _argNums.push(numOfArgs);
            return;
          }
        }else{
          return;
        }
      }
    }
}


void LambdaElimination::dealWithApp(TermList lhs, TermList rhs, int lambdaVar, TermStack &toBeProcessed, Stack<unsigned> &argNums)
{
  CALL("LambdaElimination::dealWithApp");

  IntList* lhsFVs = lhs.freeVariables();
  IntList* rhsFVs = rhs.freeVariables();

  if(rhs.isVar() && (rhs.var() == (unsigned)lambdaVar) && !IntList::member(lambdaVar, lhsFVs)){
    //This is the case [\x. exp @ x] wehere x is not free in exp.
    lhs.isTerm() ? addToProcessed(processBeyondLambda(lhs.term()), argNums) : addToProcessed(lhs, argNums);
    return;
  }

  if ((IntList::member(lambdaVar, lhsFVs)) && (IntList::member(lambdaVar, rhsFVs))){
    _combinators.push(Signature::S_COMB);
    argNums.push(0);
    toBeProcessed.push(lhs);
    toBeProcessed.push(rhs); 
  }else if(IntList::member(lambdaVar, lhsFVs)){
    _combinators.push(Signature::C_COMB);
    argNums.push(0);
    toBeProcessed.push(lhs);
    rhs.isTerm() ? addToProcessed(processBeyondLambda(rhs.term()), argNums) : addToProcessed(rhs, argNums);  
  }else if(IntList::member(lambdaVar, rhsFVs)){
    _combinators.push(Signature::B_COMB);            
    argNums.push(0);
    toBeProcessed.push(rhs);
    lhs.isTerm() ? addToProcessed(processBeyondLambda(lhs.term()), argNums) : addToProcessed(lhs, argNums);   
  }     
}

TermList LambdaElimination::createKTerm(TermList s1, TermList s2, TermList arg1)
{
  CALL("LambdaElimination::createKTerm");
  
  unsigned kcomb = env.signature->getCombinator(Signature::K_COMB);
  TermList res = TermList(Term::create2(kcomb, s1, s2));
  res = AH::createAppTerm(sortOf(res), res, arg1);             
  return res;
}   
    
TermList LambdaElimination::createSCorBTerm(TermList arg1, TermList arg2, Signature::Combinator comb)
{
    CALL("LambdaElimination::createSCorBTerm");
    
    TermList s1, s2, s3;
    unsigned cb = env.signature->getCombinator(comb);
    TermList arg1sort = sortOf(arg1);
    TermList arg2sort = sortOf(arg2);
    
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
  CALL("LambdaElimination::sortOf");
  
  return SortHelper::getResultSort(t, _varSorts);
  
}

void LambdaElimination::addCombinatorAxioms(Problem& prb)
{
  CALL("LambdaElimination::addCombinatorAxioms"); 
 
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

  Inference* inf = new Inference(Inference::COMBINATOR_AXIOM);
  
  unsigned s_comb = env.signature->getCombinator(Signature::S_COMB);
  TermList constant = TermList(Term::create(s_comb, 3, args));
  TermList lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  TermList rhs = AH::createAppTerm3(Term::arrowSort(s1, s2, s3), x, z, AH::createAppTerm(Term::arrowSort(s1, s2), y, z));

  Clause* sAxiom = new(1) Clause(1, Unit::AXIOM, inf);
  (*sAxiom)[0] = Literal::createEquality(true, lhs, rhs, s3);
  sAxiom->setCombAxiomsDescendant(true);
  UnitList::push(sAxiom, prb.units());

  unsigned c_comb = env.signature->getCombinator(Signature::C_COMB);
  constant = TermList(Term::create(c_comb, 3, args));
  lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  rhs = AH::createAppTerm3(Term::arrowSort(s1, s2, s3), x, z, y);

  Clause* cAxiom = new(1) Clause(1, Unit::AXIOM, inf);
  (*cAxiom)[0] = Literal::createEquality(true, lhs, rhs, s3);
  cAxiom->setCombAxiomsDescendant(true);
  UnitList::push(cAxiom, prb.units());
     
  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  constant = TermList(Term::create(b_comb, 3, args));
  lhs = AH::createAppTerm(srtOf(constant), constant, x, y, z); //TODO fix
  rhs = AH::createAppTerm(Term::arrowSort(s2, s3), x, AH::createAppTerm(Term::arrowSort(s1, s2), y, z));

  Clause* bAxiom = new(1) Clause(1, Unit::AXIOM, inf);
  (*bAxiom)[0] = Literal::createEquality(true, lhs, rhs, s3);
  bAxiom->setCombAxiomsDescendant(true);
  UnitList::push(bAxiom, prb.units());

  unsigned k_comb = env.signature->getCombinator(Signature::K_COMB);
  constant = TermList(Term::create2(k_comb, s1, s2));
  lhs = AH::createAppTerm3(srtOf(constant), constant, x, y);
  
  Clause* kAxiom = new(1) Clause(1, Unit::AXIOM, inf);
  (*kAxiom)[0] = Literal::createEquality(true, lhs, x, s1);
  bAxiom->setCombAxiomsDescendant(true);
  UnitList::push(kAxiom, prb.units());

  unsigned i_comb = env.signature->getCombinator(Signature::I_COMB);
  constant = TermList(Term::create1(i_comb, s1));
  lhs = AH::createAppTerm(srtOf(constant), constant, x);
  
  Clause* iAxiom = new(1) Clause(1, Unit::AXIOM, inf);
  (*iAxiom)[0] = Literal::createEquality(true, lhs, x, s1);
  iAxiom->setCombAxiomsDescendant(true);  
  UnitList::push(iAxiom, prb.units());

  if (env.options->showPreprocessing()) {
    env.out() << "Added combinator axioms: " << std::endl;
    env.out() << sAxiom->toString() << std::endl;
    env.out() << cAxiom->toString() << std::endl;
    env.out() << bAxiom->toString() << std::endl;
    env.out() << kAxiom->toString() << std::endl;  
    env.out() << iAxiom->toString() << std::endl;        
  }
}


void LambdaElimination::addFunctionExtensionalityAxiom(Problem& prb)
{
  CALL("LambdaElimination::addFunctionExtensionalityAxiom"); 
 
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

  Inference* inf = new Inference(Inference::FUNC_EXT_AXIOM);

  Clause* funcExtAx = new(2) Clause(2, Unit::AXIOM, inf);
  (*funcExtAx)[0] = Literal::createEquality(false, lhs, rhs, beta);
  (*funcExtAx)[1] = Literal::createEquality(true, x, y, Term::arrowSort(alpha, beta));
  UnitList::push(funcExtAx, prb.units());


  if (env.options->showPreprocessing()) {
    env.out() << "Added functional extensionality axiom: " << std::endl;
    env.out() << funcExtAx->toString() << std::endl;       
  }
}

void LambdaElimination::addProxyAxioms(Problem& prb)
{
  CALL("LambdaElimination::addProxyAxioms");   

  auto srtOf = [] (TermList t) { 
    ASS(t.isTerm());
    return SortHelper::getResultSort(t.term());
  };

  TermList s1 = TermList(0, false);  
  TermList x = TermList(1, false);
  TermList y = TermList(2, false);
  TermList choiceSort = Term::arrowSort(Term::arrowSort(s1, Term::boolSort()), s1);
  unsigned skolem1 = Skolem::addSkolemFunction(1,0, choiceSort, new VList(0));
  unsigned skolem2 = Skolem::addSkolemFunction(1,0, choiceSort, new VList(0));
  TermList sk1 = TermList(Term::create1(skolem1, s1));
  TermList sk2 = TermList(Term::create1(skolem2, s1));

  Inference* inf = new Inference(Inference::EQUALITY_PROXY_AXIOM);
  unsigned eqProxy = env.signature->getEqualityProxy();
  TermList constant = TermList(Term::create1(eqProxy, s1));

  Clause* eqAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*eqAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*eqAxiom1)[1] = Literal::createEquality(false,x,y,s1); 
  eqAxiom1->setProxyAxiomsDescendant(true);  
  UnitList::push(eqAxiom1, prb.units());

  Clause* eqAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*eqAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*eqAxiom2)[1] = Literal::createEquality(true,x,y,s1); 
  eqAxiom2->setProxyAxiomsDescendant(true);   
  UnitList::push(eqAxiom2, prb.units());

  inf = new Inference(Inference::NOT_PROXY_AXIOM);
  unsigned notProxy = env.signature->getNotProxy();
  constant = TermList(Term::createConstant(notProxy));

  Clause* notAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*notAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true);
  (*notAxiom1)[1] = toEquality(x, true);
  notAxiom1->setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom1, prb.units());

  Clause* notAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*notAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*notAxiom2)[1] = toEquality(x, false);
  notAxiom2->setProxyAxiomsDescendant(true);    
  UnitList::push(notAxiom2, prb.units());  

  inf = new Inference(Inference::PI_PROXY_AXIOM);
  unsigned piProxy = env.signature->getPiSigmaProxy("vPI");
  constant = TermList(Term::create1(piProxy, s1));

  Clause* piAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*piAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true);
  (*piAxiom1)[1] = toEquality(AH::createAppTerm(s1, Term::boolSort(), x, AH::createAppTerm(srtOf(sk1), sk1, x)), false);
  piAxiom1->setProxyAxiomsDescendant(true);    
  UnitList::push(piAxiom1, prb.units());

  Clause* piAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*piAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*piAxiom2)[1] = toEquality(AH::createAppTerm(s1, Term::boolSort(), x, y), true);
  piAxiom2->setProxyAxiomsDescendant(true);      
  UnitList::push(piAxiom2, prb.units());  

  inf = new Inference(Inference::SIGMA_PROXY_AXIOM);
  unsigned sigmaProxy = env.signature->getPiSigmaProxy("vSIGMA");
  constant = TermList(Term::create1(sigmaProxy, s1));

  Clause* sigmaAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*sigmaAxiom1)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), true); 
  (*sigmaAxiom1)[1] = toEquality(AH::createAppTerm(s1, Term::boolSort(), x, y), false);
  sigmaAxiom1->setProxyAxiomsDescendant(true);      
  UnitList::push(sigmaAxiom1, prb.units());

  Clause* sigmaAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*sigmaAxiom2)[0] = toEquality(AH::createAppTerm(srtOf(constant), constant, x), false);
  (*sigmaAxiom2)[1] = toEquality(AH::createAppTerm(s1, Term::boolSort(), x, AH::createAppTerm(srtOf(sk2), sk2, x)), true);
  sigmaAxiom2->setProxyAxiomsDescendant(true);    
  UnitList::push(sigmaAxiom2, prb.units()); 

  inf = new Inference(Inference::IMPLIES_PROXY_AXIOM);
  unsigned impProxy = env.signature->getBinaryProxy("vIMP");
  constant = TermList(Term::createConstant(impProxy));

  Clause* impAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*impAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*impAxiom1)[1] = toEquality(x, true);
  impAxiom1->setProxyAxiomsDescendant(true);    
  UnitList::push(impAxiom1, prb.units());

  Clause* impAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*impAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*impAxiom2)[1] = toEquality(y, false);
  impAxiom2->setProxyAxiomsDescendant(true);      
  UnitList::push(impAxiom2, prb.units());

  Clause* impAxiom3 = new(3) Clause(3, Unit::AXIOM, inf);
  (*impAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);  
  (*impAxiom3)[1] = toEquality(x, false);
  (*impAxiom3)[2] = toEquality(y, true);
  impAxiom3->setProxyAxiomsDescendant(true);
  UnitList::push(impAxiom3, prb.units());

  inf = new Inference(Inference::AND_PROXY_AXIOM);
  unsigned andProxy = env.signature->getBinaryProxy("vAND");
  constant = TermList(Term::createConstant(andProxy));

  Clause* andAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*andAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*andAxiom1)[1] = toEquality(x, true);
  andAxiom1->setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom1, prb.units());

  Clause* andAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*andAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);
  (*andAxiom2)[1] = toEquality(y, true);
  andAxiom2->setProxyAxiomsDescendant(true);
  UnitList::push(andAxiom2, prb.units());

  Clause* andAxiom3 = new(3) Clause(3, Unit::AXIOM, inf);
  (*andAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);  
  (*andAxiom3)[1] = toEquality(x, false);
  (*andAxiom3)[2] = toEquality(y, false);
  andAxiom3->setProxyAxiomsDescendant(true);  
  UnitList::push(andAxiom3, prb.units());

  inf = new Inference(Inference::OR_PROXY_AXIOM);
  unsigned orProxy = env.signature->getBinaryProxy("vOR");
  constant = TermList(Term::createConstant(orProxy));

  Clause* orAxiom1 = new(2) Clause(2, Unit::AXIOM, inf);
  (*orAxiom1)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*orAxiom1)[1] = toEquality(x, false);
  orAxiom1->setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom1, prb.units());

  Clause* orAxiom2 = new(2) Clause(2, Unit::AXIOM, inf);
  (*orAxiom2)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), true);
  (*orAxiom2)[1] = toEquality(y, false);
  orAxiom2->setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom2, prb.units());

  Clause* orAxiom3 = new(3) Clause(3, Unit::AXIOM, inf);
  (*orAxiom3)[0] = toEquality(AH::createAppTerm3(srtOf(constant), constant, x, y), false);  
  (*orAxiom3)[1] = toEquality(x, true);
  (*orAxiom3)[2] = toEquality(y, true);
  orAxiom3->setProxyAxiomsDescendant(true);
  UnitList::push(orAxiom3, prb.units()); 
  
  inf = new Inference(Inference::FOOL_AXIOM);

  Clause* tneqfClause = new(1) Clause(1, Unit::AXIOM, inf);
  (*tneqfClause)[0] =  Literal::createEquality(false, TermList(Term::foolTrue()), 
                                                      TermList(Term::foolFalse()), Term::boolSort());
  UnitList::push(tneqfClause, prb.units()); 

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
 
Literal* LambdaElimination::toEquality(TermList booleanTerm, bool polarity) {
  TermList boolVal = polarity ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
  return Literal::createEquality(true, booleanTerm, boolVal, Term::boolSort());
}
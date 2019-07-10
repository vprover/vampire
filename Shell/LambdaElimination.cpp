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

#include "Shell/Options.hpp"
//#include "Shell/SymbolOccurrenceReplacement.hpp"


#include "LambdaElimination.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

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
      appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, lhs);
      appTerm = createAppTerm(SortHelper::getResultSort(appTerm.term()), appTerm, rhs);
      
      if(!lit->polarity()){
        constant = TermList(Term::createConstant(env.signature->getNotProxy()));
        appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, appTerm);
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

      TermList form = processBeyondLambda(lhs);      
      appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, form);
      form = processBeyondLambda(rhs);
      appTerm = createAppTerm(SortHelper::getResultSort(appTerm.term()), appTerm, form);
      return appTerm;
    }
    case AND:
    case OR:{
      FormulaList::Iterator argsIt(formula->args());
      
      vstring name = (conn == AND ? "vAND" : "vIFF");
      constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));
      
      TermList form;

      unsigned count = 1;
      while(argsIt.hasNext()){
        Formula* arg = argsIt.next();
        form = processBeyondLambda(arg);
        if(count == 1){
          appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, form);
        }else if(count == 2){
          appTerm = createAppTerm(SortHelper::getResultSort(appTerm.term()), appTerm, form);
        }else{
          appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, appTerm);
          appTerm = createAppTerm(SortHelper::getResultSort(appTerm.term()), appTerm, form);
        }
        count++;
      }
      return appTerm;                           
    }
    case NOT: {
      constant = TermList(Term::createConstant(env.signature->getNotProxy()));
      TermList form = processBeyondLambda(formula->uarg());
      appTerm = createAppTerm(SortHelper::getResultSort(constant.term()), constant, form);
      return appTerm;                                                    
    }
    case FORALL:
    case EXISTS: {
      Formula::VarList* vars = formula->vars();
      Formula::VarList::Iterator vit(vars);
      SList* sort = SList::empty();
      VList* var = VList::empty();

      TermList form = processBeyondLambda(formula->qarg());
      vstring name = conn === FORALL ? "vPI" : "vSIGMA";
      unsigned proxy = getPiSigmaProxy(name);

      TermList s;
      while(vit.hasNext()){
        int v = vit.next();
        ALWAYS(SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        var->setHead(v);
        sort->setHead(s);
        form = elimLambda(Term::createLambda(form, var, sort, Term::boolSort())); 
        constant = Term::create1(proxy, s);
        form = createAppTerm(SortHelper::getResultSort(constant.term()), constant, form);
      }
      return form;
    }
    case BOOL_TERM
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
    return createAppTerm(s1, s2, arg1, arg2);
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

TermList LambdaElimination::createAppTerm(TermList sort, TermList arg1, TermList arg2)
{
  CALL("LambdaElimination::createAppTerm/2");

  ASS(sort.isTerm() && sort.term()->arity() == 2);
  ASS(env.signature->getFunction(sort.term()->functor()->arrow()));
  TermList s1 = *(sort.term()->nthArgument(0));
  TermList s2 = *(sort.term()->nthArgument(1));
  return createAppTerm(s1, s2, arg1, arg2);
}

TermList LambdaElimination::createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2)
{
  CALL("LambdaElimination::createAppTerm/1");
 
  static TermStack args;
  args.reset();
  args.push(s1);
  args.push(s2);
  args.push(arg1);
  args.push(arg2);
  unsigned app = env.signature->getApp();
  return TermList(Term::create(app, 4, args.begin()));
}
  
TermList LambdaElimination::elimLambda(Term* lambdaTerm)
{
    CALL("LambdaElimination::elimLambda");
    
    Stack<int> vars;
    Stack<TermList> sorts;
    Stack<TermList> toBeProcessed;
  
    ASS(lambdaTerm->isSpecial());
    Term::SpecialTermData* sd = lambdaTerm->getSpecialData();
    ASS_EQ(sd->getType(), Term::SF_LAMBDA);
    
    TermList lambdaExp;
    SList* sorts = sd->getVarSorts();
    IntList* vars = sd->getLambdaVars();
    
    IntList::Iterator vlit(vars);
    Term::SortList::Iterator slit(sorts);
    

    while(vlit.hasNext()){
      _vars.push(vlit.next());
      _sorts.push(slit.next());
    }

    lambdaExp = sd->getLambdaExp();
    toBeProcessed.push(lambdaExp);
  
    process(vars, sorts, toBeProcessed);    
  
    return _processed.pop();
    
}


void LambdaElimination::process(Stack<int> vars, TermStack& sorts, TermStack &toBeProcessed){
   
  CALL("LambdaElimination::process");   
    
  int lambdaVar;
  TermList lambdaVarSort;
  Stack<unsigned> argNums;
   
  while(!vars.isEmpty()){
    lambdaVar = _vars.pop();
    lambdaVarSort = _sorts.pop();
    
    while (!toBeProcessed.isEmpty()){  
   
      _processing = toBeProcessed.pop(); 
       
      if (_processing.isTerm()){ 
        
        Term* lExpTerm = _processing.term();
        IntList* freeVars = lExpTerm->freeVariables();
        
        if(IntList::member(lambdaVar, freeVars)){
          if(lExpTerm->isSpecial()){ 
            switch(lExpTerm->functor()){
              case Term::SF_FORMULA: {
                toBeProcessed.push(processBeyondLambda(lExpTerm));
                break;
              }
              case Term::SF_LAMBDA: {
                toBeProcessed.push(elimLambda(lExpTerm));
                break;
              }
              default:
                ASSERTION_VIOLATION;
                //Not deailing with ITEs, Lets and Tuples at the moment.
            }                    
          }
          else //not special. Of the sort app(X,Y).
          {
            TermList arg1 = *lExpTerm->nthArgument(2);
            TermList arg2 = *lExpTerm->nthArgument(3);
            unsigned sort = env.sorts->addFunctionSort(lambdaVarSort, SortHelper::getResultSort(lExpTerm)); 
            dealWithApp(arg1, arg2, sort, lambdaVar, toBeProcessed, argNums);                
          }
        }
        else //In the case \x.exp where x is not free in exp.
        {
          unsigned kSort = env.sorts->addFunctionSort(lambdaVarSort, sortOf(_processing));
          addToProcessed(addKComb(kSort, processBeyondLambda(_processing.term())), argNums);                  
        }
      }else{//lambda expression is a variable. If it is the lambda var, then this will be translated to I
       bool added;       
       if(_processing.var() == (unsigned)lambdaVar){ //an expression of the form \x.x
          unsigned iSort = env.sorts->addFunctionSort(lambdaVarSort, lambdaVarSort);
          TermList ts = addHolConstant("iCOMB", iSort, added, Signature::Symbol::I_COMB);
          if(added && env.options->combinatorElimination() > Options::CombElimination::INFERENCE_RULES){
            addCombinatorAxiom(ts, iSort, lambdaVarSort, Signature::Symbol::I_COMB);
          }
          addToProcessed(ts, argNums);
        }else{ //an expression of the form \x.y 
          unsigned termSort = sortOf(_processing);
          unsigned kSort = env.sorts->addFunctionSort(lambdaVarSort, termSort);
          addToProcessed(addKComb(kSort, _processing), argNums);
        }       
       //freeVars = List<unsigned>(sd->getLambdaExp().var());
      }
    }//of while
   
    if(!_vars.isEmpty()){
      _toBeProcessed.push(_processed.pop());     
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
        Signature::Symbol::HOLConstant comb = _combinators.pop();

        TermList arg1 = _processed.pop();   
        TermList arg2 = _processed.pop();
    
        unsigned combSort = _combSorts.pop();   
        if(comb == Signature::Symbol::B_COMB){
          _processed.push(addComb(combSort,arg2, arg1,comb));
        }else{
          _processed.push(addComb(combSort,arg1, arg2,comb));
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


void LambdaElimination::dealWithApp(TermList lhs, TermList rhs, unsigned sort, int lambdaVar, TermStack &toBeProcessed, Stack<unsigned> &argNums)
{
    CALL("LambdaElimination::dealWithApp");
  
    IntList* lhsFVs = lhs.freeVariables();
    IntList* rhsFVs = rhs.freeVariables();

    if(rhs.isVar() && (rhs.var() == (unsigned)lambdaVar) && !IntList::member(lambdaVar, lhsFVs)){
      //This is the case [\x. exp @ x] wehere x is not free in exp.
      lhs.isTerm() ? addToProcessed(processBeyondLambda(lhs.term()), _argNums) : addToProcessed(lhs, _argNums);
      return;
    }

    if ((IntList::member(lambdaVar, lhsFVs)) && (IntList::member(lambdaVar, rhsFVs))){
      _combinators.push(Signature::Symbol::S_COMB);
      argNums.push(0);
      toBeProcessed.push(lhs);
      toBeProcessed.push(rhs); 
    }else if(IntList::member(lambdaVar, lhsFVs)){
      _combinators.push(Signature::Symbol::C_COMB);
      argNums.push(0);
      toBeProcessed.push(lhs);
      rhs.isTerm() ? addToProcessed(processBeyondLambda(rhs.term()), _argNums) : addToProcessed(rhs, _argNums);  
    }else if(IntList::member(lambdaVar, rhsFVs)){
      _combinators.push(Signature::Symbol::B_COMB);            
      argNums.push(0);
      toBeProcessed.push(rhs);
      lhs.isTerm() ? addToProcessed(processBeyondLambda(lhs.term()), _argNums) : addToProcessed(lhs, _argNums);   
    }     
    _combSorts.push(sort);
}

TermList LambdaElimination::addKComb(unsigned appliedToArg, TermList arg)
{
    CALL("LambdaElimination::addKComb");
    
    TermList ts;
    unsigned argSort = sortOf(arg);
    unsigned appliedToZeroArgs = env.sorts->addFunctionSort(argSort, appliedToArg);
                
    bool added;
    ts = addHolConstant("kCOMB",appliedToZeroArgs, added, Signature::Symbol::K_COMB);
    if(added && env.options->combinatorElimination() > Options::CombElimination::INFERENCE_RULES){
       addCombinatorAxiom(ts, appliedToZeroArgs, argSort, Signature::Symbol::K_COMB, HSH::domain(appliedToArg));
    }   
    TermList applied;
    unsigned app = introduceAppSymbol( appliedToZeroArgs, argSort, appliedToArg);
    buildFuncApp(app, ts, arg, applied);
                
    return applied;
}   
    
TermList LambdaElimination::addComb(unsigned appliedToArgs, TermList arg1, TermList arg2, Signature::Symbol::HOLConstant comb)
{
    CALL("LambdaElimination::addComb");
    
    TermList ts;
    unsigned arg1sort = sortOf(arg1);
    unsigned arg2sort = sortOf(arg2);
    unsigned arg3sort = HSH::domain(appliedToArgs);
    unsigned appliedToOneArg = env.sorts->addFunctionSort(arg2sort, appliedToArgs);
    unsigned appliedToZeroArgs = env.sorts->addFunctionSort(arg1sort, appliedToOneArg);
    
    bool added;
    switch(comb){
       case Signature::Symbol::S_COMB:  
          ts = addHolConstant("sCOMB",appliedToZeroArgs, added, comb);
          break;
       case Signature::Symbol::C_COMB:
          ts = addHolConstant("cCOMB",appliedToZeroArgs, added, comb);
          break;
       case Signature::Symbol::B_COMB:
          ts = addHolConstant("bCOMB",appliedToZeroArgs, added, comb);
          break;
       default:
          ASSERTION_VIOLATION;
    }
    if(added && env.options->combinatorElimination() > Options::CombElimination::INFERENCE_RULES){
        addCombinatorAxiom(ts, appliedToZeroArgs, arg1sort, comb, arg2sort, arg3sort);
    }
    
    TermList app1, app2;
    unsigned app = introduceAppSymbol( appliedToZeroArgs, arg1sort, appliedToOneArg);
    buildFuncApp(app, ts, arg1, app1);
    app = introduceAppSymbol( appliedToOneArg, arg2sort, appliedToArgs);
    buildFuncApp(app, app1, arg2, app2);                
    return app2;
    
}

TermList LambdaElimination::addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant cnst){

    CALL("LambdaElimination::addHolConstant");

    unsigned fun = env.signature->addFunction(name + "_" +  Lib::Int::toString(sort),0,added);
    if(added){//first time constant added. Set type
      Signature::Symbol* symbol = env.signature->getFunction(fun);  
      symbol->setType(OperatorType::getConstantsType(sort));
      symbol->setHOLConstant(cnst);   
    }
    Term* t = Term::createConstant(fun);
    TermList ts(t);
    return ts;
}

unsigned LambdaElimination::sortOf(TermList t)
{
  CALL("LambdaElimination::sortOf");
  
  return SortHelper::getResultSort(t, _varSorts);
  
} 
  
unsigned LambdaElimination::introduceAppSymbol(unsigned sort1, unsigned sort2, unsigned resultSort) {
    
  CALL("LambdaElimination::introduceAppSymbol");

  ASS(env.sorts->getFuncSort(sort1)->getDomainSort() == sort2);
  ASS(env.sorts->getFuncSort(sort1)->getRangeSort() == resultSort);
 
  Stack<unsigned> sorts;
  sorts.push(sort1); sorts.push(sort2);
  
  OperatorType* type = OperatorType::getFunctionType(2, sorts.begin(), resultSort);
  unsigned symbol;
  bool added;
  
  vstring srt1 = Lib::Int::toString(sort1);
  vstring srt2 = Lib::Int::toString(sort2);
  symbol = env.signature->addFunction("vAPP_" + srt1 + "_" + srt2, 2, added);
  
  if(added){
   if(env.sorts->isStructuredSort(resultSort)){
     //if a -> b and a are occupied in Henkin universe then so must b be.
     env.sorts->getFuncSort(resultSort)->instantiable();
   }
   env.signature->getFunction(symbol)->setType(type);
   env.signature->getFunction(symbol)->markHOLAPP();
   /*if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Lambda or application elimination introduced ";
    env.out() << "function symbol " << env.signature->functionName(symbol) << endl;
    //env.out() << " of the sort " << type->toString() << endl; This produces really long and horrible output.
    env.endOutput();
   }*/
  }

  return symbol;
}

void LambdaElimination::buildFuncApp(unsigned symbol, TermList arg1, TermList arg2,
                                         TermList& functionApplication) {
  CALL("LambdaElimination::buildFuncApp");

  ASS_EQ(env.signature->functionArity(symbol), 2);
  
  functionApplication = TermList(Term::create2(symbol, arg1, arg2));
}

 void LambdaElimination::addCombinatorAxiom(TermList combinator, unsigned combinatorSort, unsigned argSort,
                                            Signature::Symbol::HOLConstant comb, int arg1Sort, int arg2Sort)
 {
     CALL("LambdaElimination::addCombinatorAxiom"); 
   
     Formula* combAxiom;
       
     TermList functionApplied;
     TermList var1 = TermList(0, false);
     
     List<int>* varList = new List<int>(var1.var());
     List<unsigned>* sortList = new List<unsigned>(argSort);
     
     unsigned appFun = introduceAppSymbol( combinatorSort, argSort, HSH::range(combinatorSort));
     buildFuncApp(appFun, combinator, var1, functionApplied);
   
     switch(comb){
        case Signature::Symbol::I_COMB: {    
            combAxiom = createEquality(functionApplied, var1, argSort);
            combAxiom = new QuantifiedFormula(FORALL, varList, sortList, combAxiom);
            break;
        }
        case Signature::Symbol::K_COMB: {
            TermList functionApplied2;
            TermList var2 = TermList(1, false); 
            
            appFun = introduceAppSymbol( HSH::range(combinatorSort), arg1Sort, HSH::range(HSH::range(combinatorSort)));
            buildFuncApp(appFun, functionApplied, var2, functionApplied2);
            
            varList = varList->addLast(varList, var2.var());
            sortList = sortList->addLast(sortList, arg1Sort);
                    
            combAxiom = createEquality(functionApplied2, var1, argSort);
            combAxiom = new QuantifiedFormula(FORALL, varList, sortList, combAxiom); 
            break; 
        }
        case Signature::Symbol::B_COMB:
        case Signature::Symbol::C_COMB:
        case Signature::Symbol::S_COMB: {

            TermList functionApplied2;
            TermList var2 = TermList(1, false); 
            
            appFun = introduceAppSymbol( HSH::range(combinatorSort), arg1Sort, HSH::range(HSH::range(combinatorSort)));
            buildFuncApp(appFun, functionApplied, var2, functionApplied2);
            
            varList = varList->addLast(varList, var2.var());
            sortList = sortList->addLast(sortList, arg1Sort);
            
            TermList functionApplied3;
            TermList var3 = TermList(2, false);
            
            appFun = introduceAppSymbol( HSH::range(HSH::range(combinatorSort)), arg2Sort, HSH::range(HSH::range(HSH::range(combinatorSort))));
            buildFuncApp(appFun, functionApplied2, var3, functionApplied3);
        
            varList = varList->addLast(varList, var3.var());
            sortList = sortList->addLast(sortList, arg2Sort);
            
            TermList functionApplied4, functionApplied5, functionApplied6;
            
            if(comb == Signature::Symbol::S_COMB){ 
                appFun = introduceAppSymbol( argSort, arg2Sort, HSH::range(argSort));
                buildFuncApp(appFun, var1, var3, functionApplied4);
       
                appFun = introduceAppSymbol( arg1Sort, arg2Sort, HSH::range(arg1Sort));
                buildFuncApp(appFun, var2, var3, functionApplied5);
   
                appFun = introduceAppSymbol( HSH::range(argSort), HSH::range(arg1Sort), HSH::range(HSH::range(argSort)));
                buildFuncApp(appFun, functionApplied4, functionApplied5, functionApplied6);       
            }
            
            if(comb == Signature::Symbol::B_COMB){
                appFun = introduceAppSymbol( arg1Sort, arg2Sort, HSH::range(arg1Sort));
                buildFuncApp(appFun, var2, var3, functionApplied5);
             
                appFun = introduceAppSymbol( argSort, HSH::range(arg1Sort), HSH::range(argSort));
                buildFuncApp(appFun, var1, functionApplied5, functionApplied6);     
            }
            
            if(comb == Signature::Symbol::C_COMB){
                appFun = introduceAppSymbol( argSort, arg2Sort, HSH::range(argSort));
                buildFuncApp(appFun, var1, var3, functionApplied5);
                
                appFun = introduceAppSymbol( HSH::range(argSort), arg1Sort, HSH::range(HSH::range(argSort)));
                buildFuncApp(appFun, functionApplied5, var2, functionApplied6); 
            }

            combAxiom = createEquality(functionApplied3, functionApplied6, sortOf(functionApplied3));
            combAxiom = new QuantifiedFormula(FORALL, varList,sortList, combAxiom); 
            break;
        }
        default:
          ASSERTION_VIOLATION;
          break;
        
     }
     
     Inference* lambdaInference;
     
     switch(comb){
         case Signature::Symbol::I_COMB:
            lambdaInference = new Inference(Inference::LAMBDA_ELIMINATION_I_COMB);
            break;
         case Signature::Symbol::K_COMB:
            lambdaInference = new Inference(Inference::LAMBDA_ELIMINATION_K_COMB);
            break;
         case Signature::Symbol::B_COMB:
            lambdaInference = new Inference(Inference::LAMBDA_ELIMINATION_B_COMB);
            break;
         case Signature::Symbol::C_COMB:
            lambdaInference = new Inference(Inference::LAMBDA_ELIMINATION_C_COMB);
            break;
         case Signature::Symbol::S_COMB:
            lambdaInference = new Inference(Inference::LAMBDA_ELIMINATION_S_COMB);
            break;
         default:
           ASSERTION_VIOLATION;
     }
     
     
     addAxiom(new FormulaUnit(combAxiom, lambdaInference, Unit::AXIOM));
     
 }

 FormulaUnit* LambdaElimination::addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned argSort)
 {
    CALL("LambdaElimination::addQuantifierAxiom");   
     
    Formula* qAxiom;
    TermList functionApplied;
    TermList functionApplied2;
    Formula::VarList* vars = Formula::VarList::empty();
    Formula::SortList* sorts = Formula::SortList::empty();
  
    TermList var1 = TermList(0, false);
    List<int>* varList = new List<int>(var1.var());
    List<unsigned>* sortList = new List<unsigned>(argSort);
    
    unsigned appFun = introduceAppSymbol(constSort, argSort, Sorts::SRT_BOOL);
    buildFuncApp(appFun, constant, var1, functionApplied);

    TermList var;
    unsigned varNum = 1;
    unsigned currSort;
    functionApplied2 = var1;
    
    do{   
      currSort = HSH::domain(argSort);
      sorts = sorts->addLast(sorts, currSort);

      var = TermList(varNum, false);
      vars = vars->addLast(vars, var.var());
      varNum += 1;

      unsigned appFun = introduceAppSymbol(argSort, currSort, HSH::range(argSort));
      buildFuncApp(appFun, functionApplied2, var, functionApplied2);
      argSort = HSH::range(argSort);
    }while(!(argSort == Sorts::SRT_BOOL));

    qAxiom = toEquality(functionApplied);
    qAxiom = new BinaryFormula(IFF, qAxiom, new QuantifiedFormula(conn, vars, sorts, toEquality(functionApplied2)));
    qAxiom = new QuantifiedFormula(FORALL, varList, sortList, qAxiom); 
    
  
    Inference* qInference;
    qInference = new Inference(Inference::LAMBDA_ELIMINATION_QUANTIFIER);
    
    return new FormulaUnit(qAxiom, qInference, Unit::AXIOM);     
 }
 
 FormulaUnit* LambdaElimination::addNotConnAxiom(TermList constant, unsigned notsort)
 {
    CALL("LambdaElimination::addNotConnAxiom"); 
     
    Formula* notAxiom;
    
    TermList functionApplied;   
    
    TermList var1 = TermList(0, false);
    List<int>* varList = new List<int>(var1.var());
    List<unsigned>* sortList = new List<unsigned>(Sorts::SRT_BOOL);
     
    unsigned appFun = introduceAppSymbol(notsort, Sorts::SRT_BOOL, Sorts::SRT_BOOL);
    buildFuncApp(appFun, constant, var1, functionApplied);
     
    Formula* negatedVar = new NegatedFormula(toEquality(var1));
    notAxiom = toEquality(functionApplied);
    notAxiom = new BinaryFormula(IFF, notAxiom, negatedVar);
    notAxiom = new QuantifiedFormula(FORALL, varList,sortList, notAxiom); 
    
    Inference* notInference;
    notInference = new Inference(Inference::LAMBDA_ELIMINATION_NOT);
    
    return new FormulaUnit(notAxiom, notInference, Unit::AXIOM);  
 }
 
 FormulaUnit* LambdaElimination::addEqualityAxiom(TermList equals, unsigned argsSort, unsigned equalsSort)
 {
    CALL("LambdaElimination::addEqualityAxiom"); 
    
    Formula* equalityAxiom;
    Formula* equalityBetweenVars;
    
    TermList functionApplied;
    
    TermList var1 = TermList(0, false);
    TermList var2 = TermList(1, false);
     
    List<int>* varList = new List<int>(var1.var());
    List<unsigned>* sortList = new List<unsigned>(argsSort);
    varList = varList->addLast(varList, var2.var());
    sortList = sortList->addLast(sortList, argsSort);
    
    unsigned appFun = introduceAppSymbol( equalsSort, argsSort, HSH::range(equalsSort));
    buildFuncApp(appFun, equals, var1, functionApplied);
    
    appFun = introduceAppSymbol( HSH::range(equalsSort), argsSort, HSH::range(HSH::range(equalsSort)));
    buildFuncApp(appFun, functionApplied, var2, functionApplied);
    
    equalityBetweenVars = createEquality(var1, var2, argsSort);
    
    equalityAxiom = toEquality(functionApplied);
    equalityAxiom = new BinaryFormula(IFF, equalityAxiom, equalityBetweenVars);
    equalityAxiom = new QuantifiedFormula(FORALL, varList,sortList, equalityAxiom); 
    
    Inference* eqInference;
    eqInference = new Inference(Inference::LAMBDA_ELIMINATION_EQUALITY);
    
    return new FormulaUnit(equalityAxiom, eqInference, Unit::AXIOM);  
 }
 
 FormulaUnit* LambdaElimination::addBinaryConnAxiom(TermList constant, unsigned connSort, Connective conn, unsigned appedOnce)
 {
    CALL("LambdaElimination::addBinaryConnAxiom"); 
    
    Formula* binaryConnAxiom;
    Formula* varFormula;
    
    TermList functionApplied;
    
    TermList var1 = TermList(0, false);
    TermList var2 = TermList(1, false);
     
    List<int>* varList = new List<int>(var1.var());
    List<unsigned>* sortList = new List<unsigned>(Sorts::SRT_BOOL);
    varList = varList->addLast(varList, var2.var());
    sortList = sortList->addLast(sortList, Sorts::SRT_BOOL);
    
    unsigned appFun = introduceAppSymbol( connSort, Sorts::SRT_BOOL, appedOnce);
    buildFuncApp(appFun, constant, var1, functionApplied);

    appFun = introduceAppSymbol(appedOnce, Sorts::SRT_BOOL, HSH::range(appedOnce));
    buildFuncApp(appFun, functionApplied, var2, functionApplied);

    if(conn == AND || conn == OR){
      FormulaList* args = new FormulaList(toEquality(var1));
      args = FormulaList::cons(toEquality(var2), args);
      varFormula = new JunctionFormula(conn, args);
    }else{
      varFormula = new BinaryFormula(conn, toEquality(var1), toEquality(var2));
    }
    
    binaryConnAxiom = toEquality(functionApplied);
    binaryConnAxiom = new BinaryFormula(IFF, binaryConnAxiom, varFormula);
    binaryConnAxiom = new QuantifiedFormula(FORALL, varList, sortList, binaryConnAxiom); 
    
    Inference* binConInf;
    binConInf = new Inference(Inference::LAMBDA_ELIMINATION_BIN_CON);
    
    return new FormulaUnit(binaryConnAxiom, binConInf, Unit::AXIOM); 
 }
 
 Formula* LambdaElimination::createEquality(TermList t1, TermList t2, unsigned sort) {
   Literal* equality = Literal::createEquality(true, t1, t2, sort);
   return new AtomicFormula(equality);
     
 }
 
Formula* LambdaElimination::toEquality(TermList booleanTerm) {
  TermList truth(Term::foolTrue());
  Literal* equality = Literal::createEquality(true, booleanTerm, truth, Sorts::SRT_BOOL);
  return new AtomicFormula(equality);
}
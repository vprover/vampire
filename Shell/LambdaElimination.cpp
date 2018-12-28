/**
 * @file LambdaElimination.cpp
 * Takes a single lambda term and eliminates the lambda(s)
 * from the term by applying the well known combinator rewrite rules.
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

void LambdaElimination::addFunctionExtensionalityAxioms(UnitList*& units){
  CALL("LambdaElimination::addFunctionExtensionalityAxioms");

  Stack<unsigned> sorts = env.sorts->getInstantiableFunctionSorts();
  while(!sorts.isEmpty()){
    unsigned functionSort = sorts.pop();
    unsigned firstArgSort = HSH::domain(functionSort);
     
    Formula* extAxiom;
    
    TermList functionApplied;
    TermList functionApplied2;    
    
    TermList var1 = TermList(0, false);
    TermList var2 = TermList(1, false);
    List<int>* varList = new List<int>(var1.var());
    List<unsigned>* sortList = new List<unsigned>(functionSort);
    varList = varList->addLast(varList, var2.var());
    sortList = sortList->addLast(sortList, functionSort);
     
    TermList var3 = TermList(2, false); 
    List<int>* varList2 = new List<int>(var3.var());
    List<unsigned>* sortList2 = new List<unsigned>(firstArgSort);

    
    unsigned appFun = introduceAppSymbol(functionSort, firstArgSort, HSH::range(functionSort));
    buildFuncApp(appFun, var1, var3, functionApplied);
    buildFuncApp(appFun, var2, var3, functionApplied2); 
    
    Formula* equalityForm = createEquality(functionApplied, functionApplied2, HSH::range(functionSort));
    equalityForm = new QuantifiedFormula(FORALL, varList2,sortList2, equalityForm); 
    Formula* equalityForm2 = createEquality(var1, var2, functionSort);

    extAxiom = new BinaryFormula(IMP, equalityForm, equalityForm2);
    extAxiom = new QuantifiedFormula(FORALL, varList,sortList, extAxiom); 

    Inference* notInference;
    notInference = new Inference(Inference::FUNC_EXT_AXIOM);
    
    addAxiom(new FormulaUnit(extAxiom, notInference, Unit::AXIOM), true);  
  }
  addAxiomsToUnits(units);
  return;  
}

void LambdaElimination::addBooleanExtensionalityAxiom(UnitList*& units){
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
  
}


void LambdaElimination::addCombinatorsHeuristically(UnitList*& units){
  CALL("LambdaElimination::addCombinatorsHeuristically"); 

  _combinatorsAdded = 0;
  if(env.options->addCombinators() == Options::AddCombinators::FUNCTION_OF_PROBLEM_SIZE){
    _maxCombinatorsToBeAdded = UnitList::length(units) * MULT_FACTOR;
  } else {
    _maxCombinatorsToBeAdded = env.options->numOfCombinatorsToAdd();
  }
  if(!_maxCombinatorsToBeAdded){ return; }
  
  //first add identity combinators for relevant sorts
  Stack<unsigned> sorts = env.sorts->getUsedAndInstantiableSorts();
  while(!sorts.isEmpty()){
    bool added;
    unsigned sort = sorts.pop();
    unsigned iSort = env.sorts->addFunctionSort(sort, sort);
    if(!eligible(iSort)){ continue; }
    env.sorts->getFuncSort(iSort)->makeInstantiable();
    TermList ts = addHolConstant("iCOMB", iSort, added, Signature::Symbol::I_COMB);
    if(added){
      _combinatorsAdded++;
      addCombinatorAxiom(ts, iSort, sort, Signature::Symbol::I_COMB);
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] Heuristically added combinator: " << ts.toString() + " of sort " + env.sorts->sortName(iSort) << endl;
        env.endOutput();
      }
      if(_combinatorsAdded == _maxCombinatorsToBeAdded){
        addAxiomsToUnits(units);
        return;
      }
    }  
  }
  
  //add K combinators for relevant sorts
  sorts = env.sorts->getUsedAndInstantiableSorts();
  while(!sorts.isEmpty()){
    bool added;
    unsigned sort = sorts.pop();
    Stack<unsigned> secondSorts = env.sorts->getUsedAndInstantiableSorts();
    while(!secondSorts.isEmpty()){
      unsigned secondSort = secondSorts.pop();
      unsigned kSort = env.sorts->addFunctionSort(secondSort, sort);
      kSort = env.sorts->addFunctionSort(sort, kSort);
      //env.sorts->getFuncSort(kSort)->makeInstantiable();
      if(!eligible(kSort)){ continue; }
      TermList ts = addHolConstant("kCOMB", kSort, added, Signature::Symbol::K_COMB);
      if(added){
        _combinatorsAdded++;
        addCombinatorAxiom(ts, kSort, sort, Signature::Symbol::K_COMB, secondSort);
        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] Heuristically added combinator: " << ts.toString() + " of sort " + env.sorts->sortName(kSort) << endl;
          env.endOutput();
        }
        if(_combinatorsAdded == _maxCombinatorsToBeAdded){
          addAxiomsToUnits(units);
          return;
        }
      }  
    }
  }
  
  Deque<unsigned> sortQ;
  
  //now add other combinators as relevant
  Stack<unsigned> instSorts = env.sorts->getInstantiableFunctionSorts();
  while(!instSorts.isEmpty()){
    unsigned sort = instSorts.pop();
    if(tryAddCombinatorFromSort(sort, sortQ)){;
      if(_combinatorsAdded == _maxCombinatorsToBeAdded){ 
        sortQ.reset();
        addAxiomsToUnits(units); 
        return;
      }    
    }
  }

  //Iterate the process of combinator addition (ONLY for S, B and C combinators!)
  while(!sortQ.isEmpty()){
    unsigned sort = sortQ.pop_front();
    if(tryAddCombinatorFromSort(sort, sortQ)){
      if(_combinatorsAdded == _maxCombinatorsToBeAdded){ 
        sortQ.reset();
        addAxiomsToUnits(units); 
        return;
      }
    }
  }
  
  addAxiomsToUnits(units);
  
}

bool LambdaElimination::tryAddCombinatorFromSort(unsigned sort, Deque<unsigned>& sortQ){
  CALL("LambdaElimination::tryAddCombinatorFromSort");
  
  unsigned origCombNumb = _combinatorsAdded;
  unsigned arg1sort = 0;
  unsigned arg2sort = 0;
  unsigned arg3sort = 0;
  
  arg1sort = HSH::domain(sort);
  arg2sort = HSH::range(sort);
  
  TermList ts; 
  unsigned combinatorSort;
  SortStack combinatorSorts;
  Signature::Symbol::HOLConstant comb;
  
  if(isBCompatible(sort, arg1sort, arg2sort, combinatorSorts)){
    ASS(!combinatorSorts.isEmpty());
    while(!combinatorSorts.isEmpty()){
      combinatorSort = combinatorSorts.pop();
      bool added = false;
      comb = Signature::Symbol::B_COMB;
      ts = addHolConstant("bCOMB",combinatorSort, added, comb);
      if(added){
        _combinatorsAdded++;
        env.sorts->getFuncSort(combinatorSort)->instantiable();
        sortQ.push_back(combinatorSort);
        unsigned s1 = HSH::domain(combinatorSort);
        unsigned s2 = HSH::domain(HSH::range(combinatorSort));
        unsigned s3 = HSH::domain(HSH::range(HSH::range(combinatorSort)));      
        addCombinatorAxiom(ts, combinatorSort, s1, comb, s2, s3);
        
        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] Heuristically added combinator: " << ts.toString() + " of sort " + env.sorts->sortName(combinatorSort) << endl;
          env.endOutput();
        }
        if(_combinatorsAdded == _maxCombinatorsToBeAdded){ return true; }
      }
    }
  }
  
  if(env.sorts->isStructuredSort(arg2sort)){   
    arg3sort = HSH::range(arg2sort); //order of statements crucial here
    arg2sort = HSH::domain(arg2sort);  
  } else {
    return origCombNumb != _combinatorsAdded;
  }
  
  if(isSCompatible(sort, arg1sort, arg2sort, arg3sort, combinatorSort)){
    bool added = false;
    comb = Signature::Symbol::S_COMB;
    ts = addHolConstant("sCOMB",combinatorSort, added, comb);
    if(added){
      _combinatorsAdded++;
      env.sorts->getFuncSort(combinatorSort)->instantiable();
      sortQ.push_back(combinatorSort);
      unsigned s1 = HSH::domain(combinatorSort);
      unsigned s2 = HSH::domain(HSH::range(combinatorSort));
      unsigned s3 = HSH::domain(HSH::range(HSH::range(combinatorSort)));
      addCombinatorAxiom(ts, combinatorSort, s1, comb, s2, s3);

      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] Heuristically added combinator: " << ts.toString() + " of sort " + env.sorts->sortName(combinatorSort) << endl;
        env.endOutput();
      }
      if(_combinatorsAdded == _maxCombinatorsToBeAdded){ return true; }
    }
  }

  if(isCCompatible(sort, arg1sort, arg2sort, arg3sort, combinatorSort)){    
    bool added = false;
    comb = Signature::Symbol::C_COMB;
    ts = addHolConstant("cCOMB",combinatorSort, added, comb);
    if(added){
      _combinatorsAdded++;
      env.sorts->getFuncSort(combinatorSort)->instantiable();
      sortQ.push_back(combinatorSort);
      unsigned s1 = HSH::domain(combinatorSort);
      unsigned s2 = HSH::domain(HSH::range(combinatorSort));
      unsigned s3 = HSH::domain(HSH::range(HSH::range(combinatorSort)));   
      
      addCombinatorAxiom(ts, combinatorSort, s1, comb, s2, s3);

      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] Heuristically added combinator: " << ts.toString() + " of sort " + env.sorts->sortName(combinatorSort) << endl;
        env.endOutput();
      }
      if(_combinatorsAdded == _maxCombinatorsToBeAdded){ return true; }
    }
  }   
  
  return origCombNumb != _combinatorsAdded;
}

bool LambdaElimination::isSCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, unsigned sort3, unsigned &combSort)
{
  CALL("LambdaElimination::isSCompatible");
  
  if(env.sorts->isStructuredSort(sort1)){
    if(!env.sorts->getFuncSort(sort1)->instantiable()){
      return false;
    }
  }
  
  //Check this
  vstring sname = "(" + env.sorts->sortName(sort1) + " > " + env.sorts->sortName(sort2) + ")";
  unsigned ysort;
  
  if(env.sorts->findSort(sname, ysort)){
    if(!env.sorts->getFuncSort(ysort)->instantiable()){
      return false;
    }
    combSort = env.sorts->addFunctionSort(sort1, sort3);
    combSort = env.sorts->addFunctionSort(ysort, combSort);    
    combSort = env.sorts->addFunctionSort(combinedSort, combSort); 
    return eligible(combSort);
  }
  
  return false;
}

bool LambdaElimination::isBCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, SortStack &combSorts)
{
  CALL("LambdaElimination::isBCompatible");

  vstring searchSort = env.sorts->sortName(sort1);
  SortStack ysorts = env.sorts->getSortsWithReturnSort(searchSort);
  
  while(!ysorts.isEmpty()){ 
    unsigned combSort;
    unsigned ysort = ysorts.pop();
    unsigned zsort = HSH::domain(ysort);
    if(env.sorts->isStructuredSort(zsort)){
      if(!env.sorts->getFuncSort(zsort)->instantiable()){
        continue;
      }
    }
    combSort = env.sorts->addFunctionSort(zsort, sort2);
    combSort = env.sorts->addFunctionSort(ysort, combSort);
    combSort = env.sorts->addFunctionSort(combinedSort, combSort);
    
    if(!eligible(combSort)){ continue;}
    
    combSorts.push(combSort);
  }
  return combSorts.isEmpty() ?  false : true;
  
}

bool LambdaElimination::isCCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, unsigned sort3, unsigned &combSort)
{
  CALL("LambdaElimination::isCCompatible"); 

  if(sort1 != sort2){
    return false;
  }
  if(env.sorts->isStructuredSort(sort1)){
    if(!env.sorts->getFuncSort(sort1)->instantiable()){
      return false;
    }
  }
  
  combSort = env.sorts->addFunctionSort(sort1, sort3);
  combSort = env.sorts->addFunctionSort(sort2, combSort);
  combSort = env.sorts->addFunctionSort(combinedSort, combSort);
  
  return eligible(combSort);
  
}

bool LambdaElimination::eligible(unsigned sort){
  CALL("LambdaElimination::nonEligible");
  
  if(env.options->combinatorAdditionBy() == Options::CombinatorAdditionBy::RANK){
    if(env.sorts->getFuncSort(sort)->order() > MAX_ORDER){
      return false;
    }
  }

  if(env.options->combinatorAdditionBy() == Options::CombinatorAdditionBy::NUM_OF_BASIC_SORTS){
    if(countBasicSorts(env.sorts->getFuncSort(sort)) > MAX_SORTS){
      return false;
    }
  }
  
  return true;
  
}

unsigned LambdaElimination::countBasicSorts(Sorts::FunctionSort* fsort){
  CALL("LambdaElimination::countBasicSorts");
  
  unsigned total = 0;
  
  unsigned domain = fsort->getDomainSort();
  unsigned range = fsort->getRangeSort();
  
  total = env.sorts->isStructuredSort(domain) ? countBasicSorts(env.sorts->getFuncSort(domain)) : 1;
  total += env.sorts->isStructuredSort(range) ? countBasicSorts(env.sorts->getFuncSort(range)) : 1;
  
  return total;
}

bool LambdaElimination::_holAxiomsAdded = false; 


/** Function removes all apps, lambdas and top level connectives from
  * a lambda expression via 
  */  
  
TermList LambdaElimination::processBeyondLambda(Term* term)
{
   CALL("LambdaElimination::processBeyondLambda(Term*)");

   TermList appTerm; //The resulting term to be pushed onto _toBeProcessed 

   if(term->isSpecial()){   
    switch(term->functor()){
      case Term::SF_FORMULA: {
        Formula *fm = term->getSpecialData()->getFormula();
        Connective conn = fm->connective();
                      
        TermList constant; //The HOL constant for various connectives
                      
        switch(conn){
           case LITERAL: {
              Literal* literal = fm->literal();
              ASS(literal->isEquality()); //Is this a valid assumption?
              ASS_EQ(literal->arity(), 2); 
            
              TermList lhs = *literal->nthArgument(0);
              TermList rhs = *literal->nthArgument(1);                                

              if (lhs.isTerm()) { lhs = processBeyondLambda(lhs.term()); }
              if (rhs.isTerm()) { rhs = processBeyondLambda(rhs.term()); }            
                        
              unsigned lhsSort = sortOf(lhs);      
              unsigned appSort = env.sorts->addFunctionSort(lhsSort, Sorts::SRT_BOOL);
              unsigned equalsSort = env.sorts->addFunctionSort(lhsSort, appSort);
                                
              bool added;
              constant = addHolConstant("vEQUALS", equalsSort, added, Signature::Symbol::EQUALS);
              if(added && !env.options->HOLConstantElimination()){
                FormulaUnit* fu = addEqualityAxiom(constant, lhsSort, equalsSort);
                addAxiom(fu);
              }          
              unsigned app = introduceAppSymbol( equalsSort, lhsSort, appSort); 
              buildFuncApp(app, constant, lhs, appTerm);
              app = introduceAppSymbol( appSort, lhsSort, Sorts::SRT_BOOL);
              buildFuncApp(app, appTerm, rhs, appTerm);
              
              if(!literal->polarity()){
                added = false;
                unsigned notsort = env.sorts->addFunctionSort(Sorts::SRT_BOOL, Sorts::SRT_BOOL);
                constant = addHolConstant("vNOT", notsort, added, Signature::Symbol::NOT);
                if(added && !env.options->HOLConstantElimination()){
                  FormulaUnit* fu = addNotConnAxiom(constant, notsort);
                  addAxiom(fu);
                }
                unsigned notapp = introduceAppSymbol(notsort, Sorts::SRT_BOOL, Sorts::SRT_BOOL); 
                buildFuncApp(notapp, constant, appTerm, appTerm); 
              }
              return appTerm;
           }
           case IFF:
           case IMP:
           case XOR:{
              Formula* lhs = fm->left();
              Formula* rhs = fm->right();
                            
              unsigned constSort1 = env.sorts->addFunctionSort(Sorts::SRT_BOOL, Sorts::SRT_BOOL);
              unsigned constSort2 = env.sorts->addFunctionSort(Sorts::SRT_BOOL, constSort1);
              TermList form;
              bool added;
              if(conn == IFF){
                 constant = addHolConstant("vIFF", constSort2, added, Signature::Symbol::IFF);
              }else if(conn == IMP){
                 constant = addHolConstant("vIMP", constSort2, added, Signature::Symbol::IMP);
              }else{
                 constant = addHolConstant("vXOR", constSort2, added, Signature::Symbol::XOR);
              }
              if(added && !env.options->HOLConstantElimination()){
                FormulaUnit* fu = addBinaryConnAxiom(constant,constSort2, conn, constSort1);
                addAxiom(fu);
              }  

              unsigned app1arg = introduceAppSymbol( constSort2, Sorts::SRT_BOOL, constSort1); 
              unsigned app2arg = introduceAppSymbol( constSort1, Sorts::SRT_BOOL, Sorts::SRT_BOOL); 

              if(lhs->connective() == Connective::BOOL_TERM){
                  form = lhs->getBooleanTerm();
                  if(form.isTerm()){
                    form = processBeyondLambda(form.term());
                  }
              }else{
                  form = processBeyondLambda(Term::createFormula(lhs)); //needs updating!
              }           
              buildFuncApp(app1arg, constant, form, appTerm); 
              if(rhs->connective() == Connective::BOOL_TERM){
                  form = rhs->getBooleanTerm();
                  if(form.isTerm()){
                    form = processBeyondLambda(form.term());
                  }
              }else{
                  form = processBeyondLambda(Term::createFormula(rhs));
              }
              buildFuncApp(app2arg, appTerm, form, appTerm);  
              return appTerm;
           }
           case AND:
           case OR:{
              FormulaList* args = fm->args();
              FormulaList::Iterator argsIt(args);
                
              unsigned constSort1 = env.sorts->addFunctionSort(Sorts::SRT_BOOL, Sorts::SRT_BOOL);
              unsigned constSort2 = env.sorts->addFunctionSort(Sorts::SRT_BOOL, constSort1);
              TermList form;
              bool added;
              if(conn == AND){
                constant = addHolConstant("vAND", constSort2, added, Signature::Symbol::AND);
              }else{
                constant = addHolConstant("vOR", constSort2, added, Signature::Symbol::OR);
              }
              if(added && !env.options->HOLConstantElimination()){
                FormulaUnit* fu = addBinaryConnAxiom(constant, constSort2, conn, constSort1);
                addAxiom(fu);
              }
                
              unsigned app1arg = introduceAppSymbol( constSort2, Sorts::SRT_BOOL, constSort1); 
              unsigned app2arg = introduceAppSymbol( constSort1, Sorts::SRT_BOOL, Sorts::SRT_BOOL); 
                
              unsigned count = 1;
              while(argsIt.hasNext()){
                  Formula* arg = argsIt.next();
                  if(arg->connective() == Connective::BOOL_TERM){
                    form = arg->getBooleanTerm();
                    if(form.isTerm()){
                      form = processBeyondLambda(form.term());
                    }
                  }else{
                    form = processBeyondLambda(Term::createFormula(arg));
                  }
                  if(count == 1){
                    buildFuncApp(app1arg, constant, form, appTerm);
                  }else if(count == 2){
                    buildFuncApp(app2arg, appTerm, form, appTerm);
                  }else{
                    buildFuncApp(app1arg, constant, appTerm, appTerm); 
                    buildFuncApp(app2arg, appTerm, form, appTerm); 
                  }
                  count++;
              }
              return appTerm;                           
             }
             case NOT: {
                Formula* subForm = fm->uarg(); 
                
                bool added;
                TermList form;
                unsigned notsort = env.sorts->addFunctionSort(Sorts::SRT_BOOL, Sorts::SRT_BOOL);
                constant = addHolConstant("vNOT", notsort, added, Signature::Symbol::NOT);
                if(added && !env.options->HOLConstantElimination()){
                  FormulaUnit* fu = addNotConnAxiom(constant, notsort);
                  addAxiom(fu);
                }
                unsigned notapp = introduceAppSymbol(notsort, Sorts::SRT_BOOL, Sorts::SRT_BOOL); 
                if(subForm->connective() == Connective::BOOL_TERM){
                    form = subForm->getBooleanTerm();
                    if(form.isTerm()){
                        form = processBeyondLambda(form.term());
                    }
                }else{
                    form = processBeyondLambda(Term::createFormula(subForm));
                }
                buildFuncApp(notapp, constant, form, appTerm);
                return appTerm;                                                    
             }
             case FORALL:
             case EXISTS: {
                Formula::VarList* vars = fm->vars();
                Formula::VarList::Iterator vit(vars);
                Formula::SortList* sorts = fm->sorts();
                Stack<unsigned> sortsRev;

                TermList form;
                
                Formula* qform = fm->qarg();
                if(qform->connective() == Connective::BOOL_TERM){
                    form = qform->getBooleanTerm();
                    if(form.isTerm()){
                      form = processBeyondLambda(form.term());
                    }
                }else{
                    form = processBeyondLambda(Term::createFormula(qform));
                }
                if(Formula::SortList::isEmpty(sorts)){
                  unsigned res;
                  while(vit.hasNext()){
                    if(SortHelper::tryGetVariableSort(vit.next(), qform, res)){
                      sorts = sorts->addLast(sorts, res);
                    }
                  }
                }

                ASS_EQ(Formula::VarList::length(vars), Formula::SortList::length(sorts));
                unsigned lambdaExpSort = Sorts::SRT_BOOL;
                Formula::SortList::Iterator sit(sorts);
                while(sit.hasNext()){
                  sortsRev.push(sit.next());
                }
                while(!sortsRev.isEmpty()){
                  lambdaExpSort = env.sorts->addFunctionSort(sortsRev.pop(), lambdaExpSort);
                }
        
                Term* lambdaArg = Term::createLambda(form, LAMBDA, vars, sorts, Sorts::SRT_BOOL);     
                TermList translatedArg = elimLambda(lambdaArg);               
      
                unsigned constSort = env.sorts->addFunctionSort(lambdaExpSort, Sorts::SRT_BOOL);
                
                bool added;
                if(conn == FORALL){
                  constant = addHolConstant("vPI", constSort, added, Signature::Symbol::PI);   
                }else{
                  constant = addHolConstant("vSIGMA", constSort, added, Signature::Symbol::SIGMA);
                }
                if(added && !env.options->HOLConstantElimination()){
                  FormulaUnit* fu = addQuantifierAxiom(constant, constSort, conn, lambdaExpSort);
                  addAxiom(fu);
                }
                
                unsigned app = introduceAppSymbol( constSort, lambdaExpSort, Sorts::SRT_BOOL); 
                
                buildFuncApp(app, constant, translatedArg, appTerm);
        
                return appTerm;
             }
             case TRUE:
                return TermList(Term::foolTrue());
             case FALSE:
                return TermList(Term::foolFalse());
             default:
                ASSERTION_VIOLATION;
          
          }//switch conn
          break;    
            
      }
      case Term::SF_APP: {
          TermList lhs = term->getSpecialData()->getAppLhs();
          TermList rhs = *term->nthArgument(0);

          if(!lhs.isVar() && lhs.term()->isSpecial()){ //What about if it is HOL constant?
             lhs = processBeyondLambda(lhs.term());
          }
          if(!rhs.isVar() && rhs.term()->isSpecial()){
             rhs = processBeyondLambda(rhs.term());
          }
         
          unsigned lhsSort = SortHelper::getResultSort(lhs, _varSorts);
          unsigned rhsSort = SortHelper::getResultSort(rhs, _varSorts);
          unsigned appSort = term->getSpecialData()->getSort();
          unsigned app = introduceAppSymbol(lhsSort, rhsSort, appSort);
         
          TermList termResult;
          buildFuncApp(app, lhs, rhs, termResult); 
          return termResult;
      }
      case Term::SF_LAMBDA:
          return elimLambda(term);
      default:
          ASSERTION_VIOLATION;    
    }
   }
   
   return TermList(term); 
}   
  
  
TermList LambdaElimination::elimLambda(Term* lambdaTerm)
{
    CALL("LambdaElimination::elimLambda");
    
    Stack<int> _vars;
    Stack<unsigned> _sorts;
    Stack<TermList> _toBeProcessed;
  
    ASS(lambdaTerm->isSpecial());
    Term::SpecialTermData* sd = lambdaTerm->getSpecialData();
    ASS_EQ(sd->getType(), Term::SF_LAMBDA);
    
    TermList lambdaExp;
    Term::SortList* sorts = sd->getVarSorts();
    IntList* vars = sd->getLambdaVars();
    
    IntList::Iterator vlit(vars);
    Term::SortList::Iterator slit(sorts);
    

    while(vlit.hasNext()){
       _vars.push(vlit.next());
       _sorts.push(slit.next());
    }

    lambdaExp = sd->getLambdaExp();
    _toBeProcessed.push(lambdaExp);
  
    process(_vars, _sorts, _toBeProcessed);    
  
    return _processed.pop();
    
}


void LambdaElimination::process(Stack<int> _vars, Stack<unsigned> _sorts, Stack<TermList> _toBeProcessed){
   
  CALL("LambdaElimination::process");   
    
  int lambdaVar;
  unsigned lambdaVarSort;
  Stack<unsigned> _argNums;
   
  while(!_vars.isEmpty()){
    lambdaVar = _vars.pop();
    lambdaVarSort = _sorts.pop();
    
    while (!_toBeProcessed.isEmpty()){  
   
      _processing = _toBeProcessed.pop(); 
       
      if (_processing.isTerm()){ 
        
        Term* lExpTerm = _processing.term();
        IntList* freeVars = lExpTerm->freeVariables();
        
        if(IntList::member(lambdaVar, freeVars)){
          if(lExpTerm->isSpecial()){ 
            switch(lExpTerm->functor()){
              case Term::SF_FORMULA: {
                _toBeProcessed.push(processBeyondLambda(lExpTerm));
                break;
              }
              case Term::SF_APP: {
                TermList lhs = lExpTerm->getSpecialData()->getAppLhs();
                TermList rhs = *lExpTerm->nthArgument(0);
                
                unsigned sort = env.sorts->addFunctionSort(lambdaVarSort, lExpTerm->getSpecialData()->getSort());
                dealWithApp(lhs,rhs,sort, lambdaVar, _toBeProcessed, _argNums); 
                break;
              }
              case Term::SF_LAMBDA: {
                _toBeProcessed.push(elimLambda(lExpTerm));
                break;
              }
              default:
                ASSERTION_VIOLATION;
                //Not deailing with ITEs, Lets and Tuples at the moment.
            }                    
          }
          else //not special. Of the sort app(X,Y).
          {
            TermList firstArg = *lExpTerm->nthArgument(0);
            TermList secondArg = *lExpTerm->nthArgument(1);
            unsigned sort = env.sorts->addFunctionSort(lambdaVarSort, SortHelper::getResultSort(lExpTerm)); 
            dealWithApp(firstArg,secondArg,sort, lambdaVar, _toBeProcessed, _argNums);                
          }
        }
        else //In the case \x.exp where x is not free in exp.
        {
            unsigned kSort = env.sorts->addFunctionSort(lambdaVarSort, sortOf(_processing));
            addToProcessed(addKComb(kSort, processBeyondLambda(_processing.term())), _argNums);                  
        }
      }else{//lambda expression is a variable. If it is the lambda var, then this will be translated to I
       bool added;       
       if(_processing.var() == (unsigned)lambdaVar){ //an expression of the form \x.x
            unsigned iSort = env.sorts->addFunctionSort(lambdaVarSort, lambdaVarSort);
            TermList ts = addHolConstant("iCOMB", iSort, added, Signature::Symbol::I_COMB);
            if(added && env.options->combinatorElimination() != Options::CombElimination::INFERENCE_RULES
                     && !env.options->combinatoryUnification()){
              addCombinatorAxiom(ts, iSort, lambdaVarSort, Signature::Symbol::I_COMB);
            }
            addToProcessed(ts, _argNums);
        }else{ //an expression of the form \x.y 
            unsigned termSort = sortOf(_processing);
            unsigned kSort = env.sorts->addFunctionSort(lambdaVarSort, termSort);
            addToProcessed(addKComb(kSort, _processing), _argNums);
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


void LambdaElimination::dealWithApp(TermList lhs, TermList rhs, unsigned sort, int lambdaVar, Stack<TermList> &_toBeProcessed, Stack<unsigned> &_argNums)
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
      _argNums.push(0);
      _toBeProcessed.push(lhs);
      _toBeProcessed.push(rhs); 
    }else if(IntList::member(lambdaVar, lhsFVs)){
      _combinators.push(Signature::Symbol::C_COMB);
      _argNums.push(0);
      _toBeProcessed.push(lhs);
      rhs.isTerm() ? addToProcessed(processBeyondLambda(rhs.term()), _argNums) : addToProcessed(rhs, _argNums);  
    }else if(IntList::member(lambdaVar, rhsFVs)){
      _combinators.push(Signature::Symbol::B_COMB);            
      _argNums.push(0);
      _toBeProcessed.push(rhs);
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
    if(added && env.options->combinatorElimination() != Options::CombElimination::INFERENCE_RULES
             && !env.options->combinatoryUnification()){
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
    if(added && env.options->combinatorElimination() != Options::CombElimination::INFERENCE_RULES
             && !env.options->combinatoryUnification()){
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

void LambdaElimination::addAxiom(FormulaUnit* axiom, bool extensionalityAx) {
  CALL("LambdaElimination::addAxiom");

  _holAxiomsAdded = true;

  axiom->setHOLADescendant(true && !extensionalityAx);

  //ASS_REP(!needsElimination(def), def->toString()); To be looked at later AYB

  _axioms = new UnitList(axiom, _axioms);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    if(!_combinatorAdditionMode){
      env.out() << "[PP] Lambda Elimination added axiom: " << axiom->toString() << endl;
    } else {
      if(extensionalityAx){
        env.out() << "[PP] Extensionality axiom addition: " << axiom->toString() << endl;        
      }else{
        env.out() << "[PP] Heuristic combinator creation added axiom: " << axiom->toString() << endl;
      }
    }
    env.endOutput();
  }
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

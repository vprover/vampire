/**
 * @file FOOLElimAlt.cpp
 * FOOLElimination.cpp translates formulas in term contexts by renaming them.
 * This does not work if the formulas contain Du Bruijn indices as these
 * indices can then incorrectly become free. This class defines an alternative 
 * translation for formulas in term context.
 */
 

#include "Indexing/TermSharing.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Shell/Options.hpp"
//#include "Shell/SymbolOccurrenceReplacement.hpp"


#include "FOOLElimAlt.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;


TermList FOOLElimAlt::formulaToTerm(Formula* fm)
{
   CALL("FOOLElimAlt::formulaToTerm");

   Connective conn = fm->connective();
                      
  switch(conn){
    case LITERAL: {
      Literal* literal = fm->literal();
      ASS(literal->isEquality()); 
      //Is this a valid assumption? It ought to be, because TPTP syntax does not have a != (I think)
      ASS_EQ(literal->arity(), 2); 
      TermList lhs = process(*literal->nthArgument(0));
      TermList rhs = process(*literal->nthArgument(1));
                                                                
      unsigned equalsSort = sortOf(lhs);      
                                
      bool added = false; 
      unsigned logicalSym = addLogicalConnSym("vEQUALS" + Int::toString(equalsSort), equalsSort, 2, added);
      if(added && !env.options->HOLConstantElimination()){
        addConnAxiom(logicalSym, conn, equalsSort);
      }          
      return applyLogicalConn(logicalSym, lhs, rhs);
    }
    case IFF:
    case IMP:
    case XOR:{
      Formula* lhs = fm->left();
      Formula* rhs = fm->right();

      unsigned logicalSym;
      bool added;
      if(conn == IFF){
         logicalSym = addLogicalConnSym("vIFF", Sorts::SRT_BOOL, 2, added);
      }else if(conn == IMP){
         logicalSym = addLogicalConnSym("vIMP", Sorts::SRT_BOOL, 2, added);
      }else{
         logicalSym = addLogicalConnSym("vXOR", Sorts::SRT_BOOL, 2, added);
      }
      if(added && !env.options->HOLConstantElimination()){
         addConnAxiom(logicalSym, conn, Sorts::SRT_BOOL);
      }  
      
      return applyLogicalConn(logicalSym, formulaToTerm(lhs), formulaToTerm(rhs)); 
   }
   case AND:
   case OR:{
      FormulaList* connargs = fm->args();
      FormulaList::Iterator argsIt(connargs);
        
      unsigned logicalSym;
      bool added;
      if(conn == AND){
         logicalSym = addLogicalConnSym("vAND", Sorts::SRT_BOOL, 2, added);
      }else{
         logicalSym = addLogicalConnSym("vOR", Sorts::SRT_BOOL, 2, added);
      }
      if(added && !env.options->HOLConstantElimination()){
         addConnAxiom(logicalSym, conn, Sorts::SRT_BOOL);
      }
  
      Stack<Formula*> args;  
      while(argsIt.hasNext()){
         args.push(process(argsIt.next());
      }
      TermList f1 = formulaToTerm(args.pop());
      TermList f2;
      while(!args.isEmpty()){
        f2 = formulaToTerm(args.pop());
        f1 = applyLogicalConn(logicalSym, f1, f2);
      }
      return f1;                           
     }
     case NOT: {        
        bool added;
        unsigned logicalSym = addLogicalConnSym("vNOT", Sorts::SRT_BOOL, 1, added);
        if(added && !env.options->HOLConstantElimination()){
            addConnAxiom(logicalSym, conn, Sorts::SRT_BOOL);
        }
        
        TermList dummy;
        return applyLogicalConn(logicalSym, formulaToTerm(fm->uarg()), dummy, false);                                                    
     }
     case FORALL:
     case EXISTS: {
        Formula::VarList* vars = fm->vars();
        Formula::VarList::Iterator vit(vars);
        Formula::SortList* sorts = fm->sorts();
        Stack<unsigned> sortsRev;
        
        TermList qform = formulaToTerm(fm->qarg());

        if(Formula::SortList::isEmpty(sorts)){
          unsigned res;
          while(vit.hasNext()){
            if(SortHelper::tryGetVariableSort(vit.next(), fm->qarg(), res)){
              sorts = sorts->addLast(sorts, res);
            }
          }
        }

        Formula::SortList::Iterator sit(sorts);
        while(sit.hasNext()){
          sortsRev.push(sit.next());
        }

        TermList abstractedTerm = abstract(qform, sortsRev);
        
        unsigned logicalSym;
        bool added;
        if(conn == FORALL){
          logicalSym = addLogicalConnSym("vPI", sortOf(abstractedTerm) , 1, added);   
        }else{
          logicalSym = addLogicalConnSym("vSIGMA", sortOf(abstractedTermSort) , 1, added); 
        }
        if(added && !env.options->HOLConstantElimination()){
            addQuantifierAxiom(constant, constSort, conn, lambdaExpSort);
        }
        
        return applyLogicalConn(logicalSym, abstractedTerm);
     }
     case TRUE:
        return TermList(Term::foolTrue());
     case FALSE:
        return TermList(Term::foolFalse());
     default:
        ASSERTION_VIOLATION;
  
  }//switch conn
  
}   
  
TermList FOOLElimAlt::process(TermList ts){   
   CALL("FOOLElimAlt::process");
   
   if(ts.isVar()){
     return ts;
   }

   Term* term = ts.term();
   if(term->isSpecial()){
     ASS(term->functor() == Term::SF_FORMULA);
     Formula* fm = term->getSpecialData()->getFormula();
     return formulaToTerm(fm);
   }
   
   Stack<TermList> arguments;
   Term::Iterator ait(term);
   while (ait.hasNext()) {
     arguments.push(process(ait.next()));
   }
   
   return TermList(Term::create(term, arguments.begin()));
}
  
  
unsigned FOOLElimAlt::domain(unsigned sort){   
    unsigned dom = env.sorts->getFuncSort(sort)->getDomainSort();
    return dom;
}

unsigned FOOLElimAlt::range(unsigned sort){
    unsigned range = env.sorts->getFuncSort(sort)->getRangeSort();
    return range;
}

TermList FOOLElimAlt::addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant cnst){

    CALL("FOOLElimAlt::addHolConstant");

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

unsigned FOOLElimAlt::sortOf(TermList t)
{
  CALL("FOOLElimAlt::sortOf");
  
  return SortHelper::getResultSort(t, _varSorts);
  
} 

void FOOLElimAlt::addAxiom(FormulaUnit* axiom) {
  CALL("FOOLElimAlt::addAxiom");

  //ASS_REP(!needsElimination(def), def->toString()); To be looked at later AYB

  _axioms = new UnitList(axiom, _axioms);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Lambda Elimination added axiom: " << axiom->toString() << endl;
    env.endOutput();
  }
}
  
unsigned FOOLElimAlt::addLogicalConnSym(vstring name, unsigned sort1, unsigned argNum, bool &added) {
    
  CALL("FOOLElimAlt::addLogicalConnSym");
 
  Stack<unsigned> sorts;
  for (int i = 0; i < argNum; i ++){
    sorts.push(sort1); 
  }
  
  OperatorType* type = OperatorType::getFunctionType(argNum, sorts.begin(), Sorts::SRT_BOOL);
  unsigned symbol = env.signature->addFunction(name, argNum, added, false, true);
  
  if(added){
   //TO DO mark symbol in someway to allow fo special inference rules.
   env.signature->getFunction(symbol)->setType(type);
   if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Lambda or application elimination introduced ";
    env.out() << "function symbol " << env.signature->functionName(symbol) << endl;
    env.out() << " of the sort " << type->toString() << endl; //This produces really long and horrible output.
    env.endOutput();
   }
  }
  
  return symbol;
}

TermList FOOLElimAlt::applyLogicalConn(unsigned symbol, TermList arg1, TermList arg2, bool bothArgs) {
  CALL("FOOLElimAlt::applyLogicalConn");

  ASS_L(env.signature->functionArity(symbol), 3);
  
  if(bothArgs){
    return TermList(Term::create2(symbol, arg1, arg2));
  }else{
    return TermList(Term::create1(symbol, arg1));
  }
}

 
 void FOOLElimAlt::addConnAxiom(unsigned fun, Connective conn, unsigned argSort)
 {
    CALL("FOOLElimAlt::addBinaryConnAxiom"); 
    
    Formula* axiom;
    Formula* varFormula;
  
    TermList var1 = TermList(0, false);
    TermList var2 = TermList(1, false);
     
    Formula::VarList* vl = new Formula::VarList(var1.var());
    Formula::SortList* sl = new Formula::SortList(argsSort);
    if(conn != NOT){
      vl = vl->addLast(vl, var2.var());
      sl = sl->addLast(sl, argsSort);
    }
    
    TermList functionApplied = applyLogicalConn(fun, var1, conn != NOT ? var2);
    
    switch(conn){
      case AND:
      case OR: {
        FormulaList* args = new FormulaList(toEquality(var1));
        args = FormulaList::cons(toEquality(var2), args);
        varFormula = new JunctionFormula(conn, args);        
        break;
      }
      case LITERAL: {
        varFormula = createEquality(var1, var2, argsSort);
        break;
      }
      case NOT: {
        varFormula = new NegatedFormula(toEquality(var1));
        break;
      }
      default: {
        varFormula = new BinaryFormula(conn, toEquality(var1), toEquality(var2));
      }
    }
    
    axiom = toEquality(functionApplied);
    axiom = new BinaryFormula(IFF, axiom, varFormula);
    axiom = new QuantifiedFormula(FORALL, varList, sortList, binaryConnAxiom); 
    
    //Change this!
    Inference* binConInf = binConInf = new Inference(Inference::LAMBDA_ELIMINATION_BIN_CON);
    
    addAxiom(new FormulaUnit(axiom, binConInf, Unit::AXIOM));  
 }
 
 Formula* FOOLElimAlt::createEquality(TermList t1, TermList t2, unsigned sort) {
   Literal* equality = Literal::createEquality(true, t1, t2, sort);
   return new AtomicFormula(equality);
     
 }
 
Formula* FOOLElimAlt::toEquality(TermList booleanTerm) {
  TermList truth(Term::foolTrue());
  Literal* equality = Literal::createEquality(true, booleanTerm, truth, Sorts::SRT_BOOL);
  return new AtomicFormula(equality);
}

TermList FOOLElimAlt::abstract(TermList term, Stack<unsigned> sorts){
  
   CALL("FOOLElimAlt::abstract");

   TermList abstractedTerm = term;
   
   unsigned lamSort = env.sorts->addFunctionSort(sorts.pop(), Sorts::SRT_BOOL);
   unsigned termSort = Sorts::SRT_BOOL;
   
   while(true){
     Stack<unsigned> sorts2;
     sorts2.push(termSort);
     OperatorType* type = OperatorType::getFunctionType(1, sorts2.begin(), lamSort);

     bool added;
     unsigned fun = env.signature->addFunction("lam_" + Int::toString(lamSort),1,added);
     if(added){//first time constant added. Set type
       Signature::Symbol* symbol = env.signature->getFunction(fun);  
       symbol->setType(type);
       symbol->markLambda();   
     } 
     abstractedTerm = TermList(Term::create1(fun, abstractedTerm));
     
     if(sorts.isEmpty()){ break; }
     
     termSort = lamSort;
     lamSort = env.sorts->addFunctionSort(sorts.pop(), lamSort);
   }

   return abstractedTerm;   
}
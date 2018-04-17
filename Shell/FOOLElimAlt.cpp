/*
 * File FOOLElimAlt.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file FOOLElimAlt.cpp
 * FOOLElimination.cpp translates formulas in term contexts by renaming them.
 * This does not work if the formulas contain Du Bruijn indices as these
 * indices can then incorrectly become free. This class defines an alternative 
 * translation for formulas in term context.
 */
 
#include "Parse/TPTP.hpp"

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
      unsigned logicalSym = addLogicalConnSym("vEQUALS_" + Int::toString(equalsSort), equalsSort, 2, added, SigSym::EQUALS);
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
         logicalSym = addLogicalConnSym("vIFF", Sorts::SRT_BOOL, 2, added, SigSym::IFF);
      }else if(conn == IMP){
         logicalSym = addLogicalConnSym("vIMP", Sorts::SRT_BOOL, 2, added, SigSym::IMP);
      }else{
         logicalSym = addLogicalConnSym("vXOR", Sorts::SRT_BOOL, 2, added, SigSym::XOR);
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
         logicalSym = addLogicalConnSym("vAND", Sorts::SRT_BOOL, 2, added, SigSym::AND);
      }else{
         logicalSym = addLogicalConnSym("vOR", Sorts::SRT_BOOL, 2, added, SigSym::OR);
      }
      if(added && !env.options->HOLConstantElimination()){
         addConnAxiom(logicalSym, conn, Sorts::SRT_BOOL);
      }
  
      Stack<Formula*> args;  
      while(argsIt.hasNext()){
         args.push(argsIt.next());
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
     unsigned logicalSym = addLogicalConnSym("vNOT", Sorts::SRT_BOOL, 1, added, SigSym::NOT);
     if(added && !env.options->HOLConstantElimination()){
       addConnAxiom(logicalSym, conn, Sorts::SRT_BOOL);
     }
        
     TermList dummy;
     return applyLogicalConn(logicalSym, formulaToTerm(fm->uarg()), dummy, false);                                                    
   }
   case FORALL:
   case EXISTS: {
     
      Formula::VarList* vars = fm->vars();
      Stack<unsigned> sortsRev;
      Stack<int> varsRev;
      
      TermList qform = formulaToTerm(fm->qarg());

      Formula::VarList::Iterator vit(vars);
      while(vit.hasNext()){
        varsRev.push(vit.next());
      }

      vit.reset(vars);
      while(vit.hasNext()){
         int var = vit.next();
         sortsRev.push(_varSorts.get(var));
      }

      qform = lift(qform, varsRev.size(), 0);
      qform = convertToDuBruijnIndices(qform, varsRev);
      TermList abstractedTerm = abstract(qform, Sorts::SRT_BOOL, sortsRev);
      unsigned sort = sortOf(abstractedTerm);
      
      unsigned logicalSym;
      bool added;
      if(conn == FORALL){
        logicalSym = addLogicalConnSym("vPI_" + Int::toString(sort), sort , 1, added, SigSym::PI);   
      }else{
        logicalSym = addLogicalConnSym("vSIGMA_"  + Int::toString(sort), sort , 1, added, SigSym::SIGMA); 
      }
      
      TermList dummy;
      return applyLogicalConn(logicalSym, abstractedTerm, dummy, false);
   }
   case BOOL_TERM:
      return fm->getBooleanTerm();
   case TRUE:
      return TermList(Term::foolTrue());
   case FALSE:
      return TermList(Term::foolFalse());
   default:
      //cout << "Dealing with formula " + fm->toString() << endl;
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
    env.out() << "[PP] FOOL elimination added axiom: " << axiom->toString() << endl;
    env.endOutput();
  }
}
  
unsigned FOOLElimAlt::addLogicalConnSym(vstring name, unsigned sort1, unsigned argNum, bool &added, SigSymHol cnst) 
{
    
  CALL("FOOLElimAlt::addLogicalConnSym");
 
  Stack<unsigned> sorts;
  for (unsigned i = 0; i < argNum; i ++){
    sorts.push(sort1); 
  }
  
  OperatorType* type = OperatorType::getFunctionType(argNum, sorts.begin(), Sorts::SRT_BOOL);
  unsigned symbol = env.signature->addFunction(name, argNum, added, false, true);
  
  if(added){
   Signature::Symbol* sym = env.signature->getFunction(symbol);
   sym->setType(type);
   sym->markHoLogicalConn(cnst);
   if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] FOOL elimination introduced ";
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
    Formula::SortList* sl = new Formula::SortList(argSort);
    if(conn != NOT){
      vl = vl->addLast(vl, var2.var());
      sl = sl->addLast(sl, argSort);
    }
    
    TermList functionApplied = applyLogicalConn(fun, var1, var2, conn == NOT ? false : true);
    
    switch(conn){
      case AND:
      case OR: {
        FormulaList* args = new FormulaList(toEquality(var1));
        args = FormulaList::cons(toEquality(var2), args);
        varFormula = new JunctionFormula(conn, args);        
        break;
      }
      case LITERAL: {
        varFormula = createEquality(var1, var2, argSort);
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
    axiom = new QuantifiedFormula(FORALL, vl, sl, axiom); 
    
    //Change this!
    Inference* binConInf = new Inference(Inference::LAMBDA_ELIMINATION_BIN_CON);
    
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

TermList FOOLElimAlt::abstract(TermList term, unsigned termSort, Stack<unsigned> sorts){
  
   CALL("FOOLElimAlt::abstract");

   TermList abstractedTerm = term;

   unsigned lamSort = env.sorts->addFunctionSort(sorts.pop(), termSort);
   
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

TermList FOOLElimAlt::convertToDuBruijnIndices(TermList t, Stack<int> vars){
  CALL("FOOLElimAlt::convertToDuBruijnIndices");
  
  if(t.isVar()){
    for(int i = vars.size() - 1; i >= 0; i--){
      if(vars[i] != -1 && (unsigned)vars[i] == t.var()){
        unsigned sort = sortOf(t);
        vstring name = Int::toString(vars.size() - i) + "_" + Int::toString(sort);
        OperatorType* type =  OperatorType::getConstantsType(sort);
        unsigned fun = addDuBruijnIndex(name, type);
        return TermList(Term::createConstant(fun));
      }
    }
    return t;
  }
  
  bool modified = false;
  Term* term = t.term();
  Term* newTerm = Term::cloneNonShared(term);
  
  if(!term->hasVarHead()){
  	Signature::Symbol* sym = env.signature->getFunction(term->functor());
  	if(sym->lambda()){ vars.push(-1); }
  } else {
  	int headVar = env.signature->getVarName(term->functor());
  	for(int i = vars.size() - 1; i >= 0; i --){
      if(vars[i] == headVar){
  	    OperatorType* type = env.signature->getVarType(term->functor());
  	    vstring name = Int::toString(vars.size() - i) + "_" + Int::toString(toSort(type));
        unsigned fun = addDuBruijnIndex(name, type);
        newTerm->makeSymbol(fun, newTerm->arity());
        modified = true;
      }
    }
  }
 
  TermList* args = term->args();
  TermList* newArgs = newTerm->args();
  while(!args->isEmpty()){
  	TermList ts = convertToDuBruijnIndices(*args, vars);
  	if(!TermList::equals(ts, *args)){
      *newArgs = ts;
  		modified = true;
  	}
  	args = args->next();
    newArgs = newArgs->next();
  }

  if(modified){
    return TermList(env.sharing->insert(newTerm));
  }

  newTerm->destroy();
  return t;

}

/**
  * Adds function with name @b name and type @b type and amrk as an index
  * @since 19/03/2018
  * @author Ahmed Bhayat
  */
unsigned FOOLElimAlt::addDuBruijnIndex(vstring name, OperatorType* type){
  CALL("FOOLElimAlt:::addDuBruijnIndex");

  bool added;
  unsigned fun = env.signature->addFunction(name ,type->arity(),added, false, 2);
  if(added){//first time constant added. Set type
    Signature::Symbol* symbol = env.signature->getFunction(fun);  
    symbol->setType(type);
  }
  return fun;

}

unsigned FOOLElimAlt::toSort(OperatorType* type){
  CALL("FOOLElimAlt::toSort");
  
  unsigned sort = type->result();
  for (int i = type->arity() - 1; i >= 0; i--){
    sort = env.sorts->addFunctionSort(type->arg(i), sort);
  }

  return sort;

}

OperatorType* FOOLElimAlt::toType(unsigned sort){
  CALL("FOOLElimAlt::toType");

  Stack<unsigned> sorts;  
  if(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::FUNCTION)){
    while(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::FUNCTION)){
      sorts.push(env.sorts->getFuncSort(sort)->getDomainSort());
      sort = env.sorts->getFuncSort(sort)->getRangeSort();
    }
    return OperatorType::getFunctionType(sorts.size(), sorts.begin(), sort);

  }
  return OperatorType::getConstantsType(sort);
}

/**
  * If @name represents a Du Bruijn index, it is lifted by @value 
  * @since 19/03/2018
  * @author Ahmed Bhayat
  */
vstring FOOLElimAlt::lift(vstring name, unsigned value){
  CALL("FOOLElimAlt::lift(vstring, unsigned)");
  
  ASS_REP(name.find("_") > 0, name);
  
  unsigned underPos = name.find("_");
  vstring index = name.substr(0, underPos);
  int liftedIndex;
  Int::stringToInt(index, liftedIndex);
  liftedIndex = liftedIndex + value;
  return Int::toString(liftedIndex) + name.substr(underPos);
}


TermList FOOLElimAlt::lift(TermList ts, unsigned value, unsigned cutoff){
  CALL("FOOLElimAlt:::lift(TermList, unsigned, unsigned)");
  
  if(ts.isVar()){
    return ts;
  }
  return TermList(lift(ts.term(), value, cutoff));
  
}

Term* FOOLElimAlt::lift(Term* term, unsigned value, unsigned cutoff){
  CALL("FOOLElimAlt:::lift(Term*, unsigned, unsigned)");

  if(term->isSpecial()){
    ASS_REP(term->functor() == Term::SF_FORMULA, term->toString());
    ASS_EQ(term->arity(),0);   
    Term::SpecialTermData* sd = term->getSpecialData();
    Formula* orig = lift(sd->getFormula(), value, cutoff);
    if(orig==sd->getFormula()) {
      return term;
    }
    return Term::createFormula(orig);
  }
  
  bool headModified = false;
  Term* liftedTerm;
  
  if(term->hasVarHead()){
    liftedTerm = Term::cloneNonShared(term);
    if(lift(term->args(), liftedTerm->args(), value, cutoff)){
      return env.sharing->insert(liftedTerm);      
    }else{
      return term;
    }
  }
  
  Signature::Symbol* sym = env.signature->getFunction(term->functor()); 
  vstring index = sym->name();
  if(sym->duBruijnIndex() && indexGreater(index, cutoff)){
    vstring newIndex = lift(index, value);
    unsigned fun = FOOLElimAlt::addDuBruijnIndex(newIndex, sym->fnType());
    unsigned arity = term->arity();
    liftedTerm = new(arity) Term;
    liftedTerm->makeSymbol(fun, arity);
    for (int i = arity-1;i >= 0;i--) {
      TermList ss = *(term->nthArgument(i));
      *(liftedTerm->nthArgument(i)) = ss;
    }
    headModified = true;
  }else{
    liftedTerm = Term::cloneNonShared(term);
  }
  bool argsChanged = sym->lambda() ? lift(term->args(), liftedTerm->args(), value, cutoff+1) :
                                     lift(term->args(), liftedTerm->args(), value, cutoff);
  if(argsChanged || headModified){
    if(TermList::allShared(liftedTerm->args())){
      return env.sharing->insert(liftedTerm);
    } else {
      return liftedTerm;
    }
  }
  liftedTerm->destroy();
  return term;
  
}

bool FOOLElimAlt::lift(TermList* from, TermList* to, unsigned value, unsigned cutoff){
  CALL("lift(TermList*, TermList*, unsigned , unsigned)");

  bool changed = false;
  while (!from->isEmpty()) {
    if (from->isVar()) {
      to->makeVar(from->var());
    }
    else { // from is not a variable
      Term* f = from->term();
      Term* t = lift(f, value, cutoff);
      to->setTerm(t);
      if (f != t) {
        changed = true;
      }
    }
    from = from->next();
    ASS(! to->isEmpty());
    to = to->next();
  }
  ASS(to->isEmpty());
  return changed;
}

Formula* FOOLElimAlt::lift(Formula* f, unsigned value, unsigned cutoff){
  CALL("FOOLElimAlt::lift(Formula*, unsigned, unsigned)");
 
  switch (f->connective()) {
  case LITERAL: 
  {
    Literal* l = f->literal();
    ASS(l->isEquality());
    Literal* m = new(l->arity()) Literal(*l);
    if (lift(l->args(),m->args(), value, cutoff)) {
      if(TermList::allShared(m->args())) {
        return new AtomicFormula(env.sharing->insert(m));
      } else {
        return new AtomicFormula(m);
      }
    }
    // literal not changed
    m->destroy();
    return f;
  }

  case AND: 
  case OR: 
  {
    FormulaList* newArgs = lift(f->args(), value, cutoff);
    if (newArgs == f->args()) {
      return f;
    }
    return new JunctionFormula(f->connective(), newArgs);
  }

  case IMP: 
  case IFF: 
  case XOR:
  {
    Formula* l = lift(f->left(), value, cutoff);
    Formula* r = lift(f->right(), value, cutoff);
    if (l == f->left() && r == f->right()) {
      return f;
    }
    return new BinaryFormula(f->connective(), l, r);
  }

  case NOT:
  {
    Formula* arg = lift(f->uarg(), value, cutoff);
    if (f->uarg() == arg) {
      return f;
    }
    return new NegatedFormula(arg);
  }

  case FORALL: 
  case EXISTS:
  {
    Formula* arg = lift(f->qarg(), value, cutoff);
    if (f->qarg() == arg) {
      return f;
    }
    return new QuantifiedFormula(f->connective(),f->vars(),0,arg); 
  }

  case TRUE:
  case FALSE:
    return f;

  case BOOL_TERM:
     return new BoolTermFormula(lift(f->getBooleanTerm(), value, cutoff));

  default:
    ASSERTION_VIOLATION;

  }
  
}

FormulaList* FOOLElimAlt::lift (FormulaList* fs, unsigned value, unsigned cutoff){
  CALL ("FOOLElimAlt::lift (FormulaList*, unsigned , unsigned )");

  Stack<FormulaList*>* els;
  Recycler::get(els);
  els->reset();

  FormulaList* el = fs;
  while(el) {
    els->push(el);
    el = el->tail();
  }

  FormulaList* res = 0;

  bool modified = false;
  while(els->isNonEmpty()) {
    FormulaList* el = els->pop();
    Formula* f = el->head();
    Formula* g = lift(f, value, cutoff);
    if(!modified && f!=g) {
      modified = true;
    }
    if(modified) {
      FormulaList::push(g, res);
    }
    else {
      res = el;
    }
  }

  Recycler::release(els);
  return res;
} 

/**
  * Returns true if @b index represents a Du Bruijn index greater than @b cutoff
  * @since 19/03/2018
  * @author Ahmed Bhayat
  */
bool FOOLElimAlt::indexGreater(vstring index, unsigned cutoff){
   CALL("FOOLElimAlt::indexGreater");
   
   int ind = 0;
   Int::stringToInt(index.substr(0,index.find("_")), ind);
   if((unsigned)ind > cutoff){
     return true;
   }
   return false;
}  

TermList FOOLElimAlt::etaExpand(unsigned fun, OperatorType* type, bool ex, Stack<TermList> existingArgs){
  CALL("FOOLElimAlt::etaExpand");

  unsigned arity = type->arity();
  static Stack<TermList> args(arity);
  
  unsigned exargs = 0;
  if(ex){ 
    exargs = existingArgs.size();
    for(unsigned i = 0; i < exargs; i++){
      args.push(existingArgs[i]);
    }    
  }
  unsigned count = exargs;  
  Stack<unsigned> sorts;
  
  for(int i = arity; i > exargs; i--){
    unsigned sort = type->arg(count);
    sorts.push(sort);
    OperatorType* subType = toType(sort);
    unsigned index = addDuBruijnIndex(Int::toString(i - exargs + subType->arity()) + "_" + Int::toString(sort), subType);
    if(!subType->arity()){
      args.push(TermList(Term::createConstant(index)));
    }else{
      Stack<TermList> dummy;
      args.push(etaExpand(index, subType, false, dummy));
    }
    count++;
  }
  
  Term* expandedTerm = Term::create(fun, arity, args.begin());
  TermList et = abstract(TermList(expandedTerm), type->result(), sorts);
 
  return et;
}
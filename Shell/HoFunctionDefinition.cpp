
/*
 * File HoHoFunctionDefinition.cpp.
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
 * @file HoHoFunctionDefinition.cpp
 * Implements class HoFunctionDefinition implementing work with definitions.
 *
 * @since 29/03/2018 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/BitUtils.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedLet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"
#include "Shell/BetaReductionEngine.hpp"

#include "Statistics.hpp"

#include "HoFunctionDefinition.hpp"

#if VDEBUG
#include <iostream>
#endif

namespace Shell {

using namespace Lib;
using namespace Kernel;

struct HoFunctionDefinition::HoDef {
  /** functor of defined HOL function */
  unsigned definiendum;
  /** right hand side of definition */
  Term* definiens;
  /** stack of non-index functors appearing in the definiens */
  Stack<unsigned> _rhsFunctors;
  /** clause that states definition. used to create inference */
  Clause* defCl;
  
  HoDef(Term* defin, unsigned definien, Stack<unsigned> functors)
    : definiendum(definien),
      definiens(defin),
      _rhsFunctors(functors)
  {
  }

  ~HoDef()
  {
  }

  CLASS_NAME(HoFunctionDefinition::HoDef);
  USE_ALLOCATOR(HoDef);
};

HoFunctionDefinition::HoFunctionDefinition ()
{
  CALL("HoFunctionDefinition::HoFunctionDefinition");
} // HoFunctionDefinition::HoFunctionDefinition

HoFunctionDefinition::~HoFunctionDefinition ()
{
  CALL("HoFunctionDefinition::~HoFunctionDefinition");
  
  Fn2DefMap::Iterator dit(_defs);
  while(dit.hasNext()) {
    delete dit.next();
  }
}

void HoFunctionDefinition::removeAllDefinitions(Problem& prb)
{
  CALL("HoFunctionDefinition::removeAllDefinitions(Problem&)");

  if(removeAllDefinitions(prb.units())) {
    prb.invalidateByRemoval();
  }
}

/**
 * When possible, unfold function definitions in @b units and remove them
 * Return true iff the list of units was modified.
 */
bool HoFunctionDefinition::removeAllDefinitions(UnitList*& units)
{
  CALL("HoFunctionDefinition::removeAllDefinitions");

  UnitList::DelIterator scanIterator(units);
  while(scanIterator.hasNext()) {
    Clause* cl=static_cast<Clause*>(scanIterator.next());
    ASS_REP(cl->isClause(), cl->toString());
    HoDef* def = isFunctionDefinition(cl);
    if(def) {
      def->defCl = cl;
      scanIterator.del();
      if(isSafe(def)){
        _safeDefs.push(def);
        _safeFunctors.insert(def->definiendum);
      }else{
        _defs.insert(def->definiendum, def);
        _possiblyUnsafeFunctors.push(def->definiendum);
      }
    }
  }
  bool modified = true;
  while(!_defs.isEmpty() && modified){
    modified = false;
    for(unsigned i = 0; i < _possiblyUnsafeFunctors.size(); i ++){
      //Could possibly have been removed on a previous pass through
      //the loop.
      if(_defs.find(_possiblyUnsafeFunctors[i])){
        HoDef* def = _defs.get(_possiblyUnsafeFunctors[i]);
        if(isSafe(def)){
          _defs.remove(_possiblyUnsafeFunctors[i]);
          _safeDefs.push(def);
          modified = true;
        }
      }
    }
  }
  if(!_defs.isEmpty()){
    Fn2DefMap::Iterator dit(_defs);
    //Couldn't prove these units to be safe definitions.
    //Add them back to unitlist.
    while(dit.hasNext()) {
      HoDef* def = dit.next();
      UnitList::push(def->defCl, units);
    }
    _defs.reset();
    //USER_ERROR("Input problem contains circular definition");
  }
  //At this point the ith def in _safeDefs refers to definitions stored in 
  //_safeDefs[j] for some j < i.
  //Next each definition is rewritten and added to _defs.  
 
  for(unsigned i = 0; i < _safeDefs.size(); i++){
    HoDef* def = _safeDefs[i];
    Term* unfoldedterm = unfoldDefs(def->definiens);
    if(def->definiens != unfoldedterm){
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] HO fn def discovered: " + env.signature->functionName(def->definiendum) + " = " + def->definiens->toString()
        + "\n  unfolded: " + env.signature->functionName(def->definiendum) + " = " +  unfoldedterm->toString() << std::endl;
        env.endOutput();
      }
      def->definiens = unfoldedterm;
    }
    _defs.insert(def->definiendum, def);    
  }
  
  //Unfold definitions within units
 
  UnitList::DelIterator unfoldIterator(units);
  while(unfoldIterator.hasNext()) {
    Clause* cl=static_cast<Clause*>(unfoldIterator.next());
    ASS(cl->isClause());
    Clause* newCl=applyDefinitions(cl);
    if(cl!=newCl) {
//      cout<<"D- "<<(*cl)<<endl;
//      cout<<"D+ "<<(*newCl)<<endl;
      unfoldIterator.replace(newCl);
    }
  }
 
  return true;
}

Term* HoFunctionDefinition::unfoldDefs(Term* term)
{
  CALL("HoFunctionDefinition::unfoldDefs");
  
  ASS(term->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(term->args());

  for (;;) {    
    TermList* tt=toDo.pop();
    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    HoDef* def;
    if(_defs.find(t->functor(), def)){
      BetaReductionEngine bre = BetaReductionEngine();
      TermList newTerm = TermList(def->definiens);
      for(unsigned j = 0; j < t->arity(); j++){
        TermList ts = *(t->nthArgument(j));
        ASS(newTerm.isTerm());
        newTerm = bre.betaReduce(newTerm.term(), ts); 
      }        
      modified.setTop(true);
      if(newTerm.isTerm()){
        Term* nt = newTerm.term();
        terms.push(nt);//push to terms the beta reduce version of def->definiens
        modified.push(false);
        toDo.push(nt->args());
        continue;
      } else {
        //beta reduction returned variable.
        args.push(newTerm);
        continue;
      }
    }
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),term->arity());

  if (!modified.pop()) {
    // we call replace in superposition only if we already know,
    // there is something to be replaced.
    // ASSERTION_VIOLATION; // MS: but there is now a new use in InnerRewriting which does not like this extra check
    return term;
  }

  // here we assume, that stack is an array with
  // second topmost element as &top()-1, third at
  // &top()-2, etc...
  TermList* argLst=&args.top() - (term->arity()-1);
  if (term->isLiteral()) {
    Literal* lit = static_cast<Literal*>(term);
    ASS_EQ(args.size(), lit->arity());
    return Literal::create(lit,argLst);
  }
  return Term::create(term,argLst);
  
}

/* Returns true if all the function symbols
 * occuring on the right-hand side of the definition
 * have been defined in definitions already stored in
 * _safeDefs
 */

bool HoFunctionDefinition::isSafe(HoDef* def)
{
  CALL("HoFunctionDefinition::isSafe");
  
  Stack<unsigned> defFuncs = def->_rhsFunctors;
  for(unsigned i = 0; i < defFuncs.size(); i++){
    if(!_safeFunctors.find(defFuncs[i])){
      return false;
    }         
  }
  return true;
}

Clause* HoFunctionDefinition::applyDefinitions(Clause* cl)
{
  CALL("HoFunctionDefinition::applyDefinitions(Clause*)");
  
  unsigned clen=cl->length();

  static Stack<HoDef*> usedDefs(8);
  static Stack<Literal*> resLits(8);
  ASS(usedDefs.isEmpty());
  resLits.reset();

  bool modified=false;
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    Literal* rlit=static_cast<Literal*>(applyDefinitions(lit, &usedDefs));
    resLits.push(rlit);
    modified|= rlit!=lit;
  }
  if(!modified) {
    ASS(usedDefs.isEmpty());
    return cl;
  }

  UnitList* premises=0;
  Unit::InputType inpType = cl->inputType();
  while(usedDefs.isNonEmpty()) {
    Clause* defCl=usedDefs.pop()->defCl;
    UnitList::push(defCl, premises);
    //The only type of clauses that can be definitions are those marked DEFINITION
    //We are not interested in these in the remainder of proof search.
    /*if(inpType != Unit::CONJECTURE){
      inpType = (Unit::InputType)	Int::max(inpType, defCl->inputType());
    }*/
  }
  UnitList::push(cl, premises);
  Inference* inf = new InferenceMany(Inference::DEFINITION_UNFOLDING, premises);

  Clause* res = new(clen) Clause(clen, inpType, inf);
  res->setAge(cl->age());

  for(unsigned i=0;i<clen;i++) {
    (*res)[i] = resLits[i];
  }

  return res;
}


Term* HoFunctionDefinition::applyDefinitions(Literal* lit, Stack<HoDef*>* usedDefs)
{
  CALL("HoFunctionDefinition::applyDefinitions");
    
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] applying HO function definitions to literal "<<(*lit) << std::endl;
    env.endOutput();
  }
  
  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(lit->args());

  for (;;) {

    TermList* tt=toDo.pop();
    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      Term* tempTerm = Term::create(orig,argLst);      
      args.push(TermList(tempTerm));
      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    HoDef* def;
    if(_defs.find(t->functor(), def)){
      usedDefs->push(def);
      BetaReductionEngine bre = BetaReductionEngine();
      TermList newTerm = TermList(def->definiens);
      for(unsigned j = 0; j < t->arity(); j++){
        TermList ts = *(t->nthArgument(j));
        ASS(newTerm.isTerm());
        newTerm = bre.betaReduce(newTerm.term(), ts); 
      }   
      modified.setTop(true);
      if(newTerm.isTerm()){
        Term* nt = newTerm.term();
        terms.push(nt);//push to terms the beta reduce version of def->definiens
        modified.push(false);
        toDo.push(nt->args());
        continue;
      } else {
        //beta reduction returned variable.
        args.push(newTerm);
        continue;
      }
    }
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  if (!modified.pop()) {
    return lit;
  }
    
  // here we assume, that stack is an array with
  // second topmost element as &top()-1, third at
  // &top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);
  Literal* newLit = Literal::create(static_cast<Literal*>(lit),argLst);

  if(env.options->showPreprocessing()){
    env.beginOutput();
    env.out() << " Discovered definition(s) in literal. The unfolded beta-reduced version is "<<(*newLit) << std::endl;
    env.endOutput();
  }  
  
  return newLit;
}


HoFunctionDefinition::HoDef* 
HoFunctionDefinition::isFunctionDefinition (Clause* clause)
{
  CALL("HoFunctionDefinition::isFunctionDefinition(Clause*)");

  if (clause->length() != 1) {
    return 0;
  }
  return isFunctionDefinition((*clause)[0]);
} // Definition::isFunctionDefinition (Clause* c)


HoFunctionDefinition::HoDef* 
HoFunctionDefinition::isFunctionDefinition (Literal* lit)
{
  CALL("HoFunctionDefinition::isFunctionDefinition(Literal*)");
  
  if (! lit->isPositive() ||
      ! lit->isEquality() ||
      ! lit->shared()) {
    return 0;
  }
  
  // the atom is an equality
  TermList* args = lit->args();
  if (args->isVar()) {
    return 0;
  }
  Term* l = args->term();
  args = args->next();
  if (args->isVar()) {
    return 0;
  }
  Term* r = args->term();
  HoDef* def = defines(l,r);
  if (def) {
    return def;
  }
  def = defines(r,l);
  if (def) {
    return def;
  }
  
  return 0;
}

HoFunctionDefinition::HoDef* 
HoFunctionDefinition::defines (Term* l, Term* r)
{
  CALL("HoFunctionDefinition::defines");
    
  if (env.signature->isFoolConstantSymbol(true, l->functor()) ||
      env.signature->isFoolConstantSymbol(true, r->functor()) ||
      env.signature->isFoolConstantSymbol(false, l->functor())||
      env.signature->isFoolConstantSymbol(false, r->functor())){
        return 0;
      }
    
  int functor = isEtaExpandedFunctionSymbol(l);
    
  if(functor == -1){
    return 0;
  } else {
    Stack<unsigned> rhsFunctors;
    if(isValidDefinens(r, functor, rhsFunctors)){
      HoDef* def = new HoDef(r, functor, rhsFunctors);
      return def;
    }    
  }
  return 0;
  
}

int HoFunctionDefinition::isEtaExpandedFunctionSymbol(Term* term)
{
  CALL("HoFunctionDefinition::isEtaExpandedFunctionSymbol"); 
  
  if(term->hasVarHead()){ return -1; }
  unsigned func = term->functor();
  Signature::Symbol* sym = env.signature->getFunction(func);
  while(sym->lambda()){
    TermList ts = *(term->nthArgument(0));
    if(ts.isVar()){ return -1; }
    term = ts.term();
    if(term->hasVarHead()){ return -1; }
    func = term->functor();
    sym = env.signature->getFunction(func);
  }
  
  if(sym->hoLogicalConn() || sym->duBruijnIndex() ||
     env.signature->isFoolConstantSymbol(true, func) ||
     env.signature->isFoolConstantSymbol(false, func)) {
    return -1;
  }
  
  
  //Does this iterator only return proper subterms or the term itself as well?
  SubtermIterator sti(term);
  while(sti.hasNext()){
    TermList ts = sti.next();
    if(ts.isVar()){ return -1; }
    term = ts.term();
    if(term->hasVarHead()){ return -1; }
    sym = env.signature->getFunction(term->functor());
    if(!sym->duBruijnIndex() && !sym->lambda()){ return -1; }    
  }
  
  return func;
  
}

bool HoFunctionDefinition::isValidDefinens(Term* r, unsigned functor, Stack<unsigned>& rhsFunctors)
{
  CALL("HoFunctionDefinition::isValidDefinens");
  
  Term* subterm;
  SubtermIterator sti(r);
  while(sti.hasNext()){
    TermList ts = sti.next();
    if(ts.isVar()){ return false; }
    subterm = ts.term();
    unsigned func = subterm->functor();
    //rhs contains lhs functor, not definition!
    if(func == functor){ 
      return false; 
    }else{
      Signature::Symbol* sym = env.signature->getFunction(func);
      if(!sym->duBruijnIndex() && !sym->lambda() && !sym->hoLogicalConn() && 
         !env.signature->isFoolConstantSymbol(true, func) &&
         !env.signature->isFoolConstantSymbol(false,func)){
        rhsFunctors.push(func);
      }
    }
  }
  
  return true;
}

}

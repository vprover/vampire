
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
       cout << "Have found a definition! " + cl->toString() << endl;
    }
  }
  ASSERTION_VIOLATION;
  return true;
}


/**
 * If the the clause if a function definition f(x1,...,xn) = t,
 * return the Def structure representing information about the definition.
 * @since 05/06/2004 Manchester
 * @since 26/05/2007 Manchester modified for new data structures
 */
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
  
  int functor = isEtaExpandedFunctionSymbol(l);
  
  if(functor == -1){
    return 0;
  }else{
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
  
  unsigned func = term->functor();
  Signature::Symbol* sym = env.signature->getFunction(func);
  while(sym->lambda()){
    TermList ts = *(term->nthArgument(0));
    if(ts.isVar()){ return -1; }
    term = ts.term();
    func = term->functor();
    sym = env.signature->getFunction(func);
  }
  
  if(sym->hoLogicalConn() || sym->duBruijnIndex()){
    return -1;
  }
  
  //Does this iterator only return proper subterms or the term itself as well?
  SubtermIterator sti(term);
  while(sti.hasNext()){
    TermList ts = sti.next();
    if(ts.isVar()){ return -1; }
    term = ts.term();
    sym = env.signature->getFunction(term->functor());
    if(!sym->duBruijnIndex()){ return -1; }    
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
      if(!sym->duBruijnIndex() && !sym->lambda() && !sym->hoLogicalConn()){
        rhsFunctors.push(func);
      }
    }
  }
  
  return true;
}

}

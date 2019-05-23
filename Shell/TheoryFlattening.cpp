
/*
 * File TheoryFlattening.cpp.
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
 * @file TheoryFlattening.cpp
 * Implements class TheoryFlattening.
 */

#include "TheoryFlattening.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

TheoryFlattening::TheoryFlattening(bool rec, bool share, bool grouping) : _recursive(rec), _sharing(share), _grouping(grouping) {
    //if(rec && share){
    //  USER_ERROR("Theory flattening which is recursive with sharing has not been tested");
    //}
}

void TheoryFlattening::apply(Problem& prb)
{
  CALL("TheoryFlattening::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}

/**
 * Perform theory flattening on clauses in @c units and return true if successful
 */
bool TheoryFlattening::apply(UnitList*& units)
{
  CALL("TheoryFlattening::apply(UnitList*&)");

  bool modified = false;

  UnitList* res=0;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    Clause* cln = apply(cl);
    if(cl!=cln){
      modified = true;
      uit.del();
      UnitList::push(cln, res);
    }
  }

  ASS_EQ(modified, UnitList::isNonEmpty(res));
  units=UnitList::concat(res, units);
  return modified;
}

/**
 * Perform theory flattening on clauses in @c clauses and return true if successful
 */
bool TheoryFlattening::apply(ClauseList*& clauses)
{
  CALL("TheoryFlattening::apply(UnitList*&)");

  bool modified = false;

  ClauseList* res=0;

  ClauseList::DelIterator cit(clauses);
  while(cit.hasNext()) {
    Clause* cl=cit.next();
    Clause* cln = apply(cl);
    if(cl!=cln){
      modified = true;
      cit.del();
      ClauseList::push(cln, res);
    }
  }
  ASS_EQ(modified, ClauseList::isNonEmpty(res));
  clauses=ClauseList::concat(res, clauses);
  return modified;
}


/**
 *
 * @author Giles
 */
  Clause* TheoryFlattening::apply(Clause*& cl,Stack<Literal*>& target)
{
  CALL("TheoryFlattening::apply");

  // Find the max variable. This will be used to introduce new variables. minVar is a lower bound to avoid overlaps wih other (sub-)ckauses
  unsigned maxVar = 0;
  VirtualIterator<unsigned> varIt = cl->getVariableIterator();
  while (varIt.hasNext()) {
    unsigned var = varIt.next();
    if (var > maxVar) {
      maxVar = var;
    }
  }

  // The resultant lits
  Stack<Literal*> result;

  // literals to be processed, start with those in clause
  Stack<Literal*> lits;
  for(int i= cl->length()-1; i>=0;i--){
    Literal* lit = (*cl)[i];
    if(target.isEmpty() || target.find(lit)){
      lits.push(lit);
    }
    else{ result.push(lit); }
  }

  if(!apply(lits,result,maxVar)){ return cl;}

  Clause* rep = Clause::fromStack(result,cl->inputType(),
                            new Inference1(Inference::THEORY_FLATTENING,cl)); 

  //cout << cl->toString() << " replaced by " << rep->toString() << endl;

  return rep;
}

/* Flatten literals in lits and put the flattened literals into result. Variables created during flattening will be larger than maxVar */
bool TheoryFlattening::apply(Stack<Literal*>& lits,Stack<Literal*>& result,unsigned maxVar)
{
  CALL("TheoryFlattening::apply");
  bool updated = false;
  DHMap<Term*,unsigned> abstracted;

  // process lits
  while(!lits.isEmpty()){
    Literal* lit = lits.pop();
    if(lit->arity()==0){
      result.push(lit);
      continue;
    }

    Stack<Literal*> newLits;
    Literal* nlit = replaceTopTerms(lit,newLits,maxVar,abstracted);
    if(nlit==lit){
      ASS(newLits.isEmpty());
      result.push(lit);
    }
    else{
      //cout << lit->toString() << " flattened to " << nlit->toString() << endl; 
      //for(unsigned i=0;i<newLits.length();i++){ cout << ">> " << newLits[i]->toString() << endl; }
      updated=true;
      if(_recursive){
        lits.push(nlit);
        lits.loadFromIterator(Stack<Literal*>::Iterator(newLits));
      }
      else{
        result.push(nlit);
        result.loadFromIterator(Stack<Literal*>::Iterator(newLits));
      }
    } 
  }
  return updated;
}

  
/**
 *
 * @author Giles
 */
 Literal* TheoryFlattening::replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar,
                                            DHMap<Term*,unsigned>& abstracted)
{
  CALL("TheoryFlattening::replaceTopTerms");
  //cout << "replaceTopTerms " << lit->toString() << endl;

  // Tells us if we're looking for interpreted are non-interpreted terms to flatten out
  bool interpreted = theory->isInterpretedPredicate(lit);
  bool equalityWithNumber = false;
  if(lit->isEquality()){
    interpreted=false;
    for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
      if(ts->isTerm() && env.signature->getFunction(ts->term()->functor())->interpreted()){
        interpreted=true;
      }
      if(ts->isTerm() && theory->isInterpretedConstant(ts->term())){
        equalityWithNumber = true;
      }
    }
  }
  //cout << "interpreted is " << interpreted << endl;

  bool updated = false;

  Stack<TermList> args;

  for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
    if(ts->isVar()){
      args.push(*ts);
      continue;
    }
    Term* t = ts->term();

    //cout << "term " << t->toString() << " has interp=" << env.signature->getFunction(t->functor())->interpreted() << endl;

    // if interpreted status is different factor out
    // but never factor out interpreted constants e.g. numbers
    // if grouping is false, always factor out
    if(
       ( !equalityWithNumber &&
         (interpreted != env.signature->getFunction(t->functor())->interpreted()) && 
         !theory->isInterpretedConstant(t) )
      ){
      //cout << "Factoring out " << t->toString() << endl;

      unsigned newVar;
      bool create = false;
      if(!(_sharing && abstracted.find(t,newVar))){
        newVar = ++maxVar;
        create=true;
      }
      args.push(TermList(newVar,false));
      if(create){
        unsigned sort = SortHelper::getResultSort(t);
        Literal* lit = Literal::createEquality(false,TermList(t),TermList(newVar,false),sort);
        newLits.push(lit);
        abstracted.insert(t,newVar);
      }
      updated=true;
    } 
    else{
      Term* tt = replaceTopTermsInTerm(t,newLits,maxVar,interpreted,abstracted);
      if(tt!=t){ updated=true; }
      //cout << "recurse in  " << tt->toString() << endl;
      args.push(TermList(tt));
    }
  }

  if(!updated){ return lit;}
  return Literal::create(lit,args.begin());
}

/**
 *
 * @author Giles
 */
 Term* TheoryFlattening::replaceTopTermsInTerm(Term* term, Stack<Literal*>& newLits,
                                               unsigned& maxVar,bool interpreted,
                                               DHMap<Term*,unsigned>& abstracted)
{
  CALL("TheoryFlattening::replaceTopTermsInTerm");
  //cout << "replaceTopTermsInTerm " << term->toString() << endl;


  Stack<TermList> args;
  bool updated=false;

  for(TermList* ts = term->args(); ts->isNonEmpty(); ts = ts->next()){
    if(ts->isVar()){
      args.push(*ts);
      continue;
    }
    Term* t = ts->term();

    bool interpretedStatus = env.signature->getFunction(t->functor())->interpreted(); 

    // do not abstract numbers out of uninterpreted things, no point
    if(!interpreted && interpretedStatus){
      interpretedStatus = !theory->isInterpretedNumber(t);
    }
  
    //special check
    if(interpretedStatus &&
       theory->isInterpretedPartialFunction(t->functor()) &&
       theory->isZero(*(t->nthArgument(1)))){

       // If we have something of the form /0 or %0 then we treat it as uninterpreted
         interpretedStatus=false; 
    }

    // if interpreted status is different factor out
    if( (interpreted != interpretedStatus) || !_grouping){ 
      //cout << "Factoring out " << t->toString() << endl;
      
      unsigned newVar;
      bool create = false; 
      if(!(_sharing && abstracted.find(t,newVar))){
        newVar = ++maxVar;
        create=true;
      }
      args.push(TermList(newVar,false));
      if(create){
        unsigned sort = SortHelper::getResultSort(t);
        Literal* lit = Literal::createEquality(false,TermList(t),TermList(newVar,false),sort);
        newLits.push(lit);
        abstracted.insert(t,newVar);
      }
      updated=true;
    }   
    else{
      Term* tt = replaceTopTermsInTerm(t,newLits,maxVar,interpreted,abstracted);
      if(tt!=t){ updated=true; }
      args.push(TermList(tt));
    }
  }

  //cout << "updated is " << updated << endl;

  if(!updated) return term;
  else return Term::create(term->functor(),term->arity(),args.begin());
}


}

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
Clause* TheoryFlattening::apply(Clause*& cl)
{
  CALL("TheoryFlattening::apply");

  // Find the max variable. This will be used to introduce new variables.
  unsigned maxVar = 0;
  VirtualIterator<unsigned> varIt = cl->getVariableIterator();
  while (varIt.hasNext()) {
    unsigned var = varIt.next();
    if (var > maxVar) {
      maxVar = var;
    }
  }

  // literals to be processed, start with those in clause
  Stack<Literal*> lits;
  for(int i= cl->length()-1; i>=0;i--){
    lits.push((*cl)[i]);
  }

  // The resultant lits
  Stack<Literal*> result;
  bool updated = false;

  // process lits
  while(!lits.isEmpty()){
    Literal* lit = lits.pop();
    if(lit->arity()==0){
      result.push(lit);
    }
    Stack<Literal*> newLits;
    Literal* nlit = replaceTopTerms(lit,newLits,maxVar);
    if(newLits.isEmpty()){
      result.push(lit);
    }
    else{
      //cout << lit->toString() << " flattened to " << nlit->toString() << endl; 
      //for(unsigned i=0;i<newLits.length();i++){ cout << newLits[i]->toString() << endl; }
      updated=true;
      lits.push(nlit);
      lits.loadFromIterator(Stack<Literal*>::Iterator(newLits));
    } 
  }
  if(!updated){ return cl;}

  Clause* rep = Clause::fromStack(result,cl->inputType(),
                            new Inference1(Inference::THEORY_FLATTENING,cl)); 

  //cout << cl->toString() << " replaced by " << rep->toString() << endl;

  return rep;
}

/**
 *
 * @author Giles
 */
 Literal* TheoryFlattening::replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar)
{
  CALL("TheoryFlattening::replaceTopTerms");
  //cout << "replaceTopTerms " << lit->toString() << endl;

  // Tells us if we're looking for interpreted are non-interpreted terms to flatten out
  bool interpreted = theory->isInterpretedPredicate(lit);
  if(lit->isEquality()){
    interpreted=false;
    for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
      if(ts->isTerm() && env.signature->getFunction(ts->term()->functor())->interpreted()){
        interpreted=true;
      }
    }
  }
  //cout << "interpreted is " << interpreted << endl;

  Stack<TermList> args;

  for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
    if(ts->isVar()){
      args.push(*ts);
      continue;
    }
    Term* t = ts->term();

    // if interpreted status is different factor out
    if(interpreted != env.signature->getFunction(t->functor())->interpreted()){
      //cout << "Factoring out " << t->toString() << endl;
      unsigned newVar = ++maxVar;
      args.push(TermList(newVar,false));
      unsigned sort = SortHelper::getResultSort(t);
      newLits.push(Literal::createEquality(false,TermList(t),TermList(newVar,false),sort));
    } 
    else{
      Term* tt = replaceTopTermsInTerm(t,newLits,maxVar,interpreted);
      //cout << "ret " << tt->toString() << endl;
      args.push(TermList(tt));
    }
  }

  if(newLits.isEmpty()) return lit;
  else return Literal::create(lit,args.begin());
}

/**
 *
 * @author Giles
 */
 Term* TheoryFlattening::replaceTopTermsInTerm(Term* term, Stack<Literal*>& newLits,
                                               unsigned& maxVar,bool interpreted)
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

    // if interpreted status is different factor out
    if(interpreted != env.signature->getFunction(t->functor())->interpreted()){
      //cout << "Factoring out " << t->toString() << endl;
      unsigned newVar = ++maxVar;
      args.push(TermList(newVar,false));
      unsigned sort = SortHelper::getResultSort(t);
      newLits.push(Literal::createEquality(false,TermList(t),TermList(newVar,false),sort));
      updated=true;
    }   
    else{
      Term* tt = replaceTopTermsInTerm(t,newLits,maxVar,interpreted);
      if(tt!=t){ updated=true; }
      args.push(TermList(tt));
    }
  }

  //cout << "updated is " << updated << endl;

  if(!updated) return term;
  else return Term::create(term->functor(),term->arity(),args.begin());
}


}

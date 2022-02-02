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
 * @file ClauseFlattening.cpp
 * Implementing clause flattening for the Finite Model Builder
 */

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Inference.hpp"

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Array.hpp"
#include "Lib/VirtualIterator.hpp"

#include "ClauseFlattening.hpp"

namespace FMB{

bool ClauseFlattening::isShallow(Literal* lit)
{
  CALL("ClauseFlattening::isShallow(Literal)");
  // The term to check for variable arguments
  Term* check = 0;

  if(lit->isEquality()){
   // equalities between vars are shallow if positive
   if(lit->isTwoVarEquality()) return lit->polarity()==1;

   // the only other shallow equalities are between a variable and a function with variable arguments
   if(lit->nthArgument(0)->isVar()){
     check = lit->nthArgument(1)->term();
   }
   else if(lit->nthArgument(1)->isVar()){
     check = lit->nthArgument(0)->term();
   }
   else return false;
  }
  // non-equality predicates should have variable arguments
  else check = lit;

  TermList* a = check->args();
  while(!a->isEmpty()){ 
    if(!a->isVar()) return false; 
    a = a->next();
  }
  return true;
}

/**
 * Apply equality resolution to all negative equalities between variables
 * in cl and return the result. If cl contains no such inequalities, return cl
 * itself.
 */
Clause* ClauseFlattening::resolveNegativeVariableEqualities(Clause* cl)
{
  CALL("ClauseFlattening::resolveNegativeVariableEqualities");

  Array<Literal*> lits;
  Stack<Literal*> inequalities;
  int n = 0;
  for (unsigned i = 0;i < cl->length();i++) {
    Literal* lit = (*cl)[i];
    if (lit->isEquality() &&
        lit->isNegative() &&
        lit->nthArgument(0)->isVar() &&
        lit->nthArgument(1)->isVar()) {
      inequalities.push(lit);
    }
    else {
      lits[n++] = lit;
    }
  }
  if (inequalities.isEmpty()) {
    return cl;
  }
  bool diffVar = false;
  while (!inequalities.isEmpty()) {
    Literal* ineq = inequalities.pop();
    unsigned v1 = ineq->nthArgument(0)->var();
    TermList* v2 = ineq->nthArgument(1);
    if (v1 == v2->var()) { // x != x
      continue;
    }
    diffVar = true;
    Substitution subst;
    subst.bind(v1,*v2);
    cl = new(n) Clause(n,NonspecificInference1(InferenceRule::EQUALITY_RESOLUTION,cl));
    for (int i = n-1;i >= 0;i--) {
      Literal* lit = SubstHelper::apply<Substitution>(lits[i],subst);
      (*cl)[i] = lit;
      lits[i] = lit;
    }
  }
  if (!diffVar) { // only X != X found, we should still perform the inference
    cl = new(n) Clause(n,NonspecificInference1(InferenceRule::EQUALITY_RESOLUTION,cl));
    for (int i = n-1;i >= 0;i--) {
      (*cl)[i] = lits[i];
    }
  }
  return cl;
} // ClauseFlattening::resolveNegativeVariableEqualities

/**
 * Flatten clauses
 *
 * @author Giles
 */
Clause* ClauseFlattening::flatten(Clause* cl)
{
  CALL("ClauseFlattening::flatten");
  TimeCounter tc(TC_FMB_FLATTENING);

  cl = resolveNegativeVariableEqualities(cl);

  // new, find the maximal variable number
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

  //TODO reuse variables
  // maps for reuse of renamings
  //Map<Term*,Literal*> _literalMap;
  //Map<Term*,unsigned> _variableMap;

  // The resultant args
  Stack<Literal*> result;

  //If already flat updated will be false
  bool updated=false;

  // process lits
  while(!lits.isEmpty()){
    Literal* lit = lits.pop();
    //cout << "Flattening " << lit->toString() << endl;
    // Could combine check and flattening
    if(isShallow(lit)){
      if(!result.find(lit)){
        result.push(lit);
      }
    }
    else{
      updated=true;
      if(lit->isEquality()){
        // it is a non-flattened equality

        TermList litArgSort = SortHelper::getEqualityArgumentSort(lit);

        TermList* lhs = lit->nthArgument(0);
        TermList* rhs = lit->nthArgument(1);

        //ensure var is on left if there is a var, cannot both be var
        if(rhs->isVar()){ TermList* tmp = lhs; lhs=rhs; rhs=tmp; }
        ASS(!rhs->isVar());

        if(!lhs->isVar()){
          // both non-var
          if(lit->polarity()){
            // introduce lhs!=x | rhs!=y | x=y 
            TermList v1; v1.makeVar(++maxVar);
            TermList v2; v2.makeVar(++maxVar);
            lits.push(Literal::createEquality(false,*lhs,v1,litArgSort));
            lits.push(Literal::createEquality(false,*rhs,v2,litArgSort));
            lits.push(Literal::createEquality(true,v1,v2,litArgSort));
            continue;
          }
          else{
            // introduce lhs!=x | rhs!=x
            // should be lhs=x | rhs=y | x!=y, but don't want to add x!=y
            TermList v; v.makeVar(++maxVar);
            lits.push(Literal::createEquality(false,*lhs,v,litArgSort));
            lits.push(Literal::createEquality(false,*rhs,v,litArgSort));
            continue;
          }
        }
        ASS(lhs->isVar());
        // Now lhs is a var and rhs is not
        Term* t = rhs->term();
        // Let's flatten rhs
        Stack<TermList> args;
        for(TermList* ts = t->args(); ts->isNonEmpty(); ts = ts->next()){
          if(ts->isVar()){
            args.push(*ts);
          }
          else{
            TermList v; v.makeVar(++maxVar);
            args.push(v);
            TermList rSort = SortHelper::getResultSort(ts->term());
            lits.push(Literal::createEquality(false,*ts,v,rSort));
          }
        }
        // construct the function for t
        Term* nt = Term::create(t->functor(),args.length(),args.begin());
        // add the resulting equality, which will be flat
        lits.push(Literal::createEquality(lit->polarity(),*lhs,TermList(nt),litArgSort)); 
      }

      else{ // not equality
        // not shallow predicate, so there are non-variable arguments
        // this should be lifted
        Stack<TermList> args;
        for(TermList* ts = lit->args();ts->isNonEmpty(); ts = ts->next()){
          if(ts->isVar()){
            args.push(*ts);
          }
          else{
            TermList v; v.makeVar(++maxVar);
            args.push(v);
            TermList rSort = SortHelper::getResultSort(ts->term());
            lits.push(Literal::createEquality(false,*ts,v,rSort));
          }
        }
        // add the resulting equality 
        lits.push(Literal::create(lit,args.begin()));
      }
    
    }
  }

  // If no new literals were added just return cl
  if(!updated) return cl;

  return Clause::fromStack(result,NonspecificInference1(InferenceRule::FMB_FLATTENING,cl));
}

}

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

  // a helper class to be passed to SubstHelper
  class SingleVar2VarSubst {
    unsigned _from;
    unsigned _to;
  public:
    void bind(unsigned from,unsigned to) {
      _from = from;
      _to = to;
    }
    bool isId() {
      return (_from == _to);
    }
    TermList apply(unsigned var) {
      if (var == _from) {
        return TermList(_to, false);
      } else {
        return TermList(var, false);
      }
    }
  } subst;

  // cout << "Begin: " << cl->toString() << endl;

  unsigned n = cl->length();
  unsigned idx = 0;
  while (true) {
    // scan cl from where we ended last time and look for a new negative two variable equality
    while(idx < n) {
      Literal* lit = (*cl)[idx];
      if (lit->isEquality() && lit->isNegative() && lit->nthArgument(0)->isVar() && lit->nthArgument(1)->isVar()) {
        subst.bind(lit->nthArgument(0)->var(),lit->nthArgument(1)->var());
        break;
      }
      idx++;
    }
    if (idx < n) { // we found one
      // new clause one lit shorter
      Clause* newcl = new(n-1) Clause(n-1,NonspecificInference1(InferenceRule::EQUALITY_RESOLUTION,cl));
      unsigned j = 0; // for writing into newcl
      for (unsigned i = 0; i < n; i++) {
        if (i != idx) { // skipping literal found at idx
          (*newcl)[j++] = subst.isId() ? (*cl)[i] : SubstHelper::apply((*cl)[i],subst);
        }
      }
      cl = newcl;
      n--;
      // cout << "Update: " << cl->toString() << endl;
    } else {
      // cout << "Done: " << cl->toString() << endl;
      return cl;
    }
  }
} // ClauseFlattening::resolveNegativeVariableEqualities

/**
 * Flatten clauses
 *
 * @author Giles
 */
Clause* ClauseFlattening::flatten(Clause* cl)
{
  CALL("ClauseFlattening::flatten");
  TIME_TRACE("fmb flattening");

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

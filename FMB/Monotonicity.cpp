/**
 * @file Monotonicity.cpp
 * Implements class Monotonicity.
 *
 */

#include "Forwards.hpp"

#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "SAT/SATSolver.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/MinisatInterfacing.hpp"

#include "Monotonicity.hpp"

namespace FMB
{

Monotonicity::Monotonicity(ClauseList* clauses, unsigned srt) : _srt(srt)
{
 CALL("Monotonicity::Monotonicity");

  _solver = new MinisatInterfacing(*env.options,true);

 // create pt and pf per predicate and add the constraint -pf | -pt
 for(unsigned p=1;p<env.signature->predicates();p++){
   _pT.insert(p,SATLiteral(_solver->newVar(),true));
   _pF.insert(p,SATLiteral(_solver->newVar(),true));

   Stack<SATLiteral> slits;
   slits.push(_pT.get(p).opposite()); 
   slits.push(_pF.get(p).opposite()); 
   _solver->addClause(SATClause::fromStack(slits));
 }

 ClauseIterator cit = pvi(ClauseList::Iterator(clauses));
 while(cit.hasNext()){
   Clause* c = cit.next();
   Clause::Iterator lit(*c);
   while(lit.hasNext()){
     Literal* l = lit.next();
     monotone(c,l);
   }
 }

 SATSolver::Status status = _solver->solve();
 ASS(status!=SATSolver::Status::UNKNOWN);
 _result = (status == SATSolver::Status::SATISFIABLE);
}


void Monotonicity::monotone(Clause* c, Literal* l)
{
  CALL("Monotonicity::monotone");

  // if we have equality
  if(l->isEquality()){
    TermList* t1 = l->nthArgument(0); 
    TermList* t2 = l->nthArgument(1); 
    // t1 = t2
    if(l->polarity()){
      // add a clause for each
      safe(c,l,t1);
      safe(c,l,t2);
    }
    // t1 != t2
    else{
      // the true clause, skip
    }
  }
  else{
  // not equality
    unsigned p = l->functor();
    SATLiteral add = (l->polarity() ? _pF.get(p) : _pT.get(p)).opposite();
    for(unsigned i=0;i<l->arity();i++){
      TermList* t = l->nthArgument(i);
      safe(c,l,t,add);
    }
  }
}

void Monotonicity::safe(Clause* c, Literal* parent, TermList* t){
  Stack<SATLiteral> slits;
  safe(c,parent,t,slits);
}
void Monotonicity::safe(Clause* c, Literal* parent, TermList* t,SATLiteral add){
  Stack<SATLiteral> slits;
  slits.push(add);
  safe(c,parent,t,slits);
}

void Monotonicity::safe(Clause* c, Literal* parent, TermList* t,Stack<SATLiteral>& slits)
{
  CALL("Monotonicity::safe");
  if(t->isVar()){
    unsigned var = t->var();
    unsigned s = SortHelper::getVariableSort(*t,parent);
    if(s==_srt){
      Clause::Iterator lit(*c);
      while(lit.hasNext()){
        Literal* l = lit.next(); 
        if(guards(l,var,slits)){
          // if guards returns true it means true will be added to the clause
          // so don't bother creating it
          return;
        } 
      } 
      _solver->addClause(SATClause::fromStack(slits));
    }
  }
  // otherwise true clause, so ignore
}

bool Monotonicity::guards(Literal* l, unsigned var, Stack<SATLiteral>& slits)
{
  CALL("Monotonicyt::guards");

  if(l->isEquality()){
    // check for X != f(...) or f(...) != X
    // i.e. a negative equality with X on one side
    if(!l->polarity()){
      TermList* t1 = l->nthArgument(0);
      TermList* t2 = l->nthArgument(1);
      if(t1->isVar() && t1->var()==var) return true; 
      if(t2->isVar() && t2->var()==var) return true; 
    }
  }
  else{
    // check if l contains X 
    unsigned p = l->functor();
    for(unsigned i=0;i<l->arity();i++){
      TermList* t = l->nthArgument(i);
      if(t->isVar() && t->var()==var){
        SATLiteral slit = l->polarity() ? _pT.get(p) : _pF.get(p);
        slits.push(slit);
        return false; // not the true literal
      }
    }
  }
  return false; // not the true literal
}

}

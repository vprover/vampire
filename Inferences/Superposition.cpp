/**
 * @file Superposition.cpp
 * Implements class Superposition.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/PairUtils.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Shell/Statistics.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Ordering.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Indexing/TermSharing.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "Superposition.hpp"

#include <iostream>

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void Superposition::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SuperpositionSubtermIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<SuperpositionLHSIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_LHS_SUBST_TREE) );
}

void Superposition::detach()
{
  CALL("Superposition::detach");

  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(SUPERPOSITION_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}


struct Superposition::LHSsFn
{
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, Superposition::getLHSIterator(lit)) );
  }
};

struct Superposition::RewritableResultsFn
{
  RewritableResultsFn(SuperpositionSubtermIndex* index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
  }
private:
  SuperpositionSubtermIndex* _index;
};

struct Superposition::RewriteableSubtermsFn
{
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, Superposition::getRewritableSubtermIterator(lit)) );
  }
};

struct Superposition::ApplicableRewritesFn
{
  ApplicableRewritesFn(SuperpositionLHSIndex* index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
  }
private:
  SuperpositionLHSIndex* _index;
};


struct Superposition::ForwardResultFn
{
  ForwardResultFn(Clause* cl) : _cl(cl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return performSuperposition(_cl, arg.first.first, arg.first.second, QRS_QUERY_BANK,
	    qr.clause, qr.literal, qr.term, QRS_RESULT_BANK, qr.substitution);
  }
private:
  TermList getRHS(Literal* eq, TermList lhs)
  {
    ASS(eq->isEquality());
    ASS(eq->isPositive());
    if(*eq->nthArgument(0)==lhs) {
      return *eq->nthArgument(1);
    } else {
      ASS(*eq->nthArgument(1)==lhs);
      return *eq->nthArgument(0);
    }
  }

  Clause* _cl;
};


struct Superposition::BackwardResultFn
{
  BackwardResultFn(Clause* cl) : _cl(cl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return performSuperposition(qr.clause, qr.literal, qr.term, QRS_RESULT_BANK,
	    _cl, arg.first.first, arg.first.second, QRS_QUERY_BANK, qr.substitution);
  }
private:
  Clause* _cl;
};


ClauseIterator Superposition::generateClauses(Clause* premise)
{
  CALL("Superposition::generateClauses");

  return pvi( getFilteredIterator<NonzeroPredicate>(
	getConcatenatedIterator(
	  getMappingIterator(
		  getFlattenedIterator(getMappingIterator(
			  getFlattenedIterator(getMappingIterator(
				  premise->getSelectedLiteralIterator(),
				  RewriteableSubtermsFn())),
			  ApplicableRewritesFn(_lhsIndex))),
		  ForwardResultFn(premise)),
	  getMappingIterator(
		  getFlattenedIterator(getMappingIterator(
			  getFlattenedIterator(getMappingIterator(
				  premise->getSelectedLiteralIterator(),
				  LHSsFn())),
			  RewritableResultsFn(_subtermIndex))),
		  BackwardResultFn(premise)))) );
}

/**
 * If superposition should be performed, return result of the superposition,
 * otherwise return 0.
 */
Clause* Superposition::performSuperposition(
	Clause* rwClause, Literal* rwLit, TermList rwTerm, int rwIndex,
	Clause* eqClause, Literal* eqLit, TermList eqLHS, int eqIndex,
	MMSubstitution* subst)
{
  CALL("Superposition::performSuperposition");

  static Ordering* ordering=0;
  if(!ordering) {
    ordering=Ordering::instance();
  }

  Literal* rwLitS = subst->apply(rwLit, rwIndex);
  TermList rwTermS = subst->apply(rwTerm, rwIndex);
  TermList eqLHSS = subst->apply(eqLHS, eqIndex);
  TermList tgtTerm = getRHS(eqLit, eqLHS);
  TermList tgtTermS = subst->apply(tgtTerm, eqIndex);

  //check that we're not rewriting smaller subterm with larger
  if(ordering->compare(tgtTermS,eqLHSS)==Ordering::GREATER) {
    return 0;
  }
  Literal* tgtLitS = replace(rwLitS,rwTermS,tgtTermS);
  if(tgtLitS->isEquality()) {
    //check that we're not rewriting only the smaller side of an equality
    TermList arg0=*tgtLitS->nthArgument(0);
    TermList arg1=*tgtLitS->nthArgument(1);
    if(!arg0.containsSubterm(tgtTermS)) {
      if(ordering->compare(arg0,arg1)==Ordering::GREATER) {
	return 0;
      }
    } else if(!arg1.containsSubterm(tgtTermS)) {
      if(ordering->compare(arg1,arg0)==Ordering::GREATER) {
	return 0;
      }
    }
  }

  int rwLength = rwClause->length();
  int eqLength = eqClause->length();
  int newLength = rwLength+eqLength-1;

  Inference* inf = new Inference2(Inference::SUPERPOSITION, rwClause, eqClause);
  Unit::InputType inpType = (Unit::InputType)
  	Int::max(rwClause->inputType(), eqClause->inputType());

  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  (*res)[0] = tgtLitS;
  int next = 1;
  for(int i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit) {
	(*res)[next++] = subst->apply(curr, rwIndex);
    }
  }
  for(int i=0;i<eqLength;i++) {
    Literal* curr=(*eqClause)[i];
    if(curr!=eqLit) {
	(*res)[next++] = subst->apply(curr, eqIndex);
    }
  }

  res->setAge(Int::max(rwClause->age(),eqClause->age())+1);
  if(rwIndex==QRS_QUERY_BANK) {
    env.statistics->forwardSuperposition++;
  } else {
    env.statistics->backwardSuperposition++;
  }

  return res;
}

TermList Superposition::getRHS(Literal* eq, TermList lhs)
{
  ASS(eq->isEquality());
  ASS(eq->isPositive());
  if(*eq->nthArgument(0)==lhs) {
    return *eq->nthArgument(1);
  } else {
    ASS(*eq->nthArgument(1)==lhs);
    return *eq->nthArgument(0);
  }
}

Literal* Superposition::replace(Literal* lit, TermList tSrc, TermList tDest)
{
  CALL("Superposition::replace");
  ASS(lit->shared());

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

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      if(!modified.pop()) {
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
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    if(tl==tSrc) {
      args.push(tDest);
      modified.setTop(true);
      continue;
    }
    if(tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  if(!modified.pop()) {
    //we call replace in superposition only if we already know,
    //there is something to be replaced.
    ASSERTION_VIOLATION;
    return lit;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);
  return Literal::create(lit,argLst);
}

TermIterator Superposition::getRewritableSubtermIterator(Literal* lit)
{
  CALL("Superposition::getRewritableSubtermIterator");

  if(lit->isEquality()) {
    if(lit->isNegative()) {
      return TermIterator::getEmpty();
    }
    TermList sel;
    switch(lit->getArgumentOrder())
    {
    case Term::INCOMPARABLE:
    {
      Term::NonVariableIterator nvi(lit);
      return getUniquePersistentIteratorFromPtr(&nvi);
    }
    case Term::EQUAL:
    case Term::GREATER:
      sel=*lit->nthArgument(0);
      break;
    case Term::LESS:
      sel=*lit->nthArgument(1);
#if VDEBUG
      break;
    default:
      ASSERTION_VIOLATION;
#endif
    }
    if(!sel.isTerm()) {
      return TermIterator::getEmpty();
    }
    return getUniquePersistentIterator(
	    getConcatenatedIterator(getSingletonIterator(sel),
	    vi( new Term::NonVariableIterator(sel.term()) )) );
  } else {
    Term::NonVariableIterator nvi(lit);
    return getUniquePersistentIteratorFromPtr(&nvi);
  }
}

TermIterator Superposition::getLHSIterator(Literal* lit)
{
  CALL("Superposition::getLHSIterator");

  if(lit->isEquality()) {
    if(lit->isNegative()) {
      return TermIterator::getEmpty();
    }
    TermList t0=*lit->nthArgument(0);
    TermList t1=*lit->nthArgument(1);
    switch(lit->getArgumentOrder())
    {
    case Term::INCOMPARABLE:
      return pvi( getConcatenatedIterator(getSingletonIterator(t0),
	      getSingletonIterator(t1)) );
    case Term::GREATER:
      return pvi( getSingletonIterator(t0) );
    case Term::LESS:
      return pvi( getSingletonIterator(t1) );
#if VDEBUG
    case Term::EQUAL:
      //there should be no equality literals of equal terms
    default:
      ASSERTION_VIOLATION;
#endif
    }
    return TermIterator::getEmpty();
  } else {
    return TermIterator::getEmpty();
  }
}


}

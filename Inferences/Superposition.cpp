/**
 * @file Superposition.cpp
 * Implements class Superposition.
 */

#include "Superposition.hpp"

/**
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution.
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

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Indexing/TermSharing.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "BinaryResolution.hpp"

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
  ApplicableRewritesFn(SuperpositionLHSIndex* index)
  : _index(index) {}
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
    Literal* rwLit = arg.first.first;
    TermList rwTerm=arg.first.second;
    Literal* rwLitS = qr.substitution->apply(rwLit, QRS_QUERY_BANK);
    TermList rwTermS = qr.substitution->apply(rwTerm, QRS_QUERY_BANK);
    TermList tgtTermS = qr.substitution->apply(qr.term, QRS_RESULT_BANK);
    Literal* tgtLitS = replace(rwLitS,rwTermS,tgtTermS);

    int clength = _cl->length();
    int dlength = qr.clause->length();
    int newLength = clength+dlength-1;

    Inference* inf = new Inference2(Inference::SUPERPOSITION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType)
    	Int::max(_cl->inputType(), qr.clause->inputType());

    Clause* res = new(newLength) Clause(newLength, inpType, inf);

    (*res)[0] = tgtLitS;
    int next = 1;
    for(int i=0;i<clength;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=rwLit) {
	(*res)[next++] = qr.substitution->apply(curr, QRS_QUERY_BANK);
      }
    }
    for(int i=0;i<dlength;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
	(*res)[next++] = qr.substitution->apply(curr, QRS_RESULT_BANK);
      }
    }

    res->setAge(Int::max(_cl->age(),qr.clause->age())+1);
    env.statistics->forwardSuperposition++;

    return res;
  }
private:
  Clause* _cl;
};


ClauseIterator Superposition::generateClauses(Clause* premise)
{
  CALL("Superposition::generateClauses");

  return pvi( getMappingIterator(
	  getFlattenedIterator(getMappingIterator(
		  getFlattenedIterator(getMappingIterator(
			  premise->getSelectedLiteralIterator(),
			  RewriteableSubtermsFn())),
		  ApplicableRewritesFn(_lhsIndex))),
	  ForwardResultFn(premise)) );
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
      return vi( new Term::NonVariableIterator(lit));
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
    return pvi( getConcatenatedIterator(getSingletonIterator(sel),
	    vi( new Term::NonVariableIterator(sel.term()) )) );
  } else {
    return vi( new Term::NonVariableIterator(lit));
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
      if(t0.isVar()) {
	if(t1.isVar()) {
	  break;
	}
	return pvi( getSingletonIterator(t1) );
      }
      if(t1.isVar()) {
	return pvi( getSingletonIterator(t0) );
      }
      return pvi( getConcatenatedIterator(getSingletonIterator(t0),
	      getSingletonIterator(t1)) );
    case Term::GREATER:
      ASS(t0.isTerm());
      return pvi( getSingletonIterator(t0) );
    case Term::LESS:
      ASS(t1.isTerm());
      return pvi( getSingletonIterator(t1) );
    case Term::EQUAL:
#if VDEBUG
      break;
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

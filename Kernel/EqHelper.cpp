
/*
 * File EqHelper.cpp.
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
 * @file EqHelper.cpp
 * Implements class EqHelper.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"

#include "Ordering.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"

#include "EqHelper.hpp"

namespace Kernel {

using namespace Shell;

/**
 * Return the other side of an equality @b eq than the @b lhs
 */
TermList EqHelper::getOtherEqualitySide(Literal* eq, TermList lhs)
{
  CALL("EqHelper::getOtherEqualitySide");
  ASS(eq->isEquality());

  if (*eq->nthArgument(0) == lhs) {
    return *eq->nthArgument(1);
  }
  ASS(*eq->nthArgument(1) == lhs);
  return *eq->nthArgument(0);
} // getOtherEqualitySide

bool EqHelper::hasGreaterEqualitySide(Literal* eq, const Ordering& ord, TermList& lhs, TermList& rhs)
{
  CALL("EqHelper::hasGreaterEqualitySide");
  ASS(eq->isEquality());

  switch(ord.getEqualityArgumentOrder(eq)) {
    case Ordering::INCOMPARABLE:
      return false;
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      lhs = *eq->nthArgument(0);
      rhs = *eq->nthArgument(1);
      return true;
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      lhs = *eq->nthArgument(1);
      rhs = *eq->nthArgument(0);
      return true;
#if VDEBUG
    case Ordering::EQUAL:
      //there should be no equality literals of equal terms
    default:
      ASSERTION_VIOLATION;
#endif
  }
}

Literal* EqHelper::replace(Literal* lit, TermList what, TermList by)
{
  CALL("EqHelper::replace(Literal*,...)");

  return static_cast<Literal*>(replace(static_cast<Term*>(lit), what, by));
}

/**
 * Replace all occurences of the subterm  @b tSrc by @b tDest in the term/literal
 * @b lit, and return the result
 */
Term* EqHelper::replace(Term* trm0, TermList tSrc, TermList tDest)
{
  CALL("EqHelper::replace(Term*,...)");
  ASS(trm0->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(trm0->args());

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
    if (tl == tSrc) {
      args.push(tDest);
      modified.setTop(true);
      continue;
    }
    if (tl.isVar()) {
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
  ASS_EQ(args.length(),trm0->arity());

  if (!modified.pop()) {
    // we call replace in superposition only if we already know,
    // there is something to be replaced.
    // ASSERTION_VIOLATION; // MS: but there is now a new use in InnerRewriting which does not like this extra check
    return trm0;
  }

  // here we assume, that stack is an array with
  // second topmost element as &top()-1, third at
  // &top()-2, etc...
  TermList* argLst=&args.top() - (trm0->arity()-1);
  if (trm0->isLiteral()) {
    Literal* lit = static_cast<Literal*>(trm0);
    ASS_EQ(args.size(), lit->arity());
    return Literal::create(lit,argLst);
  }
  return Term::create(trm0,argLst);
}

// for the term algebra rules to be complete, superposition is relaxed
// and rewriting allowed in the small side of an equation if the head
// of the larger term is a term algebra constructor
bool EqHelper::smallSideRewritingAllowed(Literal *lit)
{
  CALL("EqHelper::smallSideRewritingAllowed");
  ASS(lit->isEquality());
  
  static bool taCalculus = (env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE
                            || env.options->termAlgebraInferences() == Options::TAInferences::FULL);

  if (taCalculus && lit->isPositive()) {
    TermList *s = lit->nthArgument(0);
    TermList *t = lit->nthArgument(0);
    return ((s->isTerm() && env.signature->getFunction(s->term()->functor())->termAlgebraCons())
            || (t->isTerm() && env.signature->getFunction(t->term()->functor())->termAlgebraCons()));
  }
  return false;
}

/**
 * Return iterator on subterms of a literal, that can be rewritten by
 * superposition.
 */
TermIterator EqHelper::getRewritableSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getRewritableSubtermIterator");

//  if (lit->isEquality()) {
//    if (lit->isNegative()) {
//      return TermIterator::getEmpty();
//    }

// Remove positive check as per commit 517ad0a24cdbbff0fbf488d00f022bdd117c6510
//  if (lit->isEquality() && lit->isPositive()) {
  if (lit->isEquality()) {
    if (smallSideRewritingAllowed(lit)) {
      NonVariableIterator nvi(lit);
      return getUniquePersistentIteratorFromPtr(&nvi);
    }
    TermList sel;
    switch(ord.getEqualityArgumentOrder(lit)) {
    case Ordering::INCOMPARABLE:
      {
	NonVariableIterator nvi(lit);
	return getUniquePersistentIteratorFromPtr(&nvi);
      }
    case Ordering::EQUAL:
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      sel=*lit->nthArgument(0);
      break;
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      sel=*lit->nthArgument(1);
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
    if (!sel.isTerm()) {
      return TermIterator::getEmpty();
    }
    return getUniquePersistentIterator(getConcatenatedIterator(getSingletonIterator(sel),
							       vi(new NonVariableIterator(sel.term()))));
  }

  NonVariableIterator nvi(lit);
  return getUniquePersistentIteratorFromPtr(&nvi);
}

/**
 * Return iterator on sides of the equality @b lit that can be used as an LHS
 * for a rewriting inference (i.e. the other side of the equality is not greater)
 *
 * If the literal @b lit is not a positive equality, empty iterator is returned.
 */
TermIterator EqHelper::getLHSIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getLHSIterator");

  if (lit->isEquality()) {
    if (lit->isNegative()) {
      return TermIterator::getEmpty();
    }
    TermList t0=*lit->nthArgument(0);
    TermList t1=*lit->nthArgument(1);
    switch(ord.getEqualityArgumentOrder(lit))
    {
    case Ordering::INCOMPARABLE:
      return pvi( getConcatenatedIterator(getSingletonIterator(t0),
	      getSingletonIterator(t1)) );
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      return pvi( getSingletonIterator(t0) );
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      return pvi( getSingletonIterator(t1) );
#if VDEBUG
    case Ordering::EQUAL:
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

/**
 * A functor that returns true iff its argument is a non-variable term
 */
struct EqHelper::IsNonVariable
{
  DECL_RETURN_TYPE(bool);
  bool operator()(TermList t)
  { return t.isTerm(); }
};

/**
 * Return iterator on sides of the equality @b lit that can be used as an LHS
 * for superposition
 *
 * If the literal @b lit is not a positive equality, empty iterator is returned.
 */
TermIterator EqHelper::getSuperpositionLHSIterator(Literal* lit, const Ordering& ord, const Options& opt)
{
  CALL("EqHelper::getSuperpositionLHSIterator");

  if (opt.superpositionFromVariables()) {
    return getLHSIterator(lit, ord);
  }
  else {
    return pvi( getFilteredIterator(getLHSIterator(lit, ord), IsNonVariable()) );
  }
}

/**
 * Return iterator on sides of the equality @b lit that can be used as an LHS
 * for demodulation
 *
 * If the literal @b lit is not a positive equality, empty iterator is returned.
 */
TermIterator EqHelper::getDemodulationLHSIterator(Literal* lit, bool forward, const Ordering& ord, const Options& opt)
{
  CALL("EqHelper::getDemodulationLHSIterator");

  if (lit->isEquality()) {
    if (lit->isNegative()) {
      return TermIterator::getEmpty();
    }
    TermList t0=*lit->nthArgument(0);
    TermList t1=*lit->nthArgument(1);
    switch(ord.getEqualityArgumentOrder(lit))
    {
    case Ordering::INCOMPARABLE:
      if ( forward ? (opt.forwardDemodulation() == Options::Demodulation::PREORDERED)
		  : (opt.backwardDemodulation() == Options::Demodulation::PREORDERED) ) {
	return TermIterator::getEmpty();
      }
      if (t0.containsAllVariablesOf(t1)) {
	if (t1.containsAllVariablesOf(t0)) {
	  return pvi( getConcatenatedIterator(getSingletonIterator(t0),
	      getSingletonIterator(t1)) );
	}
	return pvi( getSingletonIterator(t0) );
      }
      if (t1.containsAllVariablesOf(t0)) {
	return pvi( getSingletonIterator(t1) );
      }
      break;
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      ASS(t0.containsAllVariablesOf(t1));
      return pvi( getSingletonIterator(t0) );
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      ASS(t1.containsAllVariablesOf(t0));
      return pvi( getSingletonIterator(t1) );
#if VDEBUG
    case Ordering::EQUAL:
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

TermIterator EqHelper::getEqualityArgumentIterator(Literal* lit)
{
  CALL("EqHelper::getEqualityArgumentIterator");
  ASS(lit->isEquality());

  return pvi( getConcatenatedIterator(
	  getSingletonIterator(*lit->nthArgument(0)),
	  getSingletonIterator(*lit->nthArgument(1))) );
}


}

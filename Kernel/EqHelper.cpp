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
 * @file EqHelper.cpp
 * Implements class EqHelper.
 */

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

#include "Ordering.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"
#include "ApplicativeHelper.hpp"

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
    //there should be no equality literals of equal terms
    case Ordering::EQUAL:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

VirtualIterator<Term*> EqHelper::getSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getSubtermIterator");
  return getRewritableSubtermIterator<NonVariableNonTypeIterator>(lit, ord);
}

#if VHOL

TermIterator EqHelper::getBooleanSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getSubtermIterator");
  return getRewritableSubtermIterator<BooleanSubtermIt>(lit, ord);
}

VirtualIterator<Term*> EqHelper::getFoSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getFoSubtermIterator");
  return getRewritableSubtermIterator<FirstOrderSubtermIt>(lit, ord);
}

#endif

/**
 * Return iterator on subterms of a literal, that can be rewritten by
 * superposition.
 */
template<class SubtermIterator>
VirtualIterator<ELEMENT_TYPE(SubtermIterator)> EqHelper::getRewritableSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("EqHelper::getRewritableSubtermIterator");

  if (lit->isEquality()) {
    TermList sel;
    switch(ord.getEqualityArgumentOrder(lit)) {
    case Ordering::INCOMPARABLE: {
      SubtermIterator si(lit);
      return getUniquePersistentIteratorFromPtr(&si);
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
      return VirtualIterator<ELEMENT_TYPE(SubtermIterator)>::getEmpty();
    }
    return getUniquePersistentIterator(vi(new SubtermIterator(sel.term(), true)));
  }

  SubtermIterator si(lit);
  return getUniquePersistentIteratorFromPtr(&si);

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
    //there should be no equality literals of equal terms
    case Ordering::EQUAL:
      ASSERTION_VIOLATION;
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
    //there should be no equality literals of equal terms
    case Ordering::EQUAL:
      ASSERTION_VIOLATION;
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

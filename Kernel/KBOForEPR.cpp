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
 * @file KBOForEPR.cpp
 * Implements class KBOForEPR for instances of the Knuth-Bendix ordering for EPR problems
 */

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"

#include "Shell/Property.hpp"

#include "Problem.hpp"
#include "Term.hpp"
#include "Signature.hpp"

#include "KBOForEPR.hpp"

namespace Kernel {

using namespace Lib;


/**
 * Create a KBO object.
 *
 * Function and predicate preferences and predicate levels
 * must be initialized after calling this constructor and
 * before any comparisons using this object are being made.
 */
KBOForEPR::KBOForEPR(Problem& prb, const Options& opt)
 : PrecedenceOrdering(prb, opt)
{
  CALL("KBOForEPR::KBOForEPR");
  ASS_EQ(prb.getProperty()->maxFunArity(),0);
}

/**
 * Compare arguments of non-equality literals l1 and l2 and return the
 * result of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBOForEPR::comparePredicates(Literal* l1, Literal* l2) const
{
  CALL("KBOForEPR::comparePredicates(Literal*...)");
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if (p1 != p2) {
    Comparison arComp=Int::compare(l1->arity(),l2->arity());
    if(arComp!=Lib::EQUAL) {
      //since on the ground level each literal argument must be a constant,
      //and all symbols are of weight 1, the literal with higher arity is
      //heavier and therefore greater
      return fromComparison(arComp);
    }

    Comparison prComp=Int::compare(predicatePrecedence(p1),predicatePrecedence(p2));
    ASS_NEQ(prComp, Lib::EQUAL); //precedence ordering is total
    return fromComparison(prComp);
  }

  TermList* t1=l1->args();
  TermList* t2=l2->args();

  ASS(!t1->isEmpty());
  while(*t1==*t2) {
    t1=t1->next();
    t2=t2->next();
    ASS(!t1->isEmpty()); //if we're at the end of the term, the literals would have been the same
  }
  return compare(*t1, *t2);
}

Ordering::Result KBOForEPR::compare(TermList tl1, TermList tl2) const
{
  CALL("KBOForEPR::compare(TermList)");
  ASS(!tl1.isTerm() || tl1.term()->arity()==0)
  ASS(!tl2.isTerm() || tl2.term()->arity()==0)

  if(tl1==tl2) {
    return EQUAL;
  }

  if(tl1.isOrdinaryVar() || tl2.isOrdinaryVar()) {
    return INCOMPARABLE;
  }

  //We're dealing with constants here -- if the top symbols were the same,
  //the terms would be equal as well.
  ASS_NEQ(tl1.term()->functor(), tl2.term()->functor());

  return compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
}


void KBOForEPR::showConcrete(ostream& out) const 
{ 
  out << "% < specific output for KBOForEPR not (yet) implemented >" << endl;
}

}

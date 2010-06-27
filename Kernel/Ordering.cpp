/**
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/SmartPtr.hpp"

#include "Shell/Options.hpp"

#include "Test/DiffOrdering.hpp"

#include "KBO.hpp"
#include "KBOForEPR.hpp"

#include "Ordering.hpp"

using namespace Lib;
using namespace Kernel;

OrderingSP Ordering::s_instance;

Ordering::Ordering()
{
  CALL("Ordering::Ordering");

  createEqualityComparator();
  ASS(_eqCmp);
}

Ordering::~Ordering()
{
  CALL("Ordering::~Ordering");

  destroyEqualityComparator();
}


Ordering* Ordering::instance()
{
  CALL("Ordering::instance");
  ASS(s_instance);

  //TODO: remove this when we know the ordering is always created when needed
  if(!s_instance) {
    create();
  }

  return s_instance.ptr();
}

/**
 * Creates the ordering
 *
 * Currently the ordering is created in @b SaturationAlgorithm::createFromOptions()
 */
void Ordering::create(bool epr)
{
  CALL("Ordering::create");
  ASS(!s_instance);

  if(epr) {
//    s_instance=OrderingSP(new Test::DiffOrdering(OrderingSP(new KBOForEPR),OrderingSP(new KBO)));
    s_instance=OrderingSP(new KBOForEPR);
  }
  else {
    s_instance=OrderingSP(new KBO);
  }
}


bool Ordering::orderingCreated()
{
  return s_instance;
}

Ordering::Result Ordering::fromComparison(Comparison c)
{
  CALL("Ordering::fromComparison");

  switch(c) {
  case Lib::GREATER:
    return GREATER;
  case Lib::EQUAL:
    return EQUAL;
  case Lib::LESS:
    return LESS;
  }
  ASSERTION_VIOLATION;
}

const char* Ordering::resultToString(Result r)
{
  CALL("Ordering::resultToString");

  switch(r) {
  case GREATER:
    return "GREATER";
  case GREATER_EQ:
    return "GREATER_EQ";
  case LESS:
    return "LESS";
  case LESS_EQ:
    return "LESS_EQ";
  case EQUAL:
    return "EQUAL";
  case INCOMPARABLE:
    return "INCOMPARABLE";
  default:
    ASSERTION_VIOLATION;
    return 0;
  }
}

/**
 * Remove non-maximal literals from the list @b lits. The order
 * of remaining literals stays unchanged.
 */
void Ordering::removeNonMaximal(LiteralList*& lits)
{
  LiteralList** ptr1=&lits;
  while(*ptr1) {
    LiteralList** ptr2=&(*ptr1)->tailReference();
    while(*ptr2 && *ptr1) {
      Ordering::Result res=compare((*ptr1)->head(), (*ptr2)->head());
      if(res==Ordering::GREATER || res==Ordering::GREATER_EQ || res==Ordering::EQUAL) {
	LiteralList::pop(*ptr2);
	continue;
      } else if(res==Ordering::LESS || res==Ordering::LESS_EQ) {
	LiteralList::pop(*ptr1);
	goto topLevelContinue;
      }
      ptr2=&(*ptr2)->tailReference();
    }
    ptr1=&(*ptr1)->tailReference();
topLevelContinue: ;
  }

}

//this function is implemented here instead of Term.cpp to reduce object file dependency
/** Return commutative term/literal argument order. */
Term::ArgumentOrder Term::computeArgumentOrder() const
{
  ASS(shared());
  ASS(commutative());
  ASS_EQ(arity(),2);

  Ordering* ord=Ordering::instance();
  switch(ord->compare(*nthArgument(0), *nthArgument(1)))
  {
  case Ordering::GREATER:
    return GREATER;
  case Ordering::LESS:
    return LESS;
  case Ordering::EQUAL:
    return EQUAL;
  case Ordering::INCOMPARABLE:
    return INCOMPARABLE;
  case Ordering::GREATER_EQ:
  case Ordering::LESS_EQ:
  default:
    NOT_IMPLEMENTED;
  }
}


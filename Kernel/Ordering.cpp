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
#include "Shell/Property.hpp"

#include "KBO.hpp"
#include "KBOForEPR.hpp"
#include "Problem.hpp"
#include "Signature.hpp"

#include "Ordering.hpp"

using namespace Lib;
using namespace Kernel;

OrderingSP Ordering::s_globalOrdering;

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


/**
 * If there is no global ordering yet, assign @c ordering to be
 * it and return true. Otherwise return false.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
bool Ordering::trySetGlobalOrdering(OrderingSP ordering)
{
  CALL("Ordering::trySetGlobalOrdering");

  if(s_globalOrdering) {
    return false;
  }
  s_globalOrdering = ordering;
  return true;
}

/**
 * If global ordering is set, return pointer to it, otherwise
 * return 0.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
Ordering* Ordering::tryGetGlobalOrdering()
{
  CALL("Ordering::tryGetGlobalOrdering");

  if(s_globalOrdering) {
    return s_globalOrdering.ptr();
  }
  else {
    return 0;
  }
}

/**
 * Creates the ordering
 *
 * Currently the ordering is created in @b SaturationAlgorithm::createFromOptions()
 */
Ordering* Ordering::create(Problem& prb, const Options& opt)
{
  CALL("Ordering::create");

  // KBOForEPR does not support colors; TODO fix this!
  if(prb.getProperty()->maxFunArity()==0 && !env.colorUsed) {
    return new KBOForEPR(prb, opt);
  }
  return new KBO(prb, opt);
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
  default:
    ASSERTION_VIOLATION;
  }
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
void Ordering::removeNonMaximal(LiteralList*& lits) const
{
  CALL("Ordering::removeNonMaximal");

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

Ordering::Result Ordering::getEqualityArgumentOrder(Literal* eq) const
{
  CALL("Ordering::getEqualityArgumentOrder");
  ASS(eq->isEquality());

  if(tryGetGlobalOrdering()!=this) {
    return compare(*eq->nthArgument(0), *eq->nthArgument(1));
  }

  Result res;
  ArgumentOrderVals precomputed = static_cast<ArgumentOrderVals>(eq->getArgumentOrderValue());
  if(precomputed!=0) {
    res = static_cast<Result>(precomputed);
    ASS_EQ(res, compare(*eq->nthArgument(0), *eq->nthArgument(1)));
  }
  else {
    res = compare(*eq->nthArgument(0), *eq->nthArgument(1));
    eq->setArgumentOrderValue(res);
  }
  return res;
}



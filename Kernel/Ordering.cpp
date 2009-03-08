/**
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include "../Forwards.hpp"

#include "../Lib/List.hpp"
#include "../Lib/SmartPtr.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Exception.hpp"
#include "../Shell/Options.hpp"

#include "Ordering.hpp"
#include "KBO.hpp"

using namespace Lib;
using namespace Kernel;


Ordering* Ordering::instance()
{
  static OrderingSP inst;

  if(!inst) {
    switch(env.options->symbolPrecedence()) {
    case Shell::Options::BY_ARITY:
      inst=OrderingSP(KBO::createArityPreferenceConstantLevels());
      break;
    case Shell::Options::BY_OCCURRENCE:
      inst=OrderingSP(KBO::createReversedAgePreferenceConstantLevels());
      break;
    default:
      NOT_IMPLEMENTED;
    }
  }
  return inst.ptr();
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

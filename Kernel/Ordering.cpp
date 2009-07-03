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

OrderingSP Ordering::s_instance;

Ordering* Ordering::instance()
{
  if(!s_instance) {
    s_instance=OrderingSP(KBO::create());
  }

  return s_instance.ptr();
}

bool Ordering::orderingCreated()
{
  return s_instance;
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

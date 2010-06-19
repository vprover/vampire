/**
 * @file LookaheadLiteralSelector.cpp
 * Defines class LookaheadLiteralSelector.
 */

#ifndef __LookaheadLiteralSelector__
#define __LookaheadLiteralSelector__

#include "Forwards.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

class LookaheadLiteralSelector
: public LiteralSelector
{
protected:
  virtual void doSelection(Clause* c, unsigned eligible);
private:
  Literal* pickTheBest(Literal** lits, unsigned cnt);
  void removeVariants(LiteralStack& lits);
};

}

#endif // __LookaheadLiteralSelector__

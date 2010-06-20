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
public:
  LookaheadLiteralSelector(bool completeSelection)
  : _completeSelection(completeSelection) {}
protected:
  virtual void doSelection(Clause* c, unsigned eligible);
private:
  Literal* pickTheBest(Literal** lits, unsigned cnt);
  void removeVariants(LiteralStack& lits);
  VirtualIterator<void> getGeneraingInferenceIterator(Literal* lit);

  struct GenIteratorIterator;

  bool _completeSelection;
};

}

#endif // __LookaheadLiteralSelector__

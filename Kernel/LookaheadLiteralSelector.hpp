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
  CLASS_NAME(LookaheadLiteralSelector);
  USE_ALLOCATOR(LookaheadLiteralSelector);
  
  LookaheadLiteralSelector(bool completeSelection, const Ordering& ordering, const Options& options)
  : LiteralSelector(ordering, options), _completeSelection(completeSelection) {}

  bool isBGComplete() const override { return _completeSelection; }
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

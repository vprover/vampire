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
 * @file LookaheadLiteralSelector.cpp
 * Defines class LookaheadLiteralSelector.
 */

#ifndef __LookaheadLiteralSelector__
#define __LookaheadLiteralSelector__

#include "Forwards.hpp"
#include "Shell/Options.hpp"
#include "LiteralSelector.hpp"

namespace Kernel {

class LookaheadLiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(LookaheadLiteralSelector);
  USE_ALLOCATOR(LookaheadLiteralSelector);
  
  LookaheadLiteralSelector(bool completeSelection, const Ordering& ordering, const Options& options)
  : LiteralSelector(ordering, options), _completeSelection(completeSelection) 
  {
    _delay = options.lookaheadDelay();
    _skipped = 0;
    _startupSelector = (_delay==0) ? 0 : LiteralSelector::getSelector(ordering, options, completeSelection ? 10 : 1010);
  }

  bool isBGComplete() const override { return _completeSelection; }
protected:
  void doSelection(Clause* c, unsigned eligible) override;
private:
  Literal* pickTheBest(Literal** lits, unsigned cnt);
  void removeVariants(LiteralStack& lits);
  VirtualIterator<void> getGeneraingInferenceIterator(Literal* lit);

  struct GenIteratorIterator;

  bool _completeSelection;
  LiteralSelector* _startupSelector;
  int _delay;
  int _skipped;
};

}

#endif // __LookaheadLiteralSelector__

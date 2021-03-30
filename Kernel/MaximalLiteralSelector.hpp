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
 * @file MaximalLiteralSelector.hpp
 * Defines class MaximalLiteralSelector.
 */


#ifndef __OrderingLiteralSelector__
#define __OrderingLiteralSelector__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class OrderingLiteralSelector implements literal
 * selector that selects a maximal negative literal,
 * if there is such. Otherwise it selects all maximal
 * literals.
 */
class MaximalLiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(MaximalLiteralSelector);
  USE_ALLOCATOR(MaximalLiteralSelector);

  MaximalLiteralSelector(const Ordering& ordering, const Options& options) : LiteralSelector(ordering, options) {}

  bool isBGComplete() const override { return true; }
protected:
  void doSelection(Clause* c, unsigned eligible) override;
};

};

#endif /* __OrderingLiteralSelector__ */

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
 * @file SpassLiteralSelector.hpp
 * Defines class SpassLiteralSelector.
 */


#ifndef __SpassLiteralSelector__
#define __SpassLiteralSelector__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class SpassLiteralSelector implements literal
 * selectors as understood from the code of SPASS 3.7.
 */
class SpassLiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(SpassLiteralSelector);
  USE_ALLOCATOR(SpassLiteralSelector);

  enum Values {
    OFF = 0,
    IFSEVERALMAXIMAL = 1,
    ALWAYS = 2
  };

  SpassLiteralSelector(const Ordering& ordering, const Options& options, Values value) :
    LiteralSelector(ordering, options), _value(value) {}

  bool isBGComplete() const override { return true; }
protected:
  void doSelection(Clause* c, unsigned eligible) override;

private:
  LiteralList* getMaximalsInOrder(Clause* c, unsigned eligible);

  Values _value;
};

};

#endif /* __SpassLiteralSelector__ */

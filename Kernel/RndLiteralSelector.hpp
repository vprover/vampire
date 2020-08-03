
/*
 * File RndLiteralSelector.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file RndLiteralSelector.hpp
 * Defines class RndLiteralSelector.
 */


#ifndef __RndLiteralSelector__
#define __RndLiteralSelector__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class SpassLiteralSelector implements literal
 * selectors as understood from the code of SPASS 3.7.
 */
class RndLiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(RndLiteralSelector);
  USE_ALLOCATOR(RndLiteralSelector);

  RndLiteralSelector(const Ordering& ordering, const Options& options, bool complete) :
    LiteralSelector(ordering, options), _complete(complete) {}

  bool isBGComplete() const override { return _complete; }
protected:
  void doSelection(Clause* c, unsigned eligible) override;

private:
  LiteralList* getMaximalsInOrder(Clause* c, unsigned eligible);

  bool _complete;
};

};

#endif /* __RndLiteralSelector__ */

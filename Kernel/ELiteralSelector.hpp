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
 * @file ELiteralSelector.hpp
 * Defines class ELiteralSelector.
 */


#ifndef __ELiteralSelector__
#define __ELiteralSelector__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class ELiteralSelector implements literal
 * selectors as understood from the manual and code of E 1.9.
 */
class ELiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(ELiteralSelector);
  USE_ALLOCATOR(ELiteralSelector);

  enum Values {
    // NoSelection, -- not implemented, this would be the same as spass's OFF
    SelectNegativeLiterals = 0,
    SelectPureVarNegLiterals = 1,
    // SelectLargestNegLit: Select the largest negative literal (by symbol counting, function symbols count as 2, variables as 1).
    // -- this is almost as the spass's ALWAYS, except for the specific way of computing weight (skipped for now)
    SelectSmallestNegLit = 2,
    // -- this will be an approximate (because of the different notion of weight) inversion of the (currently not implemented) above one
    SelectDiffNegLit = 3,
    SelectGroundNegLit = 4,
    SelectOptimalLit = 5
  };

  ELiteralSelector(const Ordering& ordering, const Options& options, Values value) :
    LiteralSelector(ordering, options), _value(value) {}

  bool isBGComplete() const override { return true; }
protected:
  void doSelection(Clause* c, unsigned eligible) override;

private:
  LiteralList* getMaximalsInOrder(Clause* c, unsigned eligible);

  unsigned lit_standard_diff(Literal* lit);
  unsigned lit_sel_diff_weight(Literal* lit);

  Values _value;
};

};

#endif /* __ELiteralSelector__ */

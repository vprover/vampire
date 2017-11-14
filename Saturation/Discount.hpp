
/*
 * File Discount.hpp.
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
 * @file Discount.hpp
 * Defines class Discount.
 */


#ifndef __Discount__
#define __Discount__

#include "Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class Discount
: public SaturationAlgorithm
{
public:
  CLASS_NAME(Discount);
  USE_ALLOCATOR(Discount);

  Discount(Problem& prb, const Options& opt)
    : SaturationAlgorithm(prb, opt) {}

  ClauseContainer* getSimplifyingClauseContainer();

protected:

  //overrides SaturationAlgorithm::handleClauseBeforeActivation
  bool handleClauseBeforeActivation(Clause* cl);

};

};

#endif /* __Discount__ */

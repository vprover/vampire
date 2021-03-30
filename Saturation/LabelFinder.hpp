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
 * @file LabelFinder.hpp
 * Defines class LabelFinder
 *
 * @author Giles
 * @since 3/02/2016
 */

#ifndef __LabelFinder__
#define __LabelFinder__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"

namespace Saturation {

using namespace Kernel;
using namespace Inferences;

class LabelFinder {
public:
  CLASS_NAME(LabelFinder);
  USE_ALLOCATOR(LabelFinder);
  
  ~LabelFinder();

  void onNewPropositionalClause(Clause* cl);

  Stack<unsigned> getFoundLabels(){ return _foundLabels;}

private:

  Stack<unsigned> _foundLabels;

};

}

#endif // __LabelFinder__

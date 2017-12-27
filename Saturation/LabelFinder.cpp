
/*
 * File LabelFinder.cpp.
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
 * @file LabelFinder.cpp
 * Implements class LabelFinder.
 */

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"

#include "LabelFinder.hpp"
#include "SaturationAlgorithm.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

LabelFinder::~LabelFinder()
{
  CALL("LabelFinder::~LabelFinder");

}

void LabelFinder::onNewPropositionalClause(Clause* cl)
{
  CALL("LabelFinder::onNewPropositionalClause");

  ASS(cl);
  // if we found a refutation ignore it
  if(Kernel::MainLoop::isRefutation(cl)) return;

  // Currently don't know what to do if conditional
  if(!cl->noSplits()) {
    return;
  }
  // Just looking for unit clauses
  if(cl->size() > 1){
    return;
  }

  unsigned predicate = (*cl)[0]->functor();

  // Looking for predicates
  ASS(env.signature->getPredicate(predicate));
  if(!env.signature->getPredicate(predicate)->label()){
    return;
  }

  _foundLabels.push(predicate);
}

}

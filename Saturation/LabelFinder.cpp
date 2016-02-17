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
  if(!env.signature->getPredicate(predicate)->label()){
    return;
  }

  _foundLabels.push(predicate);
  _clauses.insert(predicate,cl);
}

}

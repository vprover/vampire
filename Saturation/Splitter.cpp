/**
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "../Kernel/Clause.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "Splitter.hpp"

namespace Saturation
{

void Splitter::init(SaturationAlgorithm* sa)
{
  CALL("Splitter::init");

  _sa=sa;
}


/**
 * Return true if splitting is to be performed only if all
 * resulting clauses contain less positive literals than
 * the original one.
 */
bool Splitter::splitPositive()
{
  return env.options->splitPositive();
}

/**
 * Return true if @b cl fulfills the constraints for clauses
 * to be splitted.
 */
bool Splitter::splittingAllowed(Clause* cl)
{
  CALL("Splitter::splittingAllowed");

  if(env.options->splitInputOnly() && !cl->isInput()) {
    return false;
  }

  if(env.options->splitGoalOnly() && cl->inputType()!=Unit::CONJECTURE) {
    return false;
  }

  return true;
}

}

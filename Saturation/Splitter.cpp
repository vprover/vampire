/**
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "Splitter.hpp"

namespace Saturation
{

void Splitter::init(SaturationAlgorithm* sa)
{
  CALL("Splitter::init");

  _sa = sa;
  _ansLitMgr = _sa->getAnswerLiteralManager();
}

const Options& Splitter::getOptions() const
{
  CALL("Splitter::getOptions");
  ASS(_sa);

  return _sa->getOptions();
}

/**
 * Register the reduction of the @b cl clause
 */
void Splitter::onClauseReduction(Clause* cl, Clause* premise, Clause* replacement)
{
  CALL("Splitter::onClauseReduction(Clause*,Clause*,Clause*)");
  
  if(!premise) {
    ASS(!replacement);
    return;
  }

  onClauseReduction(cl, pvi( getSingletonIterator(premise) ), replacement);
}

/**
 * Return true if splitting is to be performed only if all
 * resulting clauses contain less positive literals than
 * the original one.
 */
bool Splitter::splitPositive()
{
  return getOptions().splitPositive();
}

/**
 * Return true if @b cl fulfills the constraints for clauses
 * to be splitted.
 */
bool Splitter::splittingAllowed(Clause* cl)
{
  CALL("Splitter::splittingAllowed");

  if(getOptions().splitInputOnly() && !cl->isInput()) {
    return false;
  }

  if(getOptions().splitGoalOnly() && cl->inputType()!=Unit::CONJECTURE) {
    return false;
  }

  return true;
}

bool Splitter::isAnswerLiteral(Literal* lit)
{
  CALL("Splitter::isAnswerLiteral");

  return _ansLitMgr && _ansLitMgr->isAnswerLiteral(lit);
}

}

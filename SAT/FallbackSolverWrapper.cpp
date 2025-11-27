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
 * @file FallbackSolverWrapper.cpp
 * Implements class FallbackSolverWrapper.
 */

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "FallbackSolverWrapper.hpp"

namespace SAT
{

/**
 *
 * @author Giles
 */
VarAssignment FallbackSolverWrapper::getAssignment(unsigned var)
{
  ASS_G(var,0); ASS_LE(var,_varCnt);

  if(_usingFallback){
    return _fallback->getAssignment(var);
  }
  return _inner->getAssignment(var); 
}


Status FallbackSolverWrapper::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) {
  // Currently always run the _inner solver to see if we can use it
  Status status = _inner->solveUnderAssumptionsLimited(assumps, conflictCountLimit);

  // Check if we need to use _fallback
  if(status == Status::UNKNOWN){
    status = _fallback->solveUnderAssumptionsLimited(assumps, conflictCountLimit);
    _usingFallback = true;
    ASS(status != Status::UNKNOWN);
    env.statistics->smtFallbacks++;
  }
  else{
    _usingFallback = false;
  }
  return status;
}


}

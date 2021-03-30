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

#include "Debug/RuntimeStatistics.hpp"

#include "SAT/SATClause.hpp"

#include "FallbackSolverWrapper.hpp"

namespace SAT
{

FallbackSolverWrapper::FallbackSolverWrapper(SATSolver* inner,SATSolver* fallback)
 : _inner(inner), _fallback(fallback), _usingFallback(false),  _varCnt(0) 
{
  CALL("FallbackSolverWrapper::FallbackSolverWrapper");
}

/**
 * Add a clause to sat solver
 *
 * @author Giles
 */
void FallbackSolverWrapper::addClause(SATClause* cl)
{
  CALL("FallbackSolverWrapper::addClause");
  
  _inner->addClause(cl);
  _fallback->addClause(cl);
}

/**
 *
 * @author Giles 
 */
SATSolver::Status FallbackSolverWrapper::solve(unsigned conflictCountLimit)
{
  CALL("FallbackSolverWrapper::solve"); 
  
  // Currently always run the _inner solver to see if we can use it
  Status status = _inner->solve(conflictCountLimit);

  // Check if we need to use _fallback
  if(status == Status::UNKNOWN){
    status = _fallback->solve(conflictCountLimit);
    _usingFallback = true;
    ASS(status != Status::UNKNOWN);
    env.statistics->smtFallbacks++;
  } 
  else{
    _usingFallback = false;
  }
  return status;
}

/**
 *
 * @author Giles
 */
SATSolver::VarAssignment FallbackSolverWrapper::getAssignment(unsigned var)
{
  CALL("FallbackSolverWrapper::getAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  if(_usingFallback){
    return _fallback->getAssignment(var);
  }
  return _inner->getAssignment(var); 
}

}

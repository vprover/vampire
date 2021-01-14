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
 * @file ShortConflictMetaDP.cpp
 * Implements class ShortConflictMetaDP.
 */

#include "ShortConflictMetaDP.hpp"

namespace DP
{

/**
 * Computes number of literals in core not implied at the zero level
 * of the SAT solver i.e. those that have not been fully decided and
 * can be backtracked.
 */
unsigned ShortConflictMetaDP::getCoreSize(const LiteralStack& core)
{
  CALL("ShortConflictMetaDP::getCoreSize");
  // ASS_EQ(_solver.getStatus(), SATSolver::SATISFIABLE);

  unsigned res = 0;
  LiteralStack::ConstIterator cit(core);
  while(cit.hasNext()) {
    Literal* lit = cit.next();
    SATLiteral sl = _sat2fo.toSAT(lit);
    ASS(_solver.trueInAssignment(sl));
    bool zeroImplied = _solver.isZeroImplied(sl.var());
    if(!zeroImplied) {
      res++;
    }
  }
  return res;
}

/**
 * Gets status of inner. If this is unsat then filter unsat cores so that we only
 * keep cores that are the smallest or one larger than the smallest.
 */
DecisionProcedure::Status ShortConflictMetaDP::getStatus(bool getMultipleCores)
{
  CALL("ShortConflictMetaDP::getStatus");

  Status iStatus = _inner->getStatus(getMultipleCores);

  _unsatCores.reset();
  if(iStatus!=DecisionProcedure::UNSATISFIABLE) {
    return iStatus;
  }

  unsigned ucCnt = _inner->getUnsatCoreCount();
  ASS_G(ucCnt,0);
  if(ucCnt==1) {
    _unsatCores.push(LiteralStack());
    _inner->getUnsatCore(_unsatCores.top(), 0);
    return DecisionProcedure::UNSATISFIABLE;
  }

  unsigned minSz = UINT_MAX;

  typedef pair<LiteralStack,unsigned> CoreWithSize;
  static Stack<CoreWithSize> cores;
  ASS(cores.isEmpty());

  // Record cores with their sizes in cores stack and
  // keep track of smallest core size in minSz
  for(unsigned i=0; i<ucCnt; i++) {
    cores.push(CoreWithSize());
    LiteralStack& core = cores.top().first;
    unsigned& sz = cores.top().second;
    _inner->getUnsatCore(core, i);
    sz = getCoreSize(core);

    if(sz<minSz) {
      minSz = sz;
    }
  }

  // Only keep cores that are at most one literal larger than the smallest size
  while(cores.isNonEmpty()) {
    LiteralStack& core = cores.top().first;
    unsigned& sz = cores.top().second;

    //this is perhaps the most important line, contains condition that restricts the acceptable core size
    if(sz<=minSz+1) {
      //we keep this core as it's small enough
      _unsatCores.push(LiteralStack());
      std::swap(core, _unsatCores.top());
      ASS(core.isEmpty());
    }

    cores.pop();
  }

  ASS(_unsatCores.isNonEmpty());
  return DecisionProcedure::UNSATISFIABLE;
}

/**
 * Get the unsat core (literal stack) at coreIndex
 */
void ShortConflictMetaDP::getUnsatCore(LiteralStack& res, unsigned coreIndex)
{
  CALL("ShortConflictMetaDP::getUnsatCore");
  ASS(res.isEmpty());
  ASS_L(coreIndex, _unsatCores.size());

  res = _unsatCores[coreIndex];
}

}

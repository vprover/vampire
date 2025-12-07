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
 * @file FallbackSolverWrapper.hpp
 * Defines class FallbackSolverWrapper.
 *
 * The idea is to run two solvers next to each other 'falling back' to one if the first isn't giving
 * us an answer. The intended setting is where the main solver is a SMT solver that can return Unknown
 * and the fallback solver is a SAT solver that cannot 
 *
 * @author Giles
 */

#ifndef __FallbackSolverWrapper__
#define __FallbackSolverWrapper__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class FallbackSolverWrapper : public SATSolver {
public:
  FallbackSolverWrapper(SATSolver* inner,SATSolver* fallback)
    : _inner(inner), _fallback(fallback) {}

  void randomizeForNextAssignment(unsigned maxVar) override {
    _inner->randomizeForNextAssignment(maxVar);
    _fallback->randomizeForNextAssignment(maxVar);
  }

  void addClause(SATClause* cl) override {
    _inner->addClause(cl);
    _fallback->addClause(cl);
  }

  VarAssignment getAssignment(unsigned var) override;

  bool isZeroImplied(unsigned var) override {
    ASS_G(var,0); ASS_LE(var,_varCnt);

    if(_usingFallback){
      return _fallback->isZeroImplied(var);
    }

    // alternatively, we could directly refer to _inner, it must handle variables up to _varCnt as well
    return  _inner->isZeroImplied(var);
  }

  void ensureVarCount(unsigned newVarCnt) override { 
    _inner->ensureVarCount(newVarCnt); 
    _fallback->ensureVarCount(newVarCnt); 
    _varCnt=std::max(_varCnt,newVarCnt); 
  }


  unsigned newVar() override { 
    ALWAYS(_inner->newVar() == ++_varCnt);
    ALWAYS(_fallback->newVar() == _varCnt);
    return _varCnt;
  }
  
  void suggestPolarity(unsigned var,unsigned pol) override { 
    _inner->suggestPolarity(var,pol); 
    _fallback->suggestPolarity(var,pol); 
  }

  Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) override;

  SATLiteralStack failedAssumptions() override {
    if(_usingFallback)
      return _fallback->failedAssumptions();
    return _inner->failedAssumptions();
  }

  SATClauseList *minimizePremises(SATClauseList *premises) override {
    if(_usingFallback)
      return _fallback->minimizePremises(premises);
    return _inner->minimizePremises(premises);
  }
private:

  ScopedPtr<SATSolver> _inner;
  ScopedPtr<SATSolver> _fallback;

  bool _usingFallback = false;
  unsigned _varCnt = 0;

};

}

#endif // __FallbackSolverWrapper__

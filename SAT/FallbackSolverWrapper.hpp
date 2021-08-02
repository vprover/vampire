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

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class FallbackSolverWrapper : public SATSolver {
public:
  CLASS_NAME(FallbackSolverWrapper);
  USE_ALLOCATOR(FallbackSolverWrapper);

  FallbackSolverWrapper(SATSolver* inner,SATSolver* fallback);

  SATClause* getRefutation() final { 
    if(_usingFallback){
      return _fallback->getRefutation();
    }
    return _inner->getRefutation(); 
  }
  SATClauseList* getRefutationPremiseList() final {
    if(_usingFallback){
      return _fallback->getRefutationPremiseList();
    }
    return _inner->getRefutationPremiseList();
  }
  void randomizeForNextAssignment(unsigned maxVar) final {
    _fallback->randomizeForNextAssignment(maxVar);
    _inner->randomizeForNextAssignment(maxVar);
  }

  void addClause(SATClause* cl) final;
  Status solve(unsigned conflictCountLimit) final;
  VarAssignment getAssignment(unsigned var) final;

  bool isZeroImplied(unsigned var) final {
    CALL("FallbackSolverWrapper::isZeroImplied");
    ASS_G(var,0); ASS_LE(var,_varCnt);

    if(_usingFallback){
      return _fallback->isZeroImplied(var);
    }

    // alternatively, we could directly refer to _inner, it must handle variables up to _varCnt as well
    return  _inner->isZeroImplied(var);
  }
  void collectZeroImplied(SATLiteralStack& acc) final { 
    if(_usingFallback){
      _fallback->collectZeroImplied(acc);
      return;
    }
    _inner->collectZeroImplied(acc); 
  }

  SATClause* getZeroImpliedCertificate(unsigned var) final { 
    if(_usingFallback){
      return _fallback->getZeroImpliedCertificate(var);
    }
    return _inner->getZeroImpliedCertificate(var); 
  }

  void ensureVarCount(unsigned newVarCnt) final { 
    _inner->ensureVarCount(newVarCnt); 
    _fallback->ensureVarCount(newVarCnt); 
    _varCnt=max(_varCnt,newVarCnt); 
  }


  unsigned newVar() final { 
    CALL("FallbackSolverWrapper::newVar");
    
    ALWAYS(_inner->newVar() == ++_varCnt);
    ALWAYS(_fallback->newVar() == _varCnt);
    return _varCnt;
  }
  
  void suggestPolarity(unsigned var,unsigned pol) final { 
    _inner->suggestPolarity(var,pol); 
    _fallback->suggestPolarity(var,pol); 
  }

private:

  SATSolverSCP _inner;
  SATSolverSCP _fallback;

  bool _usingFallback;

  unsigned _varCnt;

};

}

#endif // __FallbackSolverWrapper__

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
 * @file CombinatorDemodISE.hpp
 * Defines class CombinatorDemodISE.
 */


#ifndef __GroundReasoningISE__
#define __GroundReasoningISE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "SAT/SATSolver.hpp"
#include "SAT/SAT2FO.hpp"

#include "SAT/Z3Interfacing.hpp"

namespace Inferences {

class GroundReasoningISE
: public ImmediateSimplificationEngine
{
public:

  CLASS_NAME(GroundReasoningISE);
  USE_ALLOCATOR(GroundReasoningISE);

  GroundReasoningISE() : 
   ImmediateSimplificationEngine() {
    CALL("GroundReasoningISE::GroundReasoningISE()");

    // env.options????
    _solver = new Z3Interfacing(*env.options,_sat2fo, /* unsat core */ false,"");
  }

  Clause* simplify(Clause* cl);

private:
  ScopedPtr<SATSolverWithAssumptions> _solver;
  SAT2FO _sat2fo;
};

};

#endif /* __GroundReasoningISE__ */

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
 * @file CombinatorDemodISE.cpp
 * Implements class CombinatorDemodISE.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RapidHelper.hpp"
#include "Shell/Statistics.hpp"
#include "GroundReasoningISE.hpp"


#include "SAT/SATClause.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/SATInference.hpp"


using namespace Lib;
using namespace Kernel;
using namespace Inferences;


Clause* GroundReasoningISE::simplify(Clause* c)
{
  CALL("GroundReasoningISE::simplify");

  static bool interpNoEquality = env.options->groundReasoningNoEquality();

  static SATLiteralStack plits;
  plits.reset();

  static SATLiteralStack assumps;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    plits.push(_sat2fo.toSAT(lit));
  }

  unsigned idx;
  for(unsigned i = 0; i < c->length(); i++){
    assumps.reset();
    Literal* lit = (*c)[i];
    if(lit->ground()){
      assumps.push(plits[i]);
      SATSolver::Status res = _solver->solveUnderAssumptions(assumps);  
      if (res == SATSolver::UNSATISFIABLE) { 
        idx = i;
        goto after_loop;
      }
    }
     
  }

  // create SAT clause and add to solver
  // noSplits condition is for soundness
  if(c->length() == 1 && (*c)[0]->ground() && c->noSplits()){
    Literal* lit = (*c)[0];
    Signature::Symbol* sym = env.signature->getPredicate(lit->functor());
    if((lit->functor() != 0 && sym->interpreted()) || !interpNoEquality){
      SATClause* scl = SATClause::fromStack(plits);
      SATInference* inf = new FOConversionInference(c);
      scl->setInference(inf);
      _solver->addClause(scl);
    }
  }

  return c;
  
after_loop:

  unsigned len = c->length() - 1;
  // TODO get proper anscetor clauses
  Clause* conclusion = new(len) Clause(len,
      SimplifyingInference1(InferenceRule::GROUND_THEORY_SIMP, c));

  unsigned next = 0;
  for (unsigned i = 0; i < c->length(); i++) {
    if(i != idx){
      (*conclusion)[next++] = (*c)[i];
    }
  }
  ASS(next == len);

  return conclusion;
}




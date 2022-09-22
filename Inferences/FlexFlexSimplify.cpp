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

#if VHOL

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "FlexFlexSimplify.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;


Clause* FlexFlexSimplify::simplify(Clause* c)
{
  CALL("FlexFlexSimplify::simplify");

  if(c->isEmpty()) return c;
 
  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    if(!lit->isFlexFlex()){
      return c;
    }  
  }
  // all flex flex, return the empty clause
  return new(0) Clause(0, SimplifyingInference1(InferenceRule::FLEX_FLEX_SIMPLIFY, c));
}

#endif


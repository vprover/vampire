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
 * @file BoolSimp.hpp
 * Defines class BoolSimp.
 */

#ifndef __BOOL_SIMP__
#define __BOOL_SIMP__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class BoolSimp : public ImmediateSimplificationEngine
{
  public:
    CLASS_NAME(BoolSimp);
    USE_ALLOCATOR(BoolSimp);
    Clause* simplify(Clause* premise);

  private:
    TermList boolSimplify(TermList term); 
    TermList negate(TermList term);
    bool areComplements(TermList t1, TermList t2);
};

}

#endif

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
 * @file FOOLParamodulation.hpp
 * Defines class FOOLParamodulation.
 */

#ifndef __CASES_SIMP__
#define __CASES_SIMP__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class CasesSimp : public ImmediateSimplificationEngineMany {
  public:
    Option<ClauseIterator> simplifyMany(Clause* premise);

    ClauseIterator performSimplification(Clause* cl, Literal* lit, TermList t);
    struct RewriteableSubtermsFn;
    struct isEqualityLit
    {
      bool operator()(Literal* lit)
      {
        return lit->isEquality();
      }
    };
    struct ResultFn;
};

}

#endif

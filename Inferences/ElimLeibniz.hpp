
/*
 * File BoolSimp.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file BoolSimp.hpp
 * Defines class BoolSimp.
 */

#ifndef __ElimLeibniz__
#define __ElimLeibniz__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Inferences {

class ElimLeibniz : public GeneratingInferenceEngine
{
  public:
    CLASS_NAME(ElimLeibniz);
    USE_ALLOCATOR(ElimLeibniz);

    ClauseIterator generateClauses(Clause* premise);

  private:

    struct LeibEqRec {
      unsigned var;

      TermList argSort;
      TermList arg;
    };

    bool polarity(Literal* lit);

    bool isPair(Literal* l1, Literal* l2);

    Clause* createConclusion(Clause* premise, Literal* newLit, Literal* posLit, Literal* negLit, RobSubstitution& subst);

    LeibEqRec getLiteralInfo(Literal* lit);

};

}

#endif

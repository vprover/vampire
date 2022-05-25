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
 * @file CombinatorNormalisationISE.hpp
 * Defines class CombinatorNormalisationISE.
 */


#ifndef __CombinatorNormalisationISE__
#define __CombinatorNormalisationISE__

#include "Kernel/Signature.hpp"
#include "Forwards.hpp"
#include "InferenceEngine.hpp"

//simplification engine for normalising combinators.
//uses the following equations:

// S(KX)(KY) -> K(XY)
// S(KX)I -> X
// S(KX)Y -> BXY
// SKX -> I
// S(BKX) -> KX
// S(BKX)Y -> X
// BX(KY) -> KXY
// BXI -> X
// BI -> I
// C(KX)Y -> K(XY)

namespace Inferences {

class CombinatorNormalisationISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CombinatorNormalisationISE);
  USE_ALLOCATOR(CombinatorNormalisationISE);

  CombinatorNormalisationISE(){}
  Clause* simplify(Clause* cl);
private:
   TermList normalise(TermList t);
   bool replaceWithSmallerCombinator(TermList& t);
   TermList createKTerm(TermList s1, TermList s2, TermList arg1);
   TermList createSCorBTerm(TermList arg1, TermList arg1sort, TermList arg2, TermList arg2sort, Signature::Combinator comb);
};

};

#endif /* __CombinatorNormalisationISE__ */

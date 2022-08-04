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
#include "Kernel/TermTransformer.hpp"
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

class CombinatorNormaliser : public TermTransformer {
public:
  // true means create shared terms
  // true means recurse into replaced terms
  CombinatorNormaliser() : TermTransformer(true, true) {} 
  TermList transformSubterm(TermList trm) override;
};

class CombinatorNormalisationISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CombinatorNormalisationISE);
  USE_ALLOCATOR(CombinatorNormalisationISE);

  static TermList replaceWithSmallerCombinator(TermList t);

  CombinatorNormalisationISE(){}
  Clause* simplify(Clause* cl);
private:
  static TermList createKTerm(TermList s1, TermList s2, TermList arg1);
  static TermList createSCorBTerm(TermList arg1, TermList arg1sort, TermList arg2, TermList arg2sort, Signature::Combinator comb);
};

};

#endif /* __CombinatorNormalisationISE__ */

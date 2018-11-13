
/*
 * File ExtendedNarrowing.hpp.
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
 * @file ExtendedNarrowing.hpp
 * Defines class ExtendedNarrowing.
 */


#ifndef __ExtendedNarrowing__
#define __ExtendedNarrowing__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ExtendedNarrowing
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(ExtendedNarrowing);
  USE_ALLOCATOR(ExtendedNarrowing);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);
  
private:
  ExtendedNarrowingIndex* _index;

  static int value(const TermList tl){
    CALL("ExtendedNarrowing::value");
    
    if(!tl.isTerm()){ return -1;}
    if(env.signature->isFoolConstantSymbol(true, tl.term()->functor())){ return 1;}
    if(env.signature->isFoolConstantSymbol(false, tl.term()->functor())){ return 0;}
    
    return -1;
  }  
  
  static Literal* toFalsity(TermList boolTerm) {
    return Literal::createEquality(true, boolTerm, TermList(Term::foolFalse()), Sorts::SRT_BOOL);
  }  
  
  static Literal* toTruth(TermList boolTerm) {
    return Literal::createEquality(true, boolTerm, TermList(Term::foolTrue()), Sorts::SRT_BOOL);
  }

  struct ApplicableRewritesFn;
  struct ResultFn;  
  struct PiSigmaResultFn;
  struct NarrowingResultIterator;
  struct PSNarrowingResultIterator;
  struct IsNarrowableBoolEquality;
  
};


};

#endif /* __ExtendedNarrowing__ */


/*
 * File InterpretedSimplifier.hpp.
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
 * @file InterpretedSimplifier.hpp
 * Defines class InterpretedSimplifier.
 */

#ifndef __InterpretedSimplifier__
#define __InterpretedSimplifier__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;
#if 0
class InterpretedSimplifier
: public ForwardSimplificationEngine
{
public:
  InterpretedSimplifier();
  ~InterpretedSimplifier();

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:

  class ClauseSimplifier;

  ClauseSimplifier* _simpl;
  ArithmeticIndex* _ai;
};
#endif
}

#endif // __InterpretedSimplifier__


/*
 * File CheckedFwSimplifier.hpp.
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
 * @file CheckedFwSimplifier.hpp
 * Defines class CheckedFwSimplifier.
 */

#ifndef __CheckedFwSimplifier__
#define __CheckedFwSimplifier__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Test {

using namespace Inferences;

class CheckedFwSimplifier
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(CheckedFwSimplifier);
  USE_ALLOCATOR(CheckedFwSimplifier);

  CheckedFwSimplifier(ForwardSimplificationEngine* fse1, ForwardSimplificationEngine* fse2);
  ~CheckedFwSimplifier();

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  struct CheckingPerformer;

  ForwardSimplificationEngine* _fse1;
  ForwardSimplificationEngine* _fse2;

  CheckingPerformer* _chp;
};

}

#endif // __CheckedFwSimplifier__

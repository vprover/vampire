
/*
 * File InterpretedEvaluation.hpp.
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
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InterpretedEvaluation);
  USE_ALLOCATOR(InterpretedEvaluation);

  InterpretedEvaluation(bool doNormalize, Ordering& ordering);
  virtual ~InterpretedEvaluation();

  Clause* simplify(Clause* cl);
private:
  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue,Stack<Literal*>& sideConditions);

  InterpretedLiteralEvaluator* _simpl;
  Ordering& _ordering;
};

};

#endif /* __InterpretedEvaluation__ */

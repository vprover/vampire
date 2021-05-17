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
};

};

#endif /* __InterpretedEvaluation__ */

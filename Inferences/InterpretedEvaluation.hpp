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

#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ImmediateSimplificationEngine
{
public:
  InterpretedEvaluation(bool doNormalize, Ordering& ordering);
  ~InterpretedEvaluation() override;

  Clause* simplify(Clause* cl) override;
private:
  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);

  InterpretedLiteralEvaluator* _simpl;
};

};

#endif /* __InterpretedEvaluation__ */

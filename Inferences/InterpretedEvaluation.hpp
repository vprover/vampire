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

  InterpretedEvaluation();
  virtual ~InterpretedEvaluation();

  Clause* simplify(Clause* cl);
private:
  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue,Stack<Literal*>& sideConditions);

  InterpretedLiteralEvaluator* _simpl;
};

};

#endif /* __InterpretedEvaluation__ */

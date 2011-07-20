/**
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ImmediateSimplificationEngine
{
public:
  InterpretedEvaluation();
  virtual ~InterpretedEvaluation();

  Clause* simplify(Clause* cl);
private:
  class Evaluator;
  class ConversionEvaluator;
  template<class T> class TypedEvaluator;
  class IntEvaluator;
  class RatEvaluator;
  class RealEvaluator;
  class LiteralSimplifier;

  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);

  LiteralSimplifier* _simpl;
};

};

#endif /* __InterpretedEvaluation__ */

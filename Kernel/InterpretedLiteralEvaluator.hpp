/**
 * @file InterpretedLiteralEvaluator.hpp
 * Defines class InterpretedLiteralEvaluator.
 */

#ifndef __InterpretedLiteralEvaluator__
#define __InterpretedLiteralEvaluator__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"

#include "TermTransformer.hpp"

namespace Kernel {

class InterpretedLiteralEvaluator :  private TermTransformer
{
public:
  InterpretedLiteralEvaluator();

  ~InterpretedLiteralEvaluator();

  bool evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst);

protected:
  class Evaluator;
  class ConversionEvaluator;
  template<class T> class TypedEvaluator;
  class IntEvaluator;
  class RatEvaluator;
  class RealEvaluator;

  typedef Stack<Evaluator*> EvalStack;

  virtual TermList transform(TermList trm);

  Evaluator* getFuncEvaluator(unsigned func);

  Evaluator* getPredEvaluator(unsigned pred);

  EvalStack _evals;
  DArray<Evaluator*> _funEvaluators;
  DArray<Evaluator*> _predEvaluators;
};


}

#endif // __InterpretedLiteralEvaluator__

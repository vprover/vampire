/**
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
private:
  int getInterpretedFunction(Term* t);
  int getInterpretedPredicate(Literal* lit);

  Term* evaluateFunction(int fnIndex, TermList* args);

  bool evaluatePredicate(int predIndex, TermList* args);

  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);
};

};

#endif /* __InterpretedEvaluation__ */

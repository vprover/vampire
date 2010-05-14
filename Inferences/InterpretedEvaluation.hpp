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
  InterpretedEvaluation();

  Clause* simplify(Clause* cl);
private:
  int getInterpretedFunction(Term* t);
  int getInterpretedPredicate(Literal* lit);

  Term* evaluateFunction(int fnIndex, TermList* args);
  bool simplifyFunction(int fnIndex, TermList* args, TermList& res);

  bool evaluatePredicate(int predIndex, TermList* args);
  Literal* simplifyPredicate(int predIndex, TermList* args, Literal* original);

  bool removeEquivalentAdditionsAndSubtractionsFromOneSide(TermList& arg1, TermList& arg2);
  bool removeEquivalentAdditionsAndSubtractions(TermList& arg1, TermList& arg2);

  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);

  Theory* theory;
};

};

#endif /* __InterpretedEvaluation__ */

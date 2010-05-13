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
  bool isInterpretedConstant(Term* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  Term* getRepresentation(InterpretedType val);

  Term* evaluateFunction(int fnIndex, TermList* args);
  bool evaluatePredicate(int predIndex, TermList* args);
  Literal* simplifyPredicate(int predIndex, TermList* args, Literal* original);

  bool removeEquivalentAdditionsAndSubtractions(TermList& arg1, TermList& arg2);

  bool simplifyLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);

  DHMap<InterpretedType, Term*> _constants;
};

};

#endif /* __InterpretedEvaluation__ */

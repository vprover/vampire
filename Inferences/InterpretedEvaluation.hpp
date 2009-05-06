/**
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "../Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

typedef int InterpretedType;

class InterpretedEvaluation
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
private:
  int getInterpretedFunction(Term* t);
  int getInterpretedPredicate(Literal* lit);
  bool isInterpretedConstant(Term* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  Term* getRepresentation(InterpretedType val);

  Term* interpretFunction(int fnIndex, TermList* args);
  bool interpretPredicate(int predIndex, TermList* args);
  bool evaluateLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);
};

};

#endif /* __InterpretedEvaluation__ */

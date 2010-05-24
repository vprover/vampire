/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Term.hpp"

namespace Kernel {

typedef int InterpretedType;

class Theory
{
public:
  /**
   * Interpreted symbols and predicates
   *
   * If interpreted_evaluation is enabled, predicates GREATER_EQUAL,
   * LESS and LESS_EQUAL should not appear in the run of the
   * SaturationAlgorithm (they'll be immediately simplified by the
   * InterpretedEvaluation simplification).
   */
  enum Interpretation
  {
    //predicates

    EQUAL,
    GREATER,
    GREATER_EQUAL,
    LESS,
    LESS_EQUAL,
    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,

    //functions

    SUCCESSOR,
    UNARY_MINUS,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
    INT_DIVIDE
  };
  /**
   * Number of elements in the enum Interpretation
   *
   * At some points we make use of the fact that we can iterate through all
   * interpretations by going through the set {0,...,interpretationElementCount-1}.
   */
  static const unsigned interpretationElementCount=16;

  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);


  static Theory* instance();

  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(Literal* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  Term* getRepresentation(InterpretedType val);
  unsigned getFnNum(Interpretation itp);
  unsigned getPredNum(Interpretation itp);

  TermList zero();
  TermList one();
  TermList minusOne();

private:
  Theory();

  Term* _zero;
  Term* _one;
  Term* _minusOne;
  DHMap<InterpretedType, Term*> _constants;

};

typedef Theory::Interpretation Interpretation;

extern Theory* theory;

}

#endif // __Theory__

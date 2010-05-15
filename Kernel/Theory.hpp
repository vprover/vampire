/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include "../Forwards.hpp"

#include "../Kernel/Term.hpp"

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

    //functions

    SUCCESSOR,
    UNARY_MINUS,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
    /** The X?Y:Z ternary operator like in C++ */
    IF_THEN_ELSE,
  };
  /**
   * Number of elements in the enum Interpretation
   *
   * At some points we make use of the fact that we can iterate through all
   * interpretations by going through the set {0,...,interpretationElementCount-1}.
   */
  static const unsigned interpretationElementCount=12;

  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);


  static Theory* instance();

  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);

  Interpretation interpretFunction(Term* t);
  Interpretation interpretPredicate(Literal* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  Term* getRepresentation(InterpretedType val);

  TermList zero();
  TermList one();

private:
  Theory();

  Term* _zero;
  Term* _one;
  DHMap<InterpretedType, Term*> _constants;

};

typedef Theory::Interpretation Interpretation;

}

#endif // __Theory__

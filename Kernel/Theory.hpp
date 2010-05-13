/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

namespace Kernel {

typedef int InterpretedType;

class Theory
{
public:
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
  static const int interpretationElementCount=12;

  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);

};

typedef Theory::Interpretation Interpretation;

}

#endif // __Theory__

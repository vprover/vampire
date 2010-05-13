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
    //functions

    SUCCESSOR,
    UNARY_MINUS,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
    /** The X?Y:Z ternary operator like in C++ */
    IF_THEN_ELSE,

    //predicates

    GREATER,
    GREATER_EQUAL,
    LESS,
    LESS_EQUAL
  };

  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);

};

typedef Theory::Interpretation Interpretation;

}

#endif // __Theory__

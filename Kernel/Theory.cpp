/**
 * @file Theory.cpp
 * Implements class Theory.
 */

#include "../Debug/Assertion.hpp"

#include "Theory.hpp"

namespace Kernel
{

/**
 * Return arity of the symbol that is interpreted by Interpretation
 * @b i.
 */
unsigned Theory::getArity(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::getArity");

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
    return 1;

  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
    return 2;

  case IF_THEN_ELSE:
    return 3;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is a function (false is returned for predicates).
 */
bool Theory::isFunction(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isFunction");

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case IF_THEN_ELSE:
    return true;

  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
    return false;
  }
  ASSERTION_VIOLATION;
}


}

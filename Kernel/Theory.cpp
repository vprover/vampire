/**
 * @file Theory.cpp
 * Implements class Theory.
 */

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "../Lib/Environment.hpp"

#include "../Kernel/Signature.hpp"

#include "Theory.hpp"

namespace Kernel
{

using namespace Lib;

const unsigned Theory::interpretationElementCount;

Theory* Theory::instance()
{
  static Theory* inst=new Theory;

  return inst;
}

Theory::Theory()
: _zero(0), _one(0)
{

}

/**
 * Return arity of the symbol that is interpreted by Interpretation
 * @b i.
 */
unsigned Theory::getArity(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::getArity");
  ASS_L(i,(int)interpretationElementCount);

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
    return 1;

  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case EQUAL:
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
  ASS_L(i,(int)interpretationElementCount);

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case IF_THEN_ELSE:
    return true;

  case EQUAL:
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
    return false;
  }
  ASSERTION_VIOLATION;
}


TermList Theory::zero()
{
  if(!_zero) {
    _zero=getRepresentation(0);
  }
  return TermList(_zero);
}

TermList Theory::one()
{
  if(!_one) {
    _one=getRepresentation(1);
  }
  return TermList(_one);
}

bool Theory::isInterpretedConstant(Term* t)
{
  CALL("Theory::isInterpretedConstant");

  return t->arity()==0 && env.signature->getFunction(t->functor())->interpreted();
}

bool Theory::isInterpretedConstant(TermList t)
{
  return t.isTerm() && isInterpretedConstant(t.term());
}

bool Theory::isInterpretedPredicate(Literal* lit)
{
  return env.signature->getPredicate(lit->functor())->interpreted();
}

bool Theory::isInterpretedFunction(Term* t)
{
  return t->arity()!=0 && env.signature->getFunction(t->functor())->interpreted();
}

bool Theory::isInterpretedFunction(TermList t)
{
  return t.isTerm() && isInterpretedFunction(t.term());
}

bool Theory::isInterpretedFunction(Term* t, Interpretation itp)
{
  return t->arity()!=0 && env.signature->getFunction(t->functor())->interpreted() &&
      interpretFunction(t)==itp;
}

Interpretation Theory::interpretFunction(Term* t)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedFunction(t));

  return static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(t->functor()))
      ->getInterpretation();
}

Interpretation Theory::interpretPredicate(Literal* lit)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedPredicate(lit));

  return static_cast<Signature::InterpretedSymbol*>(env.signature->getPredicate(lit->functor()))
      ->getInterpretation();
}

InterpretedType Theory::interpretConstant(Term* t)
{
  CALL("Theory::interpretConstant");
  ASS(isInterpretedConstant(t));

  Signature::InterpretedSymbol* sym =
      static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(t->functor()));

  return sym->getValue();
}

InterpretedType Theory::interpretConstant(TermList t)
{
  CALL("Theory::interpretConstant(TermList)");
  ASS(t.isTerm());

  return interpretConstant(t.term());
}

Term* Theory::getRepresentation(InterpretedType val)
{
  Term** pRes;

  if(!_constants.getValuePtr(val, pRes)) {
    return *pRes;
  }

  int functor=env.signature->addInterpretedConstant(val);

  *pRes=Term::create(functor, 0, 0);
  return *pRes;
}


}

















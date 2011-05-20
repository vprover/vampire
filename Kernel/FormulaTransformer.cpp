/**
 * @file FormulaTransformer.cpp
 * Implements class FormulaTransformer.
 */

#include "Formula.hpp"

#include "FormulaTransformer.hpp"

namespace Kernel
{

Formula* FormulaTransformer::apply(Formula* form)
{
  CALL("FormulaTransformer::apply");

  switch (form->connective()) {
  case LITERAL:
    return applyLiteral(form);
  case AND:
    return applyAnd(form);
  case OR:
    return applyOr(form);
  case IMP:
    return applyImp(form);
  case NOT:
    return applyNot(form);
  case IFF:
    return applyIff(form);
  case XOR:
    return applyXor(form);
  case FORALL:
    return applyForAll(form);
  case EXISTS:
    return applyExists(form);

  case TRUE:
  case FALSE:
    return applyTrueFalse(form);
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return 0;
#endif
  }
}

Formula* FormulaTransformer::applyJunction(Formula* form)
{
  CALL("FormulaTransformer::applyJunction");

  FormulaList* resArgs = 0;
  bool modified = false;
  FormulaList::Iterator fs(form->args());
  while (fs.hasNext()) {
    Formula* arg = fs.next();
    Formula* newArg = apply(arg);
    if(arg!=newArg) {
	modified = true;
    }
    FormulaList::push(newArg, resArgs);
  }
  if(!modified) {
    resArgs->destroy();
    return form;
  }
  return new JunctionFormula(form->connective(), resArgs);
}

Formula* FormulaTransformer::applyNot(Formula* form)
{
  CALL("FormulaTransformer::applyNot");

  Formula* newArg = apply(form->uarg());
  if(newArg==form->uarg()) {
    return form;
  }
  return new NegatedFormula(newArg);
}

Formula* FormulaTransformer::applyBinary(Formula* form)
{
  CALL("FormulaTransformer::applyBinary");

  Formula* newLeft = apply(form->left());
  Formula* newRight = apply(form->right());
  if(newLeft==form->left() && newRight==form->right()) {
    return form;
  }
  return new BinaryFormula(form->connective(), newLeft, newRight);
}

Formula* FormulaTransformer::applyQuantified(Formula* form)
{
  CALL("FormulaTransformer::applyQuantified");

  Formula* newArg = apply(form->qarg());
  if(newArg==form->qarg()) {
    return form;
  }
  return new QuantifiedFormula(form->connective(), form->vars(), newArg);
}

}

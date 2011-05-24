/**
 * @file FormulaTransformer.cpp
 * Implements class FormulaTransformer.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Recycler.hpp"
#include "Lib/ScopedLet.hpp"

#include "Formula.hpp"
#include "SortHelper.hpp"

#include "FormulaTransformer.hpp"

namespace Kernel
{

Formula* FormulaTransformer::apply(Formula* f)
{
  CALL("FormulaTransformer::apply");

  switch (f->connective()) {
  case LITERAL:
    return applyLiteral(f);
  case AND:
    return applyAnd(f);
  case OR:
    return applyOr(f);
  case IMP:
    return applyImp(f);
  case NOT:
    return applyNot(f);
  case IFF:
    return applyIff(f);
  case XOR:
    return applyXor(f);
  case FORALL:
    return applyForAll(f);
  case EXISTS:
    return applyExists(f);

  case TRUE:
  case FALSE:
    return applyTrueFalse(f);
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return 0;
#endif
  }
}

Formula* FormulaTransformer::applyJunction(Formula* f)
{
  CALL("FormulaTransformer::applyJunction");

  FormulaList* resArgs = 0;
  bool modified = false;
  FormulaList::Iterator fs(f->args());
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
    return f;
  }
  return new JunctionFormula(f->connective(), resArgs);
}

Formula* FormulaTransformer::applyNot(Formula* f)
{
  CALL("FormulaTransformer::applyNot");

  Formula* newArg = apply(f->uarg());
  if(newArg==f->uarg()) {
    return f;
  }
  return new NegatedFormula(newArg);
}

Formula* FormulaTransformer::applyBinary(Formula* f)
{
  CALL("FormulaTransformer::applyBinary");

  Formula* newLeft = apply(f->left());
  Formula* newRight = apply(f->right());
  if(newLeft==f->left() && newRight==f->right()) {
    return f;
  }
  return new BinaryFormula(f->connective(), newLeft, newRight);
}

Formula* FormulaTransformer::applyQuantified(Formula* f)
{
  CALL("FormulaTransformer::applyQuantified");

  Formula* newArg = apply(f->qarg());
  if(newArg==f->qarg()) {
    return f;
  }
  return new QuantifiedFormula(f->connective(), f->vars(), newArg);
}

////////////////////////////////////
// PolarityAwareFormulaTransformer
//

PolarityAwareFormulaTransformer::PolarityAwareFormulaTransformer()
{
  CALL("PolarityAwareFormulaTransformer::PolarityAwareFormulaTransformer");

  Recycler::get(_varSorts); //_varSorts is reset in the transform() function
}

PolarityAwareFormulaTransformer::~PolarityAwareFormulaTransformer()
{
  CALL("PolarityAwareFormulaTransformer::~PolarityAwareFormulaTransformer");

  Recycler::release(_varSorts);
}

unsigned PolarityAwareFormulaTransformer::getVarSort(unsigned var) const
{
  CALL("PolarityAwareFormulaTransformer::getVarSort");

  return _varSorts->get(var, Sorts::SRT_DEFAULT);
}

Formula* PolarityAwareFormulaTransformer::transform(Formula* f, int polarity)
{
  CALL("PolarityAwareFormulaTransformer::transform");
  ASS_REP(polarity==0 || polarity==1 || polarity==-1, polarity);

  _varSorts->reset();
  SortHelper::collectVariableSorts(f, *_varSorts);

  _polarity = polarity;
  return FormulaTransformer::transform(f);
}

Formula* PolarityAwareFormulaTransformer::applyNot(Formula* f)
{
  CALL("PolarityAwareFormulaTransformer::applyNot");

  ScopedLet<int> plet(_polarity, -_polarity);
  return FormulaTransformer::applyNot(f);
}

Formula* PolarityAwareFormulaTransformer::applyImp(Formula* f)
{
  CALL("PolarityAwareFormulaTransformer::applyImp");
  ASS_EQ(f->connective(),IMP);

  Formula* newLeft;
  {
    ScopedLet<int> plet(_polarity, -_polarity);
    newLeft = apply(f->left());
  }
  Formula* newRight = apply(f->right());
  if(newLeft==f->left() && newRight==f->right()) {
    return f;
  }
  return new BinaryFormula(f->connective(), newLeft, newRight);
}

/**
 * This function is called by the default implementation of
 * applyIff() and applyXor().
 */
Formula* PolarityAwareFormulaTransformer::applyBinary(Formula* f)
{
  CALL("PolarityAwareFormulaTransformer::applyBinary");
  ASS(f->connective()==IFF || f->connective()==XOR);

  ScopedLet<int> plet(_polarity, -_polarity);
  return FormulaTransformer::applyBinary(f);
}


}

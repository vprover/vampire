/**
 * @file FormulaTransformer.cpp
 * Implements class FormulaTransformer.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Recycler.hpp"
#include "Lib/ScopedLet.hpp"

#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "SortHelper.hpp"
#include "TermTransformer.hpp"

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

///////////////////////////////////////
// TermTransformingFormulaTransformer
//

Formula* TermTransformingFormulaTransformer::applyLiteral(Formula* f)
{
  CALL("TermTransformingFormulaTransformer::applyLiteral");

  Literal* lit = f->literal();
  Literal* res = _termTransformer.transform(lit);
  if(lit==res) { return f; }
  return new AtomicFormula(res);
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

  ScopedLet<int> plet(_polarity, 0);
  return FormulaTransformer::applyBinary(f);
}


///////////////////////////
// FormulaUnitTransformer
//

void FormulaUnitTransformer::transform(UnitList*& units)
{
  CALL("FormulaUnitTransformer::transform(UnitList*&)");

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
	continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* newUnit = transform(fu);
    if(fu==newUnit) {
      continue;
    }
    if(newUnit) {
	uit.replace(newUnit);
    }
    else {
	uit.del();
    }
  }
}

////////////////////////////////
// LocalFormulaUnitTransformer
//

FormulaUnit* LocalFormulaUnitTransformer::transform(FormulaUnit* unit)
{
  CALL("LocalFormulaUnitTransformer::transform(FormulaUnit*)");

  Formula* f = unit->formula();
  Formula* newForm = transform(f);
  if(f==newForm) {
    return unit;
  }
  Inference* inf = new Inference1(_rule, unit);
  return new FormulaUnit(newForm, inf, unit->inputType());
}

}


/**
 * @file FormulaTransformer.cpp
 * Implements class FormulaTransformer.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Recycler.hpp"
#include "Lib/ScopedLet.hpp"

#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "Problem.hpp"
#include "SortHelper.hpp"
#include "TermTransformer.hpp"

#include "FormulaTransformer.hpp"

namespace Kernel
{

Formula* FormulaTransformer::apply(Formula* f)
{
  CALL("FormulaTransformer::apply(Formula*)");

  if(!preApply(f)) {
    return f;
  }

  Formula* res;

  switch (f->connective()) {
  case LITERAL:
    res = applyLiteral(f);
    break;
  case AND:
    res = applyAnd(f);
    break;
  case OR:
    res = applyOr(f);
    break;
  case IMP:
    res = applyImp(f);
    break;
  case NOT:
    res = applyNot(f);
    break;
  case IFF:
    res = applyIff(f);
    break;
  case XOR:
    res = applyXor(f);
    break;
  case FORALL:
    res = applyForAll(f);
    break;
  case EXISTS:
    res = applyExists(f);
    break;
  case ITE:
    res = applyIte(f);
    break;
  case TERM_LET:
    res = applyTermLet(f);
    break;
  case FORMULA_LET:
    res = applyFormulaLet(f);
    break;

  case TRUE:
  case FALSE:
    res = applyTrueFalse(f);
    break;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
  postApply(f, res);
  return res;
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


Formula* FormulaTransformer::applyIte(Formula* f)
{
  CALL("FormulaTransformer::applyIte");
  ASS_EQ(f->connective(), ITE);

  Formula* newCond = apply(f->condArg());
  Formula* newThen = apply(f->thenArg());
  Formula* newElse = apply(f->elseArg());
  if(newCond==f->condArg() && newThen==f->thenArg() && newElse==f->elseArg()) {
    return f;
  }
  return new IteFormula(newCond, newThen, newElse);
}

Formula* FormulaTransformer::applyTermLet(Formula* f)
{
  CALL("FormulaTransformer::applyTermLet");
  ASS_EQ(f->connective(), TERM_LET);

  Formula* newBody = apply(f->letBody());
  if(newBody==f->letBody()) {
    return f;
  }
  return new TermLetFormula(f->termLetLhs(), f->termLetRhs(), newBody);
}

Formula* FormulaTransformer::applyFormulaLet(Formula* f)
{
  CALL("FormulaTransformer::applyFormulaLet");
  ASS_EQ(f->connective(), FORMULA_LET);

  Formula* newBody = apply(f->letBody());
  Formula* newRhs = apply(f->formulaLetRhs());
  if(newBody==f->letBody() && newRhs==f->formulaLetRhs()) {
    return f;
  }
  return new FormulaLetFormula(f->formulaLetLhs(), newRhs, newBody);
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

Formula* PolarityAwareFormulaTransformer::applyIte(Formula* f)
{
  CALL("PolarityAwareFormulaTransformer::applyIte");
  ASS_EQ(f->connective(), ITE);

  Formula* newCond;
  {
    ScopedLet<int> plet(_polarity, 0);
    newCond = apply(f->condArg());
  }
  Formula* newThen = apply(f->thenArg());
  Formula* newElse = apply(f->elseArg());
  if(newCond==f->condArg() && newThen==f->thenArg() && newElse==f->elseArg()) {
    return f;
  }
  return new IteFormula(newCond, newThen, newElse);
}

Formula* PolarityAwareFormulaTransformer::applyFormulaLet(Formula* f)
{
  CALL("PolarityAwareFormulaTransformer::applyFormulaLet");

  Formula* newBody = apply(f->letBody());
  Formula* newRhs;
  {
    ScopedLet<int> plet(_polarity, 0);
    newRhs = apply(f->formulaLetRhs());
  }
  if(newBody==f->letBody() && newRhs==f->formulaLetRhs()) {
    return f;
  }
  return new FormulaLetFormula(f->formulaLetLhs(), newRhs, newBody);
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


///////////////////////////////////////
// ScanAndApplyFormulaUnitTransformer
//

void ScanAndApplyFormulaUnitTransformer::apply(Problem& prb)
{
  CALL("ScanAndApplyFormulaUnitTransformer::apply(Problem&)");

  if(apply(prb.units())) {
    updateModifiedProblem(prb);
  }
}

bool ScanAndApplyFormulaUnitTransformer::apply(UnitList*& units)
{
  CALL("ScanAndApplyFormulaUnitTransformer::apply(UnitList*&)");

  scan(units);

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newUnit;
    if(u->isClause()) {
      Clause* cl = static_cast<Clause*>(u);
      if(!apply(cl, newUnit)) {
	continue;
      }
    }
    else {
      FormulaUnit* fu = static_cast<FormulaUnit*>(u);
      if(!apply(fu, newUnit)) {
	continue;
      }
    }
    if(newUnit==0) {
      uit.del();
    }
    else {
      uit.replace(newUnit);
    }
    modified = true;
  }

  UnitList* added = getIntroducedFormulas();
  if(added) {
    modified = true;
    uit.insert(added);
  }

  return modified;
}

void ScanAndApplyFormulaUnitTransformer::updateModifiedProblem(Problem& prb)
{
  CALL("ScanAndApplyFormulaUnitTransformer::updateModifiedProblem");

  prb.invalidateEverything();
}



}


/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FormulaTransformer.cpp
 * Implements class FormulaTransformer.
 */

#include "Lib/DHMap.hpp"
#include "Lib/ScopedLet.hpp"

#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "Problem.hpp"
#include "SortHelper.hpp"
#include "TermTransformer.hpp"
#include "Lib/DHMap.hpp"

#include "FormulaTransformer.hpp"

namespace Kernel
{

using namespace Lib;

Formula* FormulaTransformer::transform(Formula* f) {
  Formula* res = apply(f);
  return res;
}


Formula* FormulaTransformer::apply(Formula* f)
{
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
  case BOOL_TERM:
    res = new BoolTermFormula(apply(f->getBooleanTerm()));
    break;
  case TRUE:
  case FALSE:
    res = applyTrueFalse(f);
    break;
  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }
  postApply(f, res);
  return res;
}

TermList FormulaTransformer::apply(TermList ts) {
  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();

  if (term->isSpecial()) {
    Term::SpecialTermData *sd = ts.term()->getSpecialData();
    switch (sd->specialFunctor()) {
      case SpecialFunctor::ITE:
        return TermList(Term::createITE(apply(sd->getCondition()),
                                        apply(*term->nthArgument(0)),
                                        apply(*term->nthArgument(1)),
                                        sd->getSort()));

      case SpecialFunctor::FORMULA:
        return TermList(Term::createFormula(apply(sd->getFormula())));

      case SpecialFunctor::LET:
        return TermList(Term::createLet(sd->getFunctor(),
                                        sd->getVariables(),
                                        apply(sd->getBinding()),
                                        apply(*term->nthArgument(0)),
                                        sd->getSort()));

      case SpecialFunctor::LET_TUPLE:
        return TermList(Term::createTupleLet(sd->getFunctor(),
                                             sd->getTupleSymbols(),
                                             apply(sd->getBinding()),
                                             apply(*term->nthArgument(0)),
                                             sd->getSort()));

      case SpecialFunctor::TUPLE:
        return TermList(Term::createTuple(apply(TermList(sd->getTupleTerm())).term()));

      case SpecialFunctor::LAMBDA:
        NOT_IMPLEMENTED;
      case SpecialFunctor::MATCH: {
        DArray<TermList> terms(term->arity());
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = apply(*term->nthArgument(i));
        }
        return TermList(Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin()));
      }

    }
    ASSERTION_VIOLATION_REP(ts.toString());
  }

  if (term->shared()) {
    return ts;
  }

  Stack<TermList> args;
  Term::Iterator terms(term);
  while (terms.hasNext()) {
    args.push(apply(terms.next()));
  }

  return TermList(Term::create(term, args.begin()));
}

Formula* FormulaTransformer::applyJunction(Formula* f)
{
  Connective con = f->connective();

  FormulaList* resArgs = 0;
  bool modified = false;
  FormulaList::Iterator fs(f->args());
  while (fs.hasNext()) {
    Formula* arg = fs.next();
    Formula* newArg = apply(arg);
    if(arg!=newArg) {
      modified = true;
    }
    if(newArg->connective()==con) {
      //we flatten the two junctions
      FormulaList::pushFromIterator(FormulaList::Iterator(newArg->args()), resArgs);
    }
    else {
      FormulaList::push(newArg, resArgs);
    }
  }
  if(!modified) {
    FormulaList::destroy(resArgs);
    return f;
  }
  //we want to keep arguments in the same order as the input ones
  resArgs = FormulaList::reverse(resArgs);
  return new JunctionFormula(con, resArgs);
}

Formula* FormulaTransformer::applyNot(Formula* f)
{
  Formula* newArg = apply(f->uarg());
  if(newArg==f->uarg()) {
    return f;
  }
  if(newArg->connective()==NOT) {
    return newArg->uarg();
  }
  return new NegatedFormula(newArg);
}

Formula* FormulaTransformer::applyBinary(Formula* f)
{
  Formula* newLeft = apply(f->left());
  Formula* newRight = apply(f->right());
  if(newLeft==f->left() && newRight==f->right()) {
    return f;
  }
  return new BinaryFormula(f->connective(), newLeft, newRight);
}

Formula* FormulaTransformer::applyQuantified(Formula* f)
{
  Formula* newArg = apply(f->qarg());
  if(newArg==f->qarg()) {
    return f;
  }
  // 0 is for the sorts list
  return new QuantifiedFormula(f->connective(), f->vars(),f->sorts(), newArg);
}

///////////////////////////////////////
// TermTransformingFormulaTransformer
//

Formula* TermTransformingFormulaTransformer::applyLiteral(Formula* f)
{
  Literal* lit = f->literal();
  Literal* res = _termTransformer.transformLiteral(lit);
  if(lit==res) { return f; }
  return new AtomicFormula(res);
}

///////////////////////////////////////
// TermTransformingFormulaTransformer
//

Formula* BottomUpTermTransformerFormulaTransformer::applyLiteral(Formula* f)
{
  Literal* lit = f->literal();
  Literal* res = _termTransformer.transformLiteral(lit);
  if(lit==res) { return f; }
  return new AtomicFormula(res);
}

////////////////////////////////////
// PolarityAwareFormulaTransformer
//

TermList PolarityAwareFormulaTransformer::getVarSort(unsigned var) const
{
  return _varSorts->get(var, AtomicSort::defaultSort());
}

Formula* PolarityAwareFormulaTransformer::transformWithPolarity(Formula* f, int polarity)
{
  ASS_REP(polarity==0 || polarity==1 || polarity==-1, polarity);

  _varSorts->reset();
  SortHelper::collectVariableSorts(f, *_varSorts);

  _polarity = polarity;
  return FormulaTransformer::transform(f);
}

Formula* PolarityAwareFormulaTransformer::applyNot(Formula* f)
{
  ScopedLet<int> plet(_polarity, -_polarity);
  return FormulaTransformer::applyNot(f);
}

Formula* PolarityAwareFormulaTransformer::applyImp(Formula* f)
{
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
  ASS(f->connective()==IFF || f->connective()==XOR);

  ScopedLet<int> plet(_polarity, 0);
  return FormulaTransformer::applyBinary(f);
}

///////////////////////////
// FormulaUnitTransformer
//

void FormulaUnitTransformer::transform(UnitList*& units)
{
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
  Formula* f = unit->formula();
  Formula* newForm = transform(f);
  if(f==newForm) {
    return unit;
  }
  return new FormulaUnit(newForm, FormulaTransformation(_rule, unit));
}


///////////////////////////////////////
// ScanAndApplyFormulaUnitTransformer
//

void ScanAndApplyFormulaUnitTransformer::apply(Problem& prb)
{
  if(apply(prb.units())) {
    updateModifiedProblem(prb);
  }
}

bool ScanAndApplyFormulaUnitTransformer::apply(UnitList*& units)
{
  scan(units);

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newUnit;

    if(!apply(u, newUnit)) {
      continue;
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

bool ScanAndApplyFormulaUnitTransformer::apply(Unit* u, Unit*& res)
{
  if(u->isClause()) {
    Clause* cl = static_cast<Clause*>(u);
    return apply(cl, res);
  }
  else {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    return apply(fu, res);
  }
}

void ScanAndApplyFormulaUnitTransformer::updateModifiedProblem(Problem& prb)
{
  prb.invalidateEverything();
}

}


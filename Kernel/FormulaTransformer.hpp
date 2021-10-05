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
 * @file FormulaTransformer.hpp
 * Defines class FormulaTransformer.
 */

#ifndef __FormulaTransformer__
#define __FormulaTransformer__

#include "Forwards.hpp"

#include "Inference.hpp"
#include "OperatorType.hpp"

namespace Kernel {

/**
 * A convenient base class for formula transforming classes.
 *
 * The default implementations of transformers for particular
 * connectives calls the "apply" function recursively and then
 * build a resulting formula, reusing old formula objects if
 * the recursive calls did not change their arguments.
 *
 * It also does flattening of AND and OR formulas, as well as of negations.
 */
class FormulaTransformer {
public:
  /**
   * This function is to be called from outside of the class to
   * transform formulas.
   */
  virtual Formula* transform(Formula* f);

protected:
  FormulaTransformer() {}
  virtual ~FormulaTransformer() {}

  Formula* apply(Formula* f);
  TermList apply(TermList ts);

  /** Return true if f should be traversed */
  virtual bool preApply(Formula*& f) { return true; }
  virtual void postApply(Formula* orig, Formula*& res) {}

  virtual Formula* applyLiteral(Formula* f) { return f; }

  virtual Formula* applyAnd(Formula* f) { return applyJunction(f); }
  virtual Formula* applyOr(Formula* f) { return applyJunction(f); }

  /** This function is called by applyAnd() and applyOr()
   * in their default implementation. */
  virtual Formula* applyJunction(Formula* f);

  virtual Formula* applyNot(Formula* f);

  virtual Formula* applyImp(Formula* f) { return applyBinary(f); }
  virtual Formula* applyIff(Formula* f) { return applyBinary(f); }
  virtual Formula* applyXor(Formula* f) { return applyBinary(f); }

  /** This function is called by applyImp(), applyIff()
   * and applyXor() in their default implementation. */
  virtual Formula* applyBinary(Formula* f);

  virtual Formula* applyForAll(Formula* f) { return applyQuantified(f); }
  virtual Formula* applyExists(Formula* f) { return applyQuantified(f); }

  /** This function is called by applyForAll() and applyExists()
   * in their default implementation. */
  virtual Formula* applyQuantified(Formula* f);


  virtual Formula* applyTrueFalse(Formula* f) { return f; }
};

class TermTransformingFormulaTransformer : public FormulaTransformer
{
public:
  TermTransformingFormulaTransformer(TermTransformer& termTransformer) : _termTransformer(termTransformer) {}
protected:
  virtual Formula* applyLiteral(Formula* f);

  TermTransformer& _termTransformer;
};

class TermTransformerTransformTransformedFormulaTransformer : public FormulaTransformer
{
  public:
    TermTransformerTransformTransformedFormulaTransformer(TermTransformerTransformTransformed& termTransformer)
      : _termTransformer(termTransformer) {}
  protected:
    virtual Formula* applyLiteral(Formula* f);

    TermTransformerTransformTransformed& _termTransformer;
};

class PolarityAwareFormulaTransformer : protected FormulaTransformer {
public:
  ~PolarityAwareFormulaTransformer();

  virtual Formula* transformWithPolarity(Formula* f, int polarity=1);
protected:
  PolarityAwareFormulaTransformer();

  virtual Formula* applyNot(Formula* f);

  virtual Formula* applyImp(Formula* f);

  virtual Formula* applyBinary(Formula* f);

  int polarity() const { return _polarity; }

  TermList getVarSort(unsigned var) const;

private:
  DHMap<unsigned,TermList>* _varSorts;
  int _polarity;
};

class FormulaUnitTransformer
{
public:
  virtual ~FormulaUnitTransformer() {}

  virtual FormulaUnit* transform(FormulaUnit* unit) = 0;

  void transform(UnitList*& units);
};


class LocalFormulaUnitTransformer : public FormulaUnitTransformer
{
public:
  LocalFormulaUnitTransformer(InferenceRule rule)
  : _rule(rule) {}

  using FormulaUnitTransformer::transform;

  virtual Formula* transform(Formula* f) = 0;

  virtual FormulaUnit* transform(FormulaUnit* unit);

private:
  InferenceRule _rule;
};

template<class FT>
class FTFormulaUnitTransformer : public LocalFormulaUnitTransformer
{
public:
  FTFormulaUnitTransformer(InferenceRule rule, FT& formulaTransformer)
  : LocalFormulaUnitTransformer(rule), _formulaTransformer(formulaTransformer) {}

  using LocalFormulaUnitTransformer::transform;

  virtual Formula* transform(Formula* f)
  {
    CALL("FTFormulaUnitTransformer::transform(Formula*)");
    return _formulaTransformer.transform(f);
  }

private:
  FT& _formulaTransformer;
};


class ScanAndApplyFormulaUnitTransformer {
public:
  virtual ~ScanAndApplyFormulaUnitTransformer() {}

  void apply(Problem& prb);
  bool apply(UnitList*& units);

  virtual void scan(UnitList* units) {}
  bool apply(Unit* u, Unit*& res);
  virtual UnitList* getIntroducedFormulas() { return 0; }

protected:
  virtual bool apply(FormulaUnit* unit, Unit*& res) {
    return false;
  }
  virtual bool apply(Clause* cl, Unit*& res) {
    return false;
  }

  virtual void updateModifiedProblem(Problem& prb);
};

class ScanAndApplyLiteralTransformer : public ScanAndApplyFormulaUnitTransformer {
public:
  using ScanAndApplyFormulaUnitTransformer::apply;
protected:

  /**
   * @param infRule the rule that will be used to derive modified units
   */
  ScanAndApplyLiteralTransformer(InferenceRule infRule) : _infRule(infRule) {}

  /**
   * @param l the literal
   * @param premAcc premises of the transformation should be added on this stack
   */
  virtual Literal* apply(Literal* l, UnitStack& premAcc) = 0;

  virtual bool apply(FormulaUnit* unit, Unit*& res);
  virtual bool apply(Clause* cl, Unit*& res);

private:
  struct LitFormulaTransformer;

  InferenceRule _infRule;
};


}

#endif // __FormulaTransformer__

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
 * @file SATInference.hpp
 * Defines class SATInference.
 */

#ifndef __SATInference__
#define __SATInference__

#include "Forwards.hpp"
#include "Lib/List.hpp"
#include "SATClause.hpp"

namespace Kernel {

using namespace SAT;

/**
 * During search (currently only GlobalSubsumption),
 * we may make an inference on the first-order level via SAT solving.
 *
 * We don't want to minimize the set of premises during search,
 * as we don't know whether they will be used in the proof or not.
 *
 * Therefore: use this object with a (large) superset of first-order
 * and SAT premises. Then, in Inference::minimizePremises,
 * minimize the SAT premises and use their parents to work out the true first-order parents.
 */
struct NeedsMinimization {
  /**
   * The inherited first order part (@b premises) must be already given,
   * but it is expected that it is much larger than necessary.
   *
   * A list of @b satPremises is just taken
   * (no memory responsibility overtaken; the list must survive till the minimization call),
   * a stack of @b usedAssumptions is copied.
   */
  NeedsMinimization(InferenceRule rule, UnitList* premises, SATClauseList* satPremises, const SATLiteralStack& usedAssumptions) :
    _rule(rule), _premises(premises), _satPremises(satPremises), _usedAssumptions(usedAssumptions) {}

  /**
   * Constructor versions with no assumptions.
   */
  NeedsMinimization(InferenceRule rule, UnitList* premises, SATClauseList* satPremises) :
      _rule(rule), _premises(premises), _satPremises(satPremises) {}

  InferenceRule _rule;
  // the first-order premises to be minimised
  UnitList* _premises;
  // the SAT premises that will be used to minimise them
  SATClauseList* _satPremises;
  // the SAT assumptions used, possibly empty
  SATLiteralStack _usedAssumptions;
};

}

namespace SAT {

using namespace Kernel;

class FOConversionInference;
class SATInference
{
public:
  enum InfType {
    PROP_INF,
    FO_CONVERSION
  };
  virtual ~SATInference() {}
  virtual InfType getType() const = 0;

  // assuming this is really a `FOConversionInference`, do the cast
  FOConversionInference *foConversion();

  /**
   * Call `receive` once for each FO_CONVERSION ancestor of `cl`.
   */
  template<typename Receiver>
  static void visitFOConversions(SATClause* cl, Receiver receive);

  /**
   * Collect first-order premises of `cl` into @c `acc` if they satisfy a filter `f`.
   */
  template <typename Filter>
  static void collectFilteredFOPremises(SATClause* cl, Stack<Unit*>& acc, Filter f);

  static UnitList *getFOPremises(SATClause *cl);
};

class PropInference : public SATInference
{
public:
  USE_ALLOCATOR(PropInference);

  PropInference(SATClauseList* premises) : _premises(premises) {}
  PropInference(SATClause* prem) : _premises(0)
  {
    SATClauseList::push(prem, _premises);
  }
  PropInference(SATClause* prem1, SATClause* prem2) : _premises(0)
  {
    SATClauseList::push(prem1, _premises);
    SATClauseList::push(prem2, _premises);
  }

  ~PropInference() override
  {
    SATClauseList::destroy(_premises);
  }

  InfType getType() const override { return PROP_INF; }
  SATClauseList* getPremises() const { return const_cast<SATClauseList*>(_premises); }
  void setPremises(SATClauseList* prems) { _premises = prems; }
private:
  SATClauseList* _premises;
};

class FOConversionInference : public SATInference
{
public:
  USE_ALLOCATOR(FOConversionInference);

  FOConversionInference(Unit* origin);
  FOConversionInference(Clause* cl);
  ~FOConversionInference() override;

  InfType getType() const override { return FO_CONVERSION; }
  Unit* getOrigin() const { return _origin; }
private:
  Unit* _origin;
};

inline FOConversionInference *SATInference::foConversion() {
  ASS_EQ(getType(), FO_CONVERSION)
  return static_cast<FOConversionInference *>(this);
}

template<typename Receiver>
void SATInference::visitFOConversions(SATClause* cl, Receiver receive)
{
  static Stack<SATClause*> toDo;
  static DHSet<SATClause*> seen;
  toDo.reset();
  seen.reset();

  toDo.push(cl);
  while (toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if (!seen.insert(cur))
      continue;

    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      receive(cur);
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    }
  }
}

template <typename Filter>
void SATInference::collectFilteredFOPremises(SATClause* cl, Stack<Unit*>& acc, Filter f) {
  visitFOConversions(cl, [&](SATClause *cl) {
    if(!f(cl))
      return;
    acc.push(cl->inference()->foConversion()->getOrigin());
  });
}

inline UnitList *SATInference::getFOPremises(SATClause *cl) {
  UnitList *result = nullptr;
  SATInference::visitFOConversions(cl, [&result](SATClause *cl) {
    UnitList::push(cl->inference()->foConversion()->getOrigin(), result);
  });
  return result;
}

}

#endif // __SATInference__

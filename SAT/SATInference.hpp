
/*
 * File SATInference.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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

namespace SAT {

using namespace Kernel;

class SATInference
{
public:
  enum InfType {
    PROP_INF,
    FO_CONVERSION,
    ASSUMPTION
  };
  virtual ~SATInference() {}
  virtual InfType getType() const = 0;
  
  template <typename Filter>
  static void collectFilteredFOPremises(SATClause* cl, Stack<Unit*>& acc, Filter f);
  
  static void collectFOPremises(SATClause* cl, Stack<Unit*>& acc);

  static void collectPropAxioms(SATClause* cl, SATClauseStack& res);

  static UnitList* getFOPremises(SATClause* cl);
  static SATInference* copy(const SATInference* inf);
};

class PropInference : public SATInference
{
public:
  CLASS_NAME(PropInference);
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

  ~PropInference()
  {
    SATClauseList::destroy(_premises);
  }

  virtual InfType getType() const { return PROP_INF; }
  SATClauseList* getPremises() const { return const_cast<SATClauseList*>(_premises); }
  void setPremises(SATClauseList* prems) { _premises = prems; }
private:
  SATClauseList* _premises;
};

class FOConversionInference : public SATInference
{
public:
  CLASS_NAME(FOConversionInference);
  USE_ALLOCATOR(FOConversionInference);

  FOConversionInference(Unit* origin);
  FOConversionInference(Clause* cl);
  ~FOConversionInference();

  virtual InfType getType() const { return FO_CONVERSION; }
  Unit* getOrigin() const { return _origin; }
private:
  Unit* _origin;
};

class AssumptionInference : public SATInference
{
public:
  CLASS_NAME(AssumptionInference);
  USE_ALLOCATOR(AssumptionInference);

  virtual InfType getType() const { return ASSUMPTION; }
};

/**
 * A first order inference coming from a SAT refutation.
 * Possibly the SAT refutation was unnecessarily too large
 * and may be minimized before the final proof outputting.
 */
class InferenceFromSatRefutation : public Kernel::InferenceMany
{
public:
  /**
   * The inherited first order part (@b premises) must be already given,
   * but it is expected that it is much larger than necessary.
   *
   * A list of @b satPremises is just taken
   * (no memory responsibility overtaken; the list must survive till the minimization call),
   * a stack of @b usedAssumptions is copied.
   */
  InferenceFromSatRefutation(Rule rule, UnitList* premises, SATClauseList* satPremises, const SATLiteralStack& usedAssumptions) :
    InferenceMany(rule,premises), _minimized(!env.options->minimizeSatProofs()), _satPremises(satPremises), _usedAssumptions(usedAssumptions) {}

  /**
   * Constructor versions with no assumptions.
   */
  InferenceFromSatRefutation(Rule rule, UnitList* premises, SATClauseList* satPremises) :
      InferenceMany(rule,premises), _minimized(!env.options->minimizeSatProofs()), _satPremises(satPremises) {}

  virtual SATClauseList* minimizePremises() override;

  CLASS_NAME(InferenceFromSatRefutation);
  USE_ALLOCATOR(InferenceFromSatRefutation);

protected:
  bool _minimized;
  SATClauseList* _satPremises;
  SATLiteralStack _usedAssumptions;
};


/**
 * Collect first-order premises of @c cl into @c res. Make sure that elements in @c res are unique.
 * Only consider those SATClauses and their parents which pass the given Filter f.
 */
template <typename Filter>
void SATInference::collectFilteredFOPremises(SATClause* cl, Stack<Unit*>& acc, Filter f)
{
  CALL("SATInference::collectFilteredFOPremises");
  ASS_ALLOC_TYPE(cl, "SATClause");

  static Stack<SATClause*> toDo;
  static DHSet<SATClause*> seen;
  toDo.reset();
  seen.reset();

  toDo.push(cl);
  while (toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if (!f(cur)) {
      continue;
    }    
    if (!seen.insert(cur)) {
      continue;
    }
    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      acc.push(static_cast<FOConversionInference*>(sinf)->getOrigin());
      break;
    case SATInference::ASSUMPTION:
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }
  makeUnique(acc);
}



}

#endif // __SATInference__

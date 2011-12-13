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
    FO_SPLITTING,
    ASSUMPTION
  };
  virtual ~SATInference() {}
  virtual InfType getType() const = 0;

  static UnitList* getFOPremises(SATClause* cl);
};

class PropInference : public SATInference
{
public:
  CLASS_NAME("PropInference");
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
    _premises->destroy();
  }

  virtual InfType getType() const { return PROP_INF; }
  SATClauseList* getPremises() const { return const_cast<SATClauseList*>(_premises); }
private:
  SATClauseList* _premises;
};

class FOConversionInference : public SATInference
{
public:
  CLASS_NAME("FOConversionInference");
  USE_ALLOCATOR(FOConversionInference);

  FOConversionInference(UnitSpec origin);
  FOConversionInference(Clause* cl);
  ~FOConversionInference();

  virtual InfType getType() const { return FO_CONVERSION; }
  UnitSpec getOrigin() const { return _origin; }
private:
  UnitSpec _origin;
};

class FOSplittingInference : public SATInference
{
public:
  CLASS_NAME("FOSplittingInference");
  USE_ALLOCATOR(FOSplittingInference);

  FOSplittingInference(Clause* origin, ClauseList* names);
  ~FOSplittingInference();

  virtual InfType getType() const { return FO_SPLITTING; }
  Clause* getOrigin() const { return _origin; }
  ClauseList* getNames() const { return _names; }
private:
  Clause* _origin;
  ClauseList* _names;
};

class AssumptionInference : public SATInference
{
public:
  CLASS_NAME("AssumptionInference");
  USE_ALLOCATOR(AssumptionInference);

  virtual InfType getType() const { return ASSUMPTION; }
};

}

#endif // __SATInference__

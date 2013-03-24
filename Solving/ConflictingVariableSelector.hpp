/**
 * @file ConflictingVariableSelector.hpp
 * Defines class ConflictingVariableSelector.
 */

#ifndef __ConflictingVariableSelector__
#define __ConflictingVariableSelector__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/Event.hpp"

#include "VariableSelector.hpp"

namespace Solving {

using namespace Lib;
using namespace Kernel;

class ConflictAwareVariableSelector : public VariableSelector
{
protected:
  ConflictAwareVariableSelector(Solver& s);

  virtual void onConflict(Var v, Constraint* constr) = 0;
private:
  void conflictHandler(Var v, Constraint* constr);

  SubscriptionData _onConflictSD;
};


class ConflictingVariableSelector : public ConflictAwareVariableSelector
{
public:
  ConflictingVariableSelector(Solver& s, bool considerCollapsing);

  virtual Var getNextVariable();

protected:
  virtual void onConflict(Var v, Constraint* constr);
private:
  struct VarStats
  {
    VarStats() : _conflictCnt(0), _conflictCollapsingClauseAppearances(0) {}
    unsigned _conflictCnt;
    unsigned _conflictCollapsingClauseAppearances;
  };

  bool secondIsBetter(Var v1, Var v2);

  bool _considerCollapsing;
  DArray<VarStats> _varStats;
};

class RecentlyConflictingVariableSelector : public ConflictAwareVariableSelector
{
public:
  RecentlyConflictingVariableSelector(Solver& s, bool considerCollapsing);

  virtual Var getNextVariable();

protected:
  virtual void onConflict(Var v, Constraint* constr);
private:

  void makeRecent(Var v);

  static const Var VAR_NIL;

  struct VarEntry
  {
    Var _next;
    Var _prev;
  };

  bool _considerCollapsing;
  Var _first;
  DArray<VarEntry> _varList;
};

//TODO add documentation to this class
class VSIDSVariableSelector : public ConflictAwareVariableSelector{
public:
  VSIDSVariableSelector(Solver& s, unsigned iterationsToDecay);
  virtual Var getNextVariable();
protected:
  virtual void onConflict(Var v, Constraint* constr);
private:
  unsigned _iterationToDecay;
  struct VarEntry{
    VarEntry() : _conflictCount(0),_conflictCollapsingAppearenceCount(0){}
    unsigned _conflictCount;
    unsigned _conflictCollapsingAppearenceCount;
  };
  DArray<VarEntry> _varList;
  DArray<Var> _orderList;
};
}
#endif //GNUMP
#endif // __ConflictingVariableSelector__

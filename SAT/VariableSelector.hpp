/**
 * @file VariableSelector.hpp
 * Defines class VariableSelector.
 */

#ifndef __VariableSelector__
#define __VariableSelector__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DynamicHeap.hpp"
#include "Lib/Int.hpp"

namespace SAT {

class VariableSelector {
public:
  VariableSelector(TWLSolver& solver) : _solver(solver) {}

  /**
   * If possible, assign @c var to be the variable of the next decision point
   * and return true. Otherwise (when there are no more unassigned variables)
   * return false.
   */
  virtual bool selectVariable(unsigned& var) = 0;

  virtual void ensureVarCnt(unsigned varCnt) { _varCnt = varCnt; }
  virtual void onVariableInConflict(unsigned var) {}
  virtual void onVariableUnassigned(unsigned var) {}
  virtual void onConflict() {}
  virtual void onInputClauseAdded(SATClause* cl) {}
  virtual void onRestart() {}

protected:
  bool isUndefined(unsigned var);

  unsigned _varCnt;
  TWLSolver& _solver;
};

class ActiveVariableSelector : public VariableSelector{
public:
  ActiveVariableSelector(TWLSolver& solver) : VariableSelector(solver) {}

  virtual bool selectVariable(unsigned& var);
  virtual void ensureVarCnt(unsigned varCnt);
  virtual void onInputClauseAdded(SATClause* cl);

  virtual void onVariableInConflict(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableInConflict");

    _activityHeap.markActivity(var);
  }

  virtual void onVariableUnassigned(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableUnassigned");

    _activityHeap.ensureIncluded(var);
  }

  virtual void onConflict()
  {
    CALL("ActiveVariableSelector::onConflict");

    _activityHeap.decay();
  }
protected:
  typedef size_t ActivityCounter;
  typedef float CounterType;

  class VariableActivityHeap
  {
    VariableActivityHeap(const VariableActivityHeap&);
    VariableActivityHeap& operator=(const VariableActivityHeap&);
  public:
    VariableActivityHeap(CounterType decayFactor = 1.05f)
    : _decayFactor(decayFactor), _inc(1e-30f), _heap(VAComparator(_activities)) {}

    void ensureVarCnt(unsigned varCnt)
    {
      unsigned oldVarCnt = _activities.size();
      _activities.expand(varCnt, 0);
      _heap.elMap().expand(varCnt);

      for(unsigned i=oldVarCnt; i<varCnt; i++) {
	ensureIncluded(i);
      }
    }

    void markActivity(unsigned var)
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::markActivity");

      _activities[var]+=_inc;
      if(_heap.contains(var)) {
	_heap.notifyDecrease(var);
      }
    }

    void decay()
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::decay");

      _inc*=_decayFactor;
      if(_inc>1e30f) {
	_inc = 1.0f;
	unsigned varCnt = _activities.size();
	for(unsigned i=0; i<varCnt; i++) {
	  _activities[i]/=1e30f;
	}
      }
    }

    unsigned popMostActive()
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::popMostActive");

      return _heap.pop();
    }

    void ensureIncluded(unsigned var)
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::ensureIncluded");

      if(!_heap.contains(var)) {
	_heap.insert(var);
      }
    }

    bool isEmpty() { return _heap.isEmpty(); }
  private:
    typedef DArray<CounterType> CounterArr;
    struct VAComparator
    {
      VAComparator(CounterArr& ctr) : _ctr(ctr) {}

      Comparison compare(unsigned v1, unsigned v2)
      {
	//DynamicHeap is minimal and we want maximum, so we need to swap
	//the arguments
	return Int::compare(_ctr[v2], _ctr[v1]);
      }
      CounterArr& _ctr;
    };


    CounterType _decayFactor;
    CounterType _inc;
    CounterArr _activities;
    DynamicHeap<unsigned, VAComparator, ArrayMap<size_t> > _heap;
  };

  VariableActivityHeap _activityHeap;
};

/**
 * Active variable selector based on an array instead of a heap
 */
class ArrayActiveVariableSelector : public VariableSelector {
public:
  ArrayActiveVariableSelector(TWLSolver& solver) : VariableSelector(solver) {}

  virtual bool selectVariable(unsigned& var);

  virtual void ensureVarCnt(unsigned varCnt)
  {
    VariableSelector::ensureVarCnt(varCnt);
    _activities.expand(varCnt, 0);
  }

  virtual void onInputClauseAdded(SATClause* cl);

  virtual void onVariableInConflict(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableInConflict");
    _activities[var]++;
  }

  virtual void onRestart();
protected:
  typedef size_t ActivityCounter;

  DArray<ActivityCounter> _activities;
};

/**
 * Variable selector that tries to select the most active
 * variable from the a most recently learned unsatisfied clause.
 */
class RLCVariableSelector : public ArrayActiveVariableSelector {
public:
  RLCVariableSelector(TWLSolver& solver) : ArrayActiveVariableSelector(solver) {}

  virtual bool selectVariable(unsigned& var);
};

}

#endif // __VariableSelector__

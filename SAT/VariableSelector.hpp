
/*
 * File VariableSelector.hpp.
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
 * @file SAT/VariableSelector.hpp
 * Defines class VariableSelector.
 */

#ifndef __VariableSelector__
#define __VariableSelector__

#include "Forwards.hpp"

#include "Shell/Options.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DynamicHeap.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedPtr.hpp"

namespace SAT {

using namespace Shell;

class VariableSelector
{
public:
  CLASS_NAME(VariableSelector);
  USE_ALLOCATOR(VariableSelector);

  VariableSelector(TWLSolver& solver) : _solver(solver) {}
  virtual ~VariableSelector() {}

  /**
   * If possible, assign @c var to be the variable of the next decision point
   * and return true. Otherwise (when there are no more unassigned variables)
   * return false.
   */
  virtual bool selectVariable(unsigned& var) = 0;

  virtual void ensureVarCount(unsigned varCnt) { _varCnt = varCnt; }
  virtual void onVariableInConflict(unsigned var) {}
  virtual void onVariableUnassigned(unsigned var) {}
  virtual void onConflict() {}
  virtual void onInputClauseAdded(SATClause* cl) {}
  virtual void onRestart() {}
  virtual void recordSource(unsigned satlit, Literal* lit) {}

protected:
  bool isUndefined(unsigned var);

  unsigned _varCnt;
  TWLSolver& _solver;
};

class AlternatingVariableSelector : public VariableSelector
{
public:
  CLASS_NAME(AlternatingVariableSelector);
  USE_ALLOCATOR(AlternatingVariableSelector);

  AlternatingVariableSelector(TWLSolver& solver, VariableSelector* s1, VariableSelector* s2)
   : VariableSelector(solver) {
    CALL("AlternatingVariableSelector::AlternatingVariableSelector");

    _sels[0] = s1;
    _sels[1] = s2;
    _ctr = 0;
  }

  virtual bool selectVariable(unsigned& var) {
    return _sels[_ctr%4==0]->selectVariable(var);
  }

  virtual void ensureVarCount(unsigned varCnt) {
    CALL("AlternatingVariableSelector::ensureVarCount");

    VariableSelector::ensureVarCount(varCnt);
    _sels[0]->ensureVarCount(varCnt);
    _sels[1]->ensureVarCount(varCnt);
  }

  virtual void onVariableInConflict(unsigned var) {
    _sels[0]->onVariableInConflict(var);
    _sels[1]->onVariableInConflict(var);
  }

  virtual void onVariableUnassigned(unsigned var) {
    _sels[0]->onVariableUnassigned(var);
    _sels[1]->onVariableUnassigned(var);
  }

  virtual void onConflict() {
    _sels[0]->onConflict();
    _sels[1]->onConflict();
  }

  virtual void onInputClauseAdded(SATClause* cl) {
    _sels[0]->onInputClauseAdded(cl);
    _sels[1]->onInputClauseAdded(cl);
  }

  virtual void onRestart() {
    _sels[0]->onRestart();
    _sels[1]->onRestart();
    _ctr++;
  }

private:
  int _ctr;
  VariableSelectorSCP _sels[2];
};

class ActiveVariableSelector : public VariableSelector
{
public:
  CLASS_NAME(ActiveVariableSelector);
  USE_ALLOCATOR(ActiveVariableSelector);

  typedef double CounterType;

  // decayFactor default previously 1.05
  ActiveVariableSelector(TWLSolver& solver, Options::Niceness niceness_option, CounterType decayFactor) : 
	VariableSelector(solver), _niceness_option(niceness_option),
        _activityHeap(decayFactor,(niceness_option!=Options::Niceness::NONE),*this) {}

  virtual bool selectVariable(unsigned& var);
  virtual void ensureVarCount(unsigned varCnt);
  virtual void onInputClauseAdded(SATClause* cl);

  virtual void onVariableInConflict(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableInConflict");

    ASS_G(var,0); ASS_LE(var,_varCnt);

    _activityHeap.markActivity(var);
  }

  virtual void onVariableUnassigned(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableUnassigned");

    ASS_G(var,0); ASS_LE(var,_varCnt);

    _activityHeap.ensureIncluded(var);
  }

  virtual void onConflict()
  {
    CALL("ActiveVariableSelector::onConflict");

    _activityHeap.decay();
  }

  virtual void recordSource(unsigned satlit, Literal* lit)
  {
    CALL("ActiveVaraibleSelector::recordSource");
    _sourceMap.insert(satlit,lit);
  }

protected:

  class VariableActivityHeap
  {
    VariableActivityHeap(const VariableActivityHeap&);
    VariableActivityHeap& operator=(const VariableActivityHeap&);
  public:
    VariableActivityHeap(CounterType decayFactor, bool use_niceness, ActiveVariableSelector& parent)
    : _use_niceness(use_niceness), _parent(parent), _decayFactor(decayFactor),
      _inc(1e-30f), _heap(VAComparator(_activities)) {}

    void ensureVarCount(unsigned varCnt)
    {
      unsigned oldVarCnt = _activities.size();
      if (oldVarCnt == 0) { // ignore the unused variable 0
        oldVarCnt = 1;
      }

      _activities.expand(varCnt+1, 0);
      _heap.elMap().expand(varCnt+1);

      for(unsigned i=oldVarCnt; i<=varCnt; i++) {
	ensureIncluded(i);
      }
    }

    void markActivity(unsigned var)
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::markActivity");
      ASS_G(var,0);

      CounterType this_inc = _inc;
      if(_use_niceness){
        this_inc *= _parent._niceness[var];
      }
      _activities[var]+=this_inc;
      if(_heap.contains(var)) {
	_heap.notifyDecrease(var);
      }
    }

    void decay()
    {
      CALL("ActiveVariableSelector::VariableActivityHeap::decay");

//      cout<<_inc<<endl;
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
      ASS_G(var,0);

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


    bool _use_niceness;
    ActiveVariableSelector& _parent;

    CounterType _decayFactor;
    CounterType _inc;
    CounterArr _activities;
    DynamicHeap<unsigned, VAComparator, ArrayMap<size_t> > _heap;
  };

  unsigned getNiceness(unsigned var);

  Options::Niceness _niceness_option;
  //Has initial size 0
  DArray<unsigned> _niceness;
  DHMap<unsigned,Literal*> _sourceMap;
  VariableActivityHeap _activityHeap;
};

/**
 * Active variable selector based on an array instead of a heap
 */
class ArrayActiveVariableSelector : public VariableSelector {
public:
  CLASS_NAME(ArrayActiveVariableSelector);
  USE_ALLOCATOR(ArrayActiveVariableSelector);

  ArrayActiveVariableSelector(TWLSolver& solver) : VariableSelector(solver) {}

  virtual bool selectVariable(unsigned& var);

  virtual void ensureVarCount(unsigned varCnt)
  {
    VariableSelector::ensureVarCount(varCnt);
    _activities.expand(varCnt+1, 0);
  }

  virtual void onInputClauseAdded(SATClause* cl);

  virtual void onVariableInConflict(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableInConflict");

    ASS_G(var,0); ASS_LE(var,_varCnt);

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
  CLASS_NAME(RLCVariableSelector);
  USE_ALLOCATOR(RLCVariableSelector);

  RLCVariableSelector(TWLSolver& solver) : ArrayActiveVariableSelector(solver) {}

  virtual bool selectVariable(unsigned& var);
};


/**
 * Variable selector that uses increments using niceness on conflict
 * TODO - does not use niceness options, uses default
 */
class ArrayNicenessVariableSelector : public ArrayActiveVariableSelector {
public:
  CLASS_NAME(ArrayNicenessVariableSelector);
  USE_ALLOCATOR(ArrayNicenessVariableSelector);

  ArrayNicenessVariableSelector(TWLSolver& solver) : ArrayActiveVariableSelector(solver) {}


  virtual void onVariableInConflict(unsigned var)
  {
    CALL("ActiveVariableSelector::onVariableInConflict");

    ASS_G(var,0); ASS_LE(var,_varCnt);

    _activities[var]+=_niceness[var];
  }

  virtual void onInputClauseAdded(SATClause* cl);

  virtual void ensureVarCount(unsigned varCnt)
  {
    ArrayActiveVariableSelector::ensureVarCount(varCnt);
    _niceness.expand(varCnt+1, 0);
  }

private:
  DArray<unsigned> _niceness;
};

}
#endif // __VariableSelector__


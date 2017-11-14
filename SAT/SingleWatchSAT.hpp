
/*
 * File SingleWatchSAT.hpp.
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
 * @file SingleWatchSAT.hpp
 * Defines class SingleWatchSAT.
 */


#ifndef __SingleWatchSAT__
#define __SingleWatchSAT__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Lib/Int.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/BucketSorter.hpp"

#include "SATClause.hpp"

namespace SAT {

class SingleWatchSAT
{
public:
  /** termination reason */
  enum TerminationReason {
    /** refutation found */
    REFUTATION,
    /** satisfiability detected */
    SATISFIABLE,
    /** time limit reached */
    TIME_LIMIT,
    /** memory limit reached */
    MEMORY_LIMIT
  };

  SingleWatchSAT(unsigned varCnt);
  ~SingleWatchSAT();

  bool loadClauses(SATClauseIterator clauses);
  void satisfy(int timeLimit=0);
  void reset();

  SATClauseIterator learntClauses();

  SATClause* refutation;
  TerminationReason termination;

//private:
  bool earlyTermination();

  void nextTimeStamp()
  {
    _currTimeStamp++;
    if(_currTimeStamp==0xFFFFFFFF) {
      resetTimeStamp();
    }
  }

  void resetTimeStamp();
  int evalTail(SATClause* cl);
  SATClause* resolveClauses(SATClause* c1, SATClause* c2);
  void incorporate(SATClause* cl);


  typedef DArray<SATClause*> ClauseArray;

  unsigned _currTimeStamp;
  unsigned _varCnt;

  DArray<bool> _asgnVals;

  struct LevelInfo
  {
    LevelInfo() { reset(); }
    void reset()
    {
      resetTimeStamp();
      determinant=0;
    }
    void resetTimeStamp()
    {
      visitTime=0xFFFFFFFF;
      changeTime=0xFFFFFFFF;
      determiningTime=0xFFFFFFFF;
    }
    unsigned visitTime;
    unsigned changeTime;
    unsigned determiningTime;
    SATClause* determinant;
  };
  DArray<LevelInfo> _levelInfos;
  DArray<unsigned> _conflicts;

  typedef Stack<SATClause*> ClauseStack;

  ClauseStack* _watched;
  ClauseStack* _reeval;
  ClauseStack _unitClauses;


  bool isDetermined(unsigned var)
  {
    SATClause* determinant=_levelInfos[var].determinant;
    if(!determinant) {
      return false;
    }
    if(determinant->length()==1) {
      return true;
    }
    unsigned determiningLevel=(*determinant)[1].var();
    if(determiningLevel>_level) {
      return false;
    }
    return _levelInfos[var].determiningTime>=_levelInfos[determiningLevel].visitTime;
  }

  SATClause* handleUnitConflict(SATClause* cl);
  void performDetermination(SATClause* cl);

  void putForReevaluation(SATClause* cl);

  unsigned _level;
  unsigned _lowestUnevaluated;
  int _startTime;
  int _timeLimit;
  int _unusedRemovalCnt;
};

};

#endif /* __SingleWatchSAT__ */

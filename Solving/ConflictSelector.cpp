/**
 * @file ConflictSelector.cpp
 * Implements class ConflictSelector.
 */
#if GNUMP
#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Solver.hpp"

#include "ConflictSelector.hpp"


#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Shell;

ConflictSelector::ConflictSelector(Solver& s)
 : _solver(s), _bounds(s.getBounds())
{
  CALL("ConflictSelector::ConflictSelector");
}

void ConflictSelector::getConflictIndexes(Var v, size_t& left, size_t& right)
{
  CALL("ConflictSelector::getConflictIndexes");

  BoundStack& leftBounds = _bounds.getBounds(BoundId(v, true));
  ASS(&leftBounds);	//when we have a conflict, there must be some bounds
  BoundStack& rightBounds = _bounds.getBounds(BoundId(v, false));
  ASS(&rightBounds);	//when we have a conflict, there must be some bounds
  ASS(leftBounds.top().hasConflictWith(rightBounds.top(), true));
  getConflictIndexes(v, leftBounds, rightBounds, left, right);
  ASS(leftBounds[left].hasConflictWith(rightBounds[right], true));

  if(left!=leftBounds.size()-1 || right!=rightBounds.size()-1) {
    _solver.getStats().nonRecentConflicts++;
  }
}

class MostRecentConflictSelector : public ConflictSelector {
public:
  MostRecentConflictSelector(Solver& s) : ConflictSelector(s) {}

protected:
  virtual void getConflictIndexes(Var v, const BoundStack& leftBounds,
      const BoundStack& rightBounds, size_t& left, size_t& right)
  {
    CALL("MostRecentConflictSelector::getConflictIndexes");

    left = leftBounds.size()-1;
    right = rightBounds.size()-1;
  }
};

class TooEarlyConflictSelector : public ConflictSelector {
public:
  TooEarlyConflictSelector(Solver& s) : ConflictSelector(s) {}

protected:
  virtual void getConflictIndexes(Var v, const BoundStack& leftBounds,
      const BoundStack& rightBounds, size_t& left, size_t& right)
  {
    CALL("TooEarlyConflictSelector::getConflictIndexes");

    size_t curLeft = leftBounds.size()-1;
    size_t curRight = rightBounds.size()-1;
    LOG("tkv_conflict","Conflict selection for "<<env.signature->varName(v));
    while(curLeft>0 && leftBounds[curLeft-1].hasConflictWith(rightBounds[curRight], true)) {
    TRACE("tkv_conflict",tout<<"Skipping left bound "<<leftBounds[curLeft].value()<<" justified by "
	<<(leftBounds[curLeft].justification().parent()?leftBounds[curLeft].justification().parent()->toString():string("<decision point>")););
      curLeft--;
    }
    TRACE("tkv_conflict",tout<<"Selecting left bound "<<leftBounds[curLeft].value()<<" justified by "
	<<(leftBounds[curLeft].justification().parent()?leftBounds[curLeft].justification().parent()->toString():string("<decision point>")););
    while(curRight>0 && leftBounds[curLeft].hasConflictWith(rightBounds[curRight-1], true)) {
    TRACE("tkv_conflict",tout<<"Skipping right bound "<<rightBounds[curRight].value()<<" justified by "
	<<(rightBounds[curRight].justification().parent()?rightBounds[curRight].justification().parent()->toString():string("<decision point>")););
      curRight--;
    }
    TRACE("tkv_conflict",tout<<"Selecting right bound "<<rightBounds[curRight].value()<<" justified by "
	<<(rightBounds[curRight].justification().parent()?rightBounds[curRight].justification().parent()->toString():string("<decision point>")););
    left = curLeft;
    right = curRight;
  }
};


class GoodConflictSelector : public ConflictSelector {
public:
  GoodConflictSelector(Solver& s) : ConflictSelector(s) {}

protected:
  typedef int Goodness;

  virtual Goodness getGoodness(Var v, size_t left, size_t right, const BoundStack& leftBounds,
      const BoundStack& rightBounds) = 0;

  virtual void getConflictIndexes(Var v, const BoundStack& leftBounds,
      const BoundStack& rightBounds, size_t& left, size_t& right)
  {
    CALL("GoodConflictSelector::getConflictIndexes");

    size_t curLeft = leftBounds.size()-1;
    size_t curRight = rightBounds.size()-1;
    bool onlyCandidate = true;
    size_t bestLeft = curLeft;
    size_t bestRight = curRight;
    Goodness bestGoodness; //we evaluate the goodness of candidates only if there are more than one

    LOG("tkv_conflict","Conflict selection for "<<env.signature->varName(v));
    while(curLeft>0 && leftBounds[curLeft-1].hasConflictWith(rightBounds[curRight], true) && leftBounds[curLeft].justification().parent()) {
      if(onlyCandidate) {
	bestGoodness = getGoodness(v, bestLeft, bestRight, leftBounds, rightBounds);
	onlyCandidate = false;
      }
    TRACE("tkv_conflict",tout<<"Skipping left bound "<<leftBounds[curLeft].value()<<" justified by "
	<<(leftBounds[curLeft].justification().parent()?leftBounds[curLeft].justification().parent()->toString():string("<decision point>")););
      curLeft--;
      Goodness curGoodness = getGoodness(v, curLeft, curRight, leftBounds, rightBounds);
      if(curGoodness>bestGoodness) {
	bestGoodness = curGoodness;
	bestLeft = curLeft;
	bestRight = curRight;
      }
    }
    TRACE("tkv_conflict",tout<<"Selecting left bound "<<leftBounds[curLeft].value()<<" justified by "
	  <<(leftBounds[curLeft].justification().parent()?leftBounds[curLeft].justification().parent()->toString():string("<decision point>")););
    while(curRight>0 && leftBounds[curLeft].hasConflictWith(rightBounds[curRight-1], true) && rightBounds[curRight].justification().parent()) {
      //If we can go to earlier right bounds, left bound must have been the
      //one whose adding caused conflict (so we could not have gone to earlier
      //bounds on the left side).
      //This is possible to assume only becase we stop the bound propagation
      //immediately after deriving a conflict.
      ASS_EQ(curLeft, leftBounds.size()-1);
      if(onlyCandidate) {
	bestGoodness = getGoodness(v, bestLeft, bestRight, leftBounds, rightBounds);
	onlyCandidate = false;
      }
      TRACE("tkv_conflict",tout<<"Skipping right bound "<<rightBounds[curRight].value()<<" justified by "
	  <<(rightBounds[curRight].justification().parent()?rightBounds[curRight].justification().parent()->toString():string("<decision point>")););
      curRight--;
      Goodness curGoodness = getGoodness(v, curLeft, curRight, leftBounds, rightBounds);
      if(curGoodness>bestGoodness) {
	bestGoodness = curGoodness;
	bestLeft = curLeft;
	bestRight = curRight;
      }
    }
    TRACE("tkv_conflict",tout<<"Selecting right bound "<<rightBounds[curRight].value()<<" justified by "
	  <<(rightBounds[curRight].justification().parent()?rightBounds[curRight].justification().parent()->toString():string("<decision point>")););
    left = bestLeft;
    right = bestRight;
  }
};

class LeastRecentConflictSelector : public GoodConflictSelector {
public:
  LeastRecentConflictSelector(Solver& s) : GoodConflictSelector(s) {}

protected:
  virtual Goodness getGoodness(Var v, size_t left, size_t right, const BoundStack& leftBounds,
      const BoundStack& rightBounds)
  {
    CALL("LeastRecentConflictSelector::getGoodness");

    return -left-right;
  }
};

class ShortestConstraintConflictSelector : public GoodConflictSelector {
public:
  ShortestConstraintConflictSelector(Solver& s) : GoodConflictSelector(s) {}

protected:
  virtual Goodness getGoodness(Var v, size_t left, size_t right, const BoundStack& leftBounds,
      const BoundStack& rightBounds)
  {
    CALL("ShortestConstraintConflictSelector::getGoodness");

    ConstraintRCPtr conf;
    _bounds.getConflictCollapsingInequality(v, left, right, conf);
    Goodness res = conf->coeffCnt();
//    cout<<env.signature->varName(v)<<": "<<res<<endl;
    return res;
  }
};

ConflictSelector* ConflictSelector::create(Solver& s, Options& opt)
{
  CALL("ConflictSelector::create");

  ConflictSelector* res;
  switch(opt.conflictSelector()) {
  case Options::CS_LEAST_RECENT:
    res = new LeastRecentConflictSelector(s);
//    res = new TooEarlyConflictSelector(s);
    break;
  case Options::CS_MOST_RECENT:
    res = new MostRecentConflictSelector(s);
    break;
  case Options::CS_SHORTEST_CONSTRAINT:
    res = new ShortestConstraintConflictSelector(s);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  return res;
}

}
#endif //GNUMP

/**
 * @file BoundsArray.hpp
 * Defines class BoundsArray.
 */

#ifndef __BoundsArray__
#define __BoundsArray__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/DArray.hpp"

#include "Lib/Deque.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/RCPtr.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Number.hpp"

#include "ConflictSelector.hpp"

namespace Solving {

using namespace Lib;
using namespace Kernel;

/**
 * Result of bound suggestion or bound propagation.
 *
 * It holds that greater values stand for greater impact
 * (BS_NONE < BS_IMPROVEMENT < BS_CONFLICT)
 */
enum BoundSuggestionResult
{
  /** The suggested bound is subsumed by a bound that is already present */
  BS_NONE = 0,
  /** The suggested bound improved the current bound */
  BS_IMPROVEMENT = 1,
  /** The suggested bound caused a conflict */
  BS_CONFLICT = 2
};

class BoundJustification
{
  friend class BoundsArray;
public:
  struct BoundSpec {
    BoundSpec() {}
    BoundSpec(const BoundId& b, size_t boundIndex) : bound(b), boundIndex(boundIndex) {}

    BoundId bound;
    size_t boundIndex;
  };
  typedef DArray<BoundSpec> BoundSpecArray;

  BoundJustification() : _propagatedBounds(0) {}
  BoundJustification(const BoundJustification& j);
  BoundJustification& operator=(const BoundJustification& j);

  Constraint* parent() const { return _parent.ptr(); }
  void setParent(Constraint* p) { _parent = p; }

  const BoundSpecArray& propagatedBounds() const { return _propagatedBounds; }

  template<class Iter>
  void initPropagatedBounds(Iter boundSpecIt) {
    CALL("BoundJustification::initPropagatedBounds");
    _propagatedBounds.initFromIterator(boundSpecIt);
  }

  string toString(const BoundsArray& bounds) const;

private:
  ConstraintRCPtr _parent;
  BoundSpecArray _propagatedBounds;
};

class BoundInfo
{
  friend class BoundsArray;
public:
  BoundInfo() : _depth(-1), _cachedCollapsingInequality(0) {}
  BoundInfo(BoundNumber val, bool strict)
   : _value(val), _strict(strict), _depth(-1) {}
  BoundInfo(BoundNumber val, bool strict, const BoundJustification& justification)
   : _value(val), _strict(strict), _depth(-1), _justification(justification) {}

  const BoundNumber & value() const { return _value; }
  bool strict() const { return _strict; }

  void setValue(const BoundNumber& val) { _value = val; }
  void setStrict(bool s) { _strict = s; }

  /**
   * Return true if the depth value was assigned to for this object
   *
   * Depth value is assigned upon insertion into the @b BoundsArray object.
   */
  bool hasDepthAssigned() const { ASS_GE(_depth,-1); return _depth!=-1; }
  /** Number of decision points at the moment when the bound was inferred */
  DecisionLevel depth() const { ASS(hasDepthAssigned()); return _depth; }

  /** Justification for the bound which can be used for deriving the conflict clause */
  const BoundJustification& justification() const { return _justification; }
  BoundJustification& justification() { return _justification; }

  /**
   * Return true if the current bound is less precise than the bound @c o.
   * If @c leftBound is true, we assume that the bound is a left bound,
   * otherwise we assume it is a right bound.
   *
   * Both this and @c o must be valid.
   */
  bool lessPreciseThan(const BoundInfo& o, bool leftBound) const {
    CALL("BoundInfo::lessPreciseThan");

    if(value()==o.value()) {
      return !strict() && o.strict();
    }
    if(leftBound) {
      return o.value()>value();
    }
    else {
      return o.value()<value();
    }
  }

  /**
   * Return true if the current bound is in conflict with @c o. If
   * @c iAmLeft is true, the current bound is assumed to be the left
   * one and @c o the right. If @c iAmLeft is false, it is the other
   * way round.
   */
  bool hasConflictWith(const BoundInfo& o, bool iAmLeft) const {
    CALL("BoundInfo::hasConflictWith");

    if(!iAmLeft) {
      return o.hasConflictWith(*this, true);
    }

    if(value()<o.value()) {
      return false;
    }
    if(value()>o.value()) {
      return true;
    }
    ASS_EQ(value(),o.value());
    return strict() || o.strict();
  }


  Constraint* tryGetCachedCollapsingInequality() const { return _cachedCollapsingInequality.ptr(); }
  void setCachedCollapsingInequality(Constraint* c) const { _cachedCollapsingInequality = c; }

  string toString(const BoundsArray& bounds, const BoundId& b, bool outputJustification=true) const;
private:
  void assignDepth(DecisionLevel depth) {
    CALL("BoundInfo::assignDepth");
    ASS(!hasDepthAssigned());
    ASS_GE(depth, 0);

    _depth = depth;
  }

  BoundNumber _value;
  bool _strict;
  /**
   * If non-negative, contains decition level on which the bound was inferred;
   * otherwise the decision level of the bound has not been assigned.
   *
   * Only BoundInfo object in a @b BoundsArray have their decision level
   * assigned (it is being assigned in @c BoundsArray::suggestBound() ).
   *
   */
  DecisionLevel _depth;
  BoundJustification _justification;
  mutable ConstraintRCPtr _cachedCollapsingInequality;
};


class BoundsArray
{
public:
  typedef DHSet<Var> ConflictSet;

  struct UpdateInfo
  {
    UpdateInfo(const BoundId& b, size_t boundDepth)
     : bound(b), boundDepth(boundDepth) {}

    BoundId bound;
    /** Index of the bound on the bound stack. */
    size_t boundDepth;
  };
  typedef Deque<UpdateInfo> UpdateQueue;

  BoundsArray(Solver& parent);

  void makeDecisionAssignment(Var v, BoundNumber value);

  BoundSuggestionResult suggestBound(const BoundId& b, const BoundInfo & inf, bool decisionPoint=false);

  void backtrack(DecisionLevel maxDepth);

  /**
   * Return number of variables that this object can contain.
   *
   * Numbers of the variables must be less than the returned value.
   */
  size_t varCnt() const {
    CALL("BoundsArray::varCnt");
    ASS_EQ(_left.size(),_right.size());
    return _left.size();
  }

  const BoundInfo* getBound(const BoundId& b) const;
  bool getBound(const BoundId& b, BoundNumber& val, bool& strict) const;
  bool getBound(const BoundId& b, BoundNumber& val) const {
    bool aux;
    return getBound(b, val, aux);
  }

  bool isUnbounded(const BoundId& b) const;
  bool isBoundedOnCurrentLevel(const BoundId& b) const;
  size_t countBoundsByConstraintOnCurrentLevel(const BoundId& b, const Constraint& c) const;
  bool isBoundedByCollapsingConstraintOnCurrentLevel(const BoundId& b) const;

  bool hasConflict(Var v) const;
  bool hasTightBound(Var v) const;
  BoundNumber getTightBound(Var v) const;

  static const size_t LATEST_BOUND_INDEX = static_cast<size_t>(-1);
  void tryGetCollapsingInequality(const BoundId& b, size_t boundIndex, ConstraintRCPtr& result) const;
  void tryGetCollapsingInequality(const BoundId& b, ConstraintRCPtr& result) const {
    tryGetCollapsingInequality(b, LATEST_BOUND_INDEX, result);
  }
  void getConflictCollapsingInequality(Var v, ConstraintRCPtr& result) const;
  void getConflictCollapsingInequality(Var v, size_t leftIdx, size_t rightIdx, ConstraintRCPtr& result) const;
  /**
   * Return reference to the conflict set.
   *
   * When a bound update results in a conflict, the number of the conflicting
   * variable is put into this set.
   *
   * The owner of the @c BoundsArray should periodically check whether this set is
   * empty, and if not, the conflicts should be processed and the set reset.
   */
  ConflictSet& getConflictSet() { return _conflictSet; }

  /**
   * When update of a bound does not lead to a conflict, a record about this
   * update is put at the back of this queue.
   *
   * The owner of the @c BoundsArray should periodically check whether this queue
   * is empty, and if not, a bound propagation may be performed and the queue emptied.
   *
   * The content of the queue is emptied upon backtracking.
   */
  UpdateQueue& getUpdateQueue() { return _updateQueue; }

  /**
   * Return reference to the stack with left or right bounds of variable @c v.
   *
   * Each bound must be more precise than bounds that are below it on the stack.
   *
   * Each bound must come from higher decision level than the bounds below it.
   */
  BoundStack& getBounds(const BoundId& b)
  {
    CALL("BoundsArray::getBounds");
    return b.left ? _left[b.var] : _right[b.var];
  }
  const BoundStack& getBounds(const BoundId& b) const
  {
    return const_cast<BoundsArray*>(this)->getBounds(b);
  }


  Solver& getSolver() { return _parent; }
  /**
   * Assign conflict selector object
   *
   * The conflict selector cannot be created in the constructor of this object
   * because is needs the created Solver object as argument of its constructor.
   */
  void assignConflictSelector(ConflictSelector* cs) { _conflictSelector = cs; }
private:
  static void backtrackStack(BoundStack& s, DecisionLevel maxDepth);

  DecisionLevel getDepth() const;

  Solver& _parent;

  /** Contains stack of left bounds for each variable */
  DArray<BoundStack> _left;
  /** Contains stack of right bounds for each variable */
  DArray<BoundStack> _right;

  /**
   * When a bound update results in a conflict, the number of the conflicting
   * variable is put into this set.
   *
   * Users of the @c BoundsArray object may access elements in this set and
   * reset it through the @c getConflictSet() function.
   */
  ConflictSet _conflictSet;

  /**
   * When update of a bound does not lead to a conflict, a record about this
   * update is put at the back of this queue.
   *
   * The content of the queue is emptied upon backtracking.
   *
   * Users of the @c BoundsArray object may access this queue through the
   * @c getUpdateQueue() function.
   */
  UpdateQueue _updateQueue;

  mutable ScopedPtr<ConflictSelector> _conflictSelector;
};

}
#endif //GNUMP
#endif // __BoundsArray__

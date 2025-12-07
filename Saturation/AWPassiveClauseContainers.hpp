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
 * @file AWPassiveClauseContainers.hpp
 * Defines the class AWPassiveClauseContainer and related
 * @since 31/12/2007 Manchester
 */

#ifndef __AWPassiveClauseContainers__
#define __AWPassiveClauseContainers__

#include <climits>
#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ClauseQueue.hpp"
#include "ClauseContainer.hpp"
#include "AbstractPassiveClauseContainers.hpp"

namespace Saturation {

using namespace Kernel;

class AgeQueue
: public ClauseQueue
{
public:
  AgeQueue(const Options& opt) : _opt(opt) {}

  typedef std::pair<unsigned,unsigned> OrdVal;
  static constexpr OrdVal maxOrdVal = std::make_pair(UINT_MAX,UINT_MAX);
  OrdVal getOrdVal(Clause* cl) const;
protected:
  bool lessThan(Clause*,Clause*) override;
private:
  const Shell::Options& _opt;
};

class WeightQueue
  : public ClauseQueue
{
public:
  WeightQueue(const Options& opt) : _opt(opt) {}

  typedef std::pair<unsigned,unsigned> OrdVal;
  static constexpr OrdVal maxOrdVal = std::make_pair(UINT_MAX,UINT_MAX);
  OrdVal getOrdVal(Clause* cl) const;
protected:
  bool lessThan(Clause*,Clause*) override;
private:
  const Shell::Options& _opt;
};

class AgeBasedPassiveClauseContainer
: public SingleQueuePassiveClauseContainer<AgeQueue>
{
public:
  AgeBasedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name)
    : SingleQueuePassiveClauseContainer<AgeQueue>(isOutermost,opt,name) {}

  bool mayBeAbleToDiscriminateChildrenOnLimits() const override { return limitsActive(); }
  bool allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const override {
    return cl->age() >= _curLimit.first;
  }

  /**
   * Note about performance. It's not clear why, but pure AgeBasedPassiveClauseContainer
   * actually performs worse when trying to do the below LRS trick
   * (via mayBeAbleToDiscriminateClausesUnderConstructionOnLimits == true and exceedsAgeLimit),
   * However, I didn't check what the implication for unique solutions is, so it's fine to have
   * the LRS support, but don't expect it to beat Otter in this particular case.
   *
   * Possible explanation: some age-wise large clauses could still be effective (forward-)reducers
   * (since they may still be weight-wise small) and under Otter which backs up LRS (as opposed to Discount),
   * it's the reducers that could help reaching the empty clause before even getting selected.
   * (AWPassiveClauseContainer will keep these, because it only deletes those clauses which both queues consider bad.)
   *
   * On the other hand, the above pair of functions (mayBeAbleToDiscriminateChildrenOnLimits and allChildrenNecessarilyExceedLimits)
   * as implemented (and not bluntly inherited from SingleQueuePassiveClauseContainer)
   * are now probably able to improve performance a tiny bit.
   */

  bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const override { return true; }
  bool exceedsAgeLimit(unsigned numPositiveLiterals, const Inference& inference, bool& andThatsIt) const override
  {
    andThatsIt = true; // we are the pure age-queue container
    return inference.age() > _curLimit.first;
  }
  bool exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { ASSERTION_VIOLATION; return true; }
};

class WeightBasedPassiveClauseContainer
: public SingleQueuePassiveClauseContainer<WeightQueue>
{
public:
  WeightBasedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name)
    : SingleQueuePassiveClauseContainer<WeightQueue>(isOutermost,opt,name) {}

  /*
   * Some of the previous, nominally buggy versions of "awr 0:1" path
   # (as represented by this WeightBasedPassiveClauseContainer) were more performant.
   * In particular, disabling retroactive deletes (at least for clauses with age == 0) should help.
   *
   * The implementation here is left as is, as it best reflects the ideas behind LRS
   * on this simple example. (As learning step before looking at AWPassiveClauseContainer).
   *
   * Overall, "awr 0:1" is a very weak strategy and its value even for schedules is uncertain.
   */

  bool mayBeAbleToDiscriminateChildrenOnLimits() const override { return limitsActive(); }
  bool allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const override {
    // TODO: this is an ugly copy-pase from AWPassiveClauseContainer::allChildrenNecessarilyExceedLimits

    // creating a fake inference to represent our current (pessimistic) estimate potential
    // FromInput - so that there is no Unit ownership issue
    Inference inf = FromInput(UnitInputType::CONJECTURE); // CONJECTURE, so that derivedFromGoal is estimated as true
    inf.setAge(cl->age() + 1); // clauses inferred from the clause as generating inferences will be over age limit...

    int maxSelWeight=0;
    for(unsigned i=0;i<upperBoundNumSelLits;i++) {
      maxSelWeight=std::max((int)(*cl)[i]->weight(),maxSelWeight);
    }
    // TODO: this lower bound is not correct:
    //       if Avatar is used, then the child-clause could become splittable,
    //       in which case we don't know any lower bound on the resulting components.
    unsigned weightLowerBound = cl->weight() - maxSelWeight; // heuristic: we assume that at most one literal will be removed from the clause.
    unsigned numPositiveLiteralsParent = cl->numPositiveLiterals();
    unsigned numPositiveLiteralsLowerBound = numPositiveLiteralsParent > 0 ? numPositiveLiteralsParent-1 : numPositiveLiteralsParent; // heuristic: we assume that at most one literal will be removed from the clause
    return exceedsWeightLimit(weightLowerBound, numPositiveLiteralsLowerBound, inf);
  }

  bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const override { return limitsActive(); }
  bool exceedsAgeLimit(unsigned numPositiveLiterals, const Inference& inference, bool& andThatsIt) const override
  {
    return true; // there is no age queue, so exceeding the age limit is really easy
  }
  bool exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override
  {
    // the same considerations as in AWPassiveClauseContainer::exceedsWeightLimit
    return Clause::computeWeightForClauseSelection(w, 0, 0, inference.derivedFromGoal(), _opt) > _curLimit.first;
  }
};

/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name);
  ~AWPassiveClauseContainer() override;
  void add(Clause* cl) override;

  void remove(Clause* cl) override;

  bool byWeight(int balance);

  Clause* popSelected() override;
  /** True if there are no passive clauses */
  bool isEmpty() const override
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  unsigned sizeEstimate() const override { return _size; }

private:
  /** The age queue */
  AgeQueue _ageQueue;
  /** The weight queue */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;

  unsigned _size;

  /*
   * LRS specific methods and fields for computation of Limits
   */
public:
  void simulationInit() override;
  bool simulationHasNext() override;
  void simulationPopSelected() override;

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override;
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override;

  void onLimitsUpdated() override;
private:
  bool setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight);

  int _simulationBalance;
  ClauseQueue::Iterator _simulationCurrAgeIt;
  ClauseQueue::Iterator _simulationCurrWeightIt;
  Clause* _simulationCurrAgeCl;
  Clause* _simulationCurrWeightCl;

  unsigned _ageSelectionMaxAge;
  unsigned _ageSelectionMaxWeight;
  unsigned _weightSelectionMaxWeight;
  /*
   * An experiment showed that maintaining the tiebreaker _weightSelectionMaxAge
   * and doing the corresponding extra check (in fulfilsWeightLimit) didn't lead to a better performance
   * (a possible explanation: it's better to be careful on the weight queue about age as "all small clauses, no matter how old/young are potentially useful"
   * while at the same time, it's better to be more aggressive with deletions on the age queue, as the large clauses there are probably useless)
   */
  bool ageLimited() const;
  bool weightLimited() const;

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  bool mayBeAbleToDiscriminateChildrenOnLimits() const override { return ageLimited() && weightLimited(); }
  bool allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const override;

  bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const override { return ageLimited() && weightLimited(); }

  // age is to be recovered from inference
  // andThatsIt not touched by AWPassive (as there is always also the weigtht queue to talk to)
  bool exceedsAgeLimit(unsigned numPositiveLiterals, const Inference& inference, bool& andThatsIt) const override;

  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;

  bool limitsActive() const override { return ageLimited() || weightLimited(); }

  bool exceedsAllLimits(Clause* c) const override;
}; // class AWPassiveClauseContainer


};

#endif /* __AWPassiveClauseContainers__ */

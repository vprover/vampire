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
 * @file AWPassiveClauseContainer.cpp
 * Implements class AWPassiveClauseContainer for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include <cmath>
#include <climits>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Random.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "AWPassiveClauseContainer.hpp"
#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
#endif

#define DEBUG_MODEL 0
#include <torch/utils.h>

namespace Saturation
{
using namespace Lib;
using namespace Kernel;


LearnedPassiveClauseContainer::LearnedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _scores(), _queue(_scores), _size(0), _temperature(opt.npccTemperature())
{
  CALL("LearnedPassiveClauseContainer::LearnedPassiveClauseContainer");

  ASS(_isOutermost);
}

void LearnedPassiveClauseContainer::add(Clause* cl)
{
  CALL("LearnedPassiveClauseContainer::add");

  float* t;
  if (_scores.getValuePtr(cl,t)) {
    *t = scoreClause(cl);
  } else {
    ASS_EQ(*t,scoreClause(cl));
  }
  _queue.insert(cl);
  _size++;

  // cout << "Added " << cl->toString() << " size " << _size << endl;

  ASS(cl->store() == Clause::PASSIVE);
  addedEvent.fire(cl); 
}

void LearnedPassiveClauseContainer::remove(Clause* cl)
{
  CALL("LearnedPassiveClauseContainer::remove");
  
  // we never delete from _scores, maybe that's not the best?
  _queue.remove(cl);

  _size--;

  // cout << "Removed " << cl->toString() << " size " << _size << endl;

  removedEvent.fire(cl);
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* LearnedPassiveClauseContainer::popSelected()
{
  CALL("LearnedPassiveClauseContainer::popSelected");

  // TODO: here it will get trickier with the temperature and softmax sampling!

  // we never delete from _scores, maybe that's not the best?
  Clause* cl = _queue.pop();
  _size--;

  // cout << "Popped " << cl->toString() << " size " << _size << endl;

  selectedEvent.fire(cl);
  return cl;
}

float LearnedPassiveClauseContainerExper30Rich8::scoreClause(Clause* cl) 
{
  CALL("LearnedPassiveClauseContainerExper30Rich8::scoreClause");

  Inference& inf = cl->inference();

  float features[6] = {(float)cl->age(),
                       (float)cl->size(),
                       (float)cl->weight(),
                       (float)cl->splitWeight(),
                       (float)(cl->derivedFromGoal() ? 1 : 0),
                       (float)inf.getSineLevel()};

  float weight[] = {
   0.17750899493694305, 0.4301970899105072, -0.22575949132442474, -0.5281910300254822, -0.3343266546726227, -0.3467724025249481,
   0.9967665672302246, -0.032552435994148254, 0.12055815011262894, 0.7064186930656433, 0.5752375721931458, -0.03562523052096367,
   -1.1139947175979614, -0.08131226152181625, 0.27828678488731384, -0.0036001463886350393, 1.0258698463439941, -0.0004782595206052065,
   -1.667973518371582, -0.1800791174173355, 0.2666095197200775, -0.9580445289611816, -0.803350031375885, -0.06070465222001076,
   0.16889645159244537, -0.450431764125824, 0.013268651440739632, -0.30909839272499084, 0.5091701149940491, -0.8680006861686707,
   0.4304373562335968, 0.3508818745613098, -0.04628021642565727, -0.01123655866831541, 0.9596571326255798, 0.3488212525844574,
   0.4510716199874878, 0.06400706619024277, 0.3206351697444916, -0.4565311670303345, -1.2873623371124268, 0.24093298614025116,
   -0.9983522891998291, -0.34866684675216675, 0.14929981529712677, 0.027654409408569336, 1.3375648260116577, 0.1258217990398407};
  float bias[] = {-0.10469218343496323, 0.43706417083740234, -0.4611364006996155, -0.36935943365097046, 0.11525914072990417, 0.2756221294403076, -0.45866015553474426, -0.8117114305496216};
  float kweight[] = {0.6784864068031311, -0.7771093249320984, 1.138319730758667, 0.3890429139137268, 0.6841748356819153, 0.6464572548866272, -1.2347546815872192, 0.4839847981929779};

  float res = 0.0;
  for (int i = 0; i < 8; i++) {
      float tmp = bias[i];
      for (int j = 0; j < 6; j++) {
          tmp += features[j]*weight[6*i+j];
      }
      if (tmp < 0.0) {
          tmp = 0.0;
      }
      res += tmp*kweight[i];
  }
  return res;
}

float LearnedPassiveClauseContainerExper50AW8::scoreClause(Clause* cl) 
{
  CALL("LearnedPassiveClauseContainerExper50AW8::scoreClause");

  float features[2] = {(float)cl->age(),
                       (float)cl->weight()};

  float weight[] = {
      0.029385199770331383, -0.05604780092835426,
      0.5210933685302734, -0.11956997960805893,
     -0.12272355705499649, 0.4423070549964905,
      0.6215072274208069, 0.5331867933273315,
     -0.45388317108154297, -0.0002418156509520486,
     -0.09092159569263458, 0.10178456455469131,
     -1.2727569341659546, 0.03932950273156166,
     -0.37406590580940247, -0.03839114308357239};
  float bias[] = {1.4743773937225342, 0.02129037119448185, -0.44254645705223083, 0.4881513714790344, -0.5040042996406555, -0.7501189708709717, 0.7462053298950195, -0.42353570461273193};
  float kweight[] = {1.538811206817627, 0.6278026103973389, 0.9221699237823486, -1.2884126901626587, 1.1014342308044434, 2.3632664680480957, 0.7592650651931763, 0.19266073405742645};

  float res = 0.0;
  for (int i = 0; i < 8; i++) {
      float tmp = bias[i];
      for (int j = 0; j < 2; j++) {
          tmp += features[j]*weight[2*i+j];
      }
      if (tmp < 0.0) {
          tmp = 0.0;
      }
      res += tmp*kweight[i];
  }
  return res;
}

float LearnedPassiveClauseContainerExper53AW16::scoreClause(Clause* cl) 
{
  CALL("LearnedPassiveClauseContainerExper53AW16::scoreClause");

  float features[2] = {(float)cl->age(),
                       (float)cl->weight()};

  float weight[] = {
      -0.6957781314849854, -0.3740074038505554,
      -0.3851650357246399, -0.6150509119033813,
       0.5112624168395996, -0.4895874559879303,
      -0.3304271697998047, -0.6706569194793701,
       0.21555005013942719, 0.9162867665290833,
       0.9391804337501526, 0.20778290927410126,
       0.21343015134334564, -0.11224309355020523,
       0.6425503492355347, 0.3950461149215698,
      -0.2407713681459427, -0.5422213077545166,
      -0.9309044480323792, 0.19236497581005096,
       0.7156696915626526, -0.16288228332996368,
       0.1343029886484146, -0.011083467863500118,
       0.22794225811958313, -0.03605156019330025,
       0.05842972546815872, -0.27899613976478577,
       0.22266727685928345, -0.0656970739364624,
       0.21127811074256897, -0.3992813527584076};
  float bias[] = {0.33329373598098755, -0.46352657675743103, -0.34661200642585754, 0.5527774691581726, -0.047720640897750854, -0.14827901124954224, -0.011851632967591286, -0.21482400596141815, 0.19076380133628845, 0.03552812337875366, -0.09172938764095306, 0.8349571824073792, 1.6815431118011475, 0.7830315232276917, 0.9602375626564026, -0.5289806127548218};
  float kweight[] = {0.7501270174980164, -0.03919833153486252, 0.5291730165481567, 0.32769009470939636, -0.284211665391922, -0.48525238037109375, 1.0637099742889404, -0.08649937063455582, -0.7089776992797852, 2.016587257385254, -1.4036800861358643, 1.2701835632324219, 0.37852808833122253, -1.6900583505630493, 2.0193533897399902, -0.7187753319740295};

  float res = 0.0;
  for (int i = 0; i < 16; i++) {
      float tmp = bias[i];
      for (int j = 0; j < 2; j++) {
          tmp += features[j]*weight[2*i+j];
      }
      if (tmp < 0.0) {
          tmp = 0.0;
      }
      res += tmp*kweight[i];
  }
  return res;
}


NeuralPassiveClauseContainer::NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _size(0), _temperature(opt.npccTemperature())
{
  CALL("NeuralPassiveClauseContainer::NeuralPassiveClauseContainer");

  ASS(_isOutermost);

  TIME_TRACE(TimeTrace::DEEP_STUFF);

#if DEBUG_MODEL
  auto start = env.timer->elapsedMilliseconds();
#endif

  // seems to be making this nicely single-threaded
  at::set_num_threads(1);
  at::set_num_interop_threads(1);

  torch::manual_seed(opt.randomSeed());

  _model = torch::jit::load(opt.neuralPassiveClauseContainer().c_str());

  if (auto m = _model.find_method("eatMyTweaks")) { // if the model is not interested in tweaks, it will get none!
    c10::List<double> tweaks;

    const vstring& tweak_str = opt.neuralPassiveClauseContainerTweaks();

    std::size_t i=0,j;
    while (true) {
      j = tweak_str.find_first_of(',',i);

      auto t = tweak_str.substr(i,j-i);
      if (t.empty()) {
        break;
      }

      double nextVal;
      ALWAYS(Int::stringToDouble(t,nextVal));
      tweaks.push_back(nextVal);

      if (j == std::string::npos) {
        break;
      }

      i = j+1;
    }

    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(torch::jit::IValue(tweaks));
    (*m)(std::move(inputs));
  }

#if DEBUG_MODEL
  cout << "Model loaded in " << env.timer->elapsedMilliseconds() - start << " ms" << endl;
  cout << at::get_parallel_info() << endl;
#endif
}

void NeuralPassiveClauseContainer::add(Clause* cl)
{ 
  CALL("NeuralPassiveClauseContainer::add");

  std::vector<torch::jit::IValue> inputs;

  if (!_known.find(cl)) { // TODO: keep in sync with SaturationAlgorithm::onPassiveAdded
    // argument 1 - the clause id
    inputs.push_back((int64_t)cl->number());

    Inference& inf = cl->inference();

    // argumet 2 - a tuple of floats, the features
    inputs.push_back(std::make_tuple(
      (double)cl->age(),
      (double)cl->size(),
      (double)cl->weight(),
      (double)cl->splitWeight(),
      (double)(cl->derivedFromGoal() ? 1 : 0),
      (double)inf.getSineLevel(),
      (double)(cl->isPureTheoryDescendant() ? 1 : 0),
      (double)inf.th_ancestors,
      (double)inf.all_ancestors,
      (double)(inf.th_ancestors / inf.all_ancestors)
    ));

    ALWAYS(_known.insert(cl));
    ALWAYS(_clausesById.insert(cl->number(),cl));

    _model.get_method("regClause")(std::move(inputs));
  }

  inputs.clear();
  inputs.push_back((int64_t)cl->number());
  _model.get_method("add")(std::move(inputs));

  _size++;

  ASS(cl->store() == Clause::PASSIVE);
  addedEvent.fire(cl); 
}

void NeuralPassiveClauseContainer::remove(Clause* cl) 
{ 
  CALL("NeuralPassiveClauseContainer::remove");

  ASS(cl->store()==Clause::PASSIVE);
  
  std::vector<torch::jit::IValue> inputs;
  
  inputs.push_back((int64_t)cl->number());
  _model.get_method("remove")(std::move(inputs));

  _size--;

  removedEvent.fire(cl); 
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* NeuralPassiveClauseContainer::popSelected() 
{ 
  CALL("NeuralPassiveClauseContainer::popSelected");
  ASS(_size);

  std::vector<torch::jit::IValue> inputs;
  inputs.push_back(_temperature);
  auto out = _model.get_method("popSelected")(std::move(inputs));
  unsigned id = out.toInt();

  Clause* cl = nullptr;
  ALWAYS(_clausesById.find(id,cl));

  _size--;
  selectedEvent.fire(cl);

  return cl;
}

AWPassiveClauseContainer::AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name) :
  PassiveClauseContainer(isOutermost, opt, name),
  _ageQueue(opt),
  _weightQueue(opt),
  _ageRatio(opt.ageRatio()),
  _weightRatio(opt.weightRatio()),
  _balance(0),
  _size(0),

  _simulationBalance(0),
  _simulationCurrAgeIt(_ageQueue),
  _simulationCurrWeightIt(_weightQueue),
  _simulationCurrAgeCl(nullptr),
  _simulationCurrWeightCl(nullptr),

  _ageSelectionMaxAge(UINT_MAX),
  _ageSelectionMaxWeight(UINT_MAX),
  _weightSelectionMaxWeight(UINT_MAX),
  _weightSelectionMaxAge(UINT_MAX)
{
  CALL("AWPassiveClauseContainer::AWPassiveClauseContainer");

  if(_opt.ageWeightRatioShape() == Options::AgeWeightRatioShape::CONVERGE) {
    _ageRatio = 1;
    _weightRatio = 1;
  }

  ASS_GE(_ageRatio, 0);
  ASS_GE(_weightRatio, 0);
  ASS(_ageRatio > 0 || _weightRatio > 0);
}

AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while (cit.hasNext()) 
  {
    Clause* cl=cit.next();
    ASS(!_isOutermost || cl->store()==Clause::PASSIVE);
    cl->setStore(Clause::NONE);
  }
}


/**
 * Weight comparison of clauses.
 * @return the result of comparison (LESS, EQUAL or GREATER)
 * @warning if the option increased_numeral_weight is on, then each comparison
 *          recomputes the numeral weight of clauses, see Clause::getNumeralWeight(), so it
 *          it can be expensive
 */
Comparison AWPassiveClauseContainer::compareWeight(Clause* cl1, Clause* cl2, const Options& opt)
{
  CALL("AWPassiveClauseContainer::compareWeight");

  return Int::compare(cl1->weightForClauseSelection(opt), cl2->weightForClauseSelection(opt));
}

/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by weight;</li>
 *     <li>by age;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool WeightQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("WeightQueue::lessThan");

  if(env.options->prioritiseClausesProducedByLongReduction()){
    if(c1->inference().reductions() < c2->inference().reductions()){
      return false;
    }

    if(c2->inference().reductions() < c1->inference().reductions()){
      return true;
    }
  }

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1, c2, _opt);
  if (weightCmp!=EQUAL) {
    return weightCmp==LESS;
  }

  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }
  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // WeightQueue::lessThan


/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by age;</li>
 *     <li>by weight;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool AgeQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("AgeQueue::lessThan");

  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1, c2, _opt);
  if (weightCmp!=EQUAL) {
    return weightCmp==LESS;
  }

  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }

  return c1->number() < c2->number();
} // WeightQueue::lessThan

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWPassiveClauseContainer::add(Clause* cl)
{
  CALL("AWPassiveClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);
  ASS(cl->store() == Clause::PASSIVE);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;

  if (_isOutermost)
  {
    addedEvent.fire(cl);
  }
} // AWPassiveClauseContainer::add

/**
 * Remove Clause from the Passive store. Should be called only
 * when the Clause is no longer needed by the inference process
 * (i.e. was backward subsumed/simplified), as it can result in
 * deletion of the clause.
 */
void AWPassiveClauseContainer::remove(Clause* cl)
{
  CALL("AWPassiveClauseContainer::remove");
  if (_isOutermost)
  {
    ASS(cl->store()==Clause::PASSIVE);
  }
  ASS(_ageRatio > 0 || _weightRatio > 0);
  bool wasRemoved = false;
  if (_ageRatio) {
    wasRemoved = _ageQueue.remove(cl);
  }
  if (_weightRatio) {
    wasRemoved = _weightQueue.remove(cl);
  }

  if (wasRemoved) {
    _size--;
  }

  if (_isOutermost)
  {
    removedEvent.fire(cl);
    ASS(cl->store()!=Clause::PASSIVE);
  }
}

bool AWPassiveClauseContainer::byWeight(int balance)
{
  CALL("AWPassiveClauseContainer::byWeight");

  if (! _ageRatio) {
    return true;
  }
  else if (! _weightRatio) {
    return false;
  }
  else if (balance > 0) {
    return true;
  }
  else if (balance < 0) {
    return false;
  }
  else {
    return (_ageRatio <= _weightRatio);
  }
}

/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  CALL("AWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

  auto shape = _opt.ageWeightRatioShape();
  unsigned frequency = _opt.ageWeightRatioShapeFrequency();
  static unsigned count = 0;
  count++;

  bool is_converging = shape == Options::AgeWeightRatioShape::CONVERGE;
  int targetAgeRatio = is_converging ? _opt.ageRatio() : 1;
  int targetWeightRatio = is_converging ? _opt.weightRatio() : 1;

  if(count % frequency == 0) {
    switch(shape) {
    case Options::AgeWeightRatioShape::CONSTANT:
      break;
    case Options::AgeWeightRatioShape::DECAY:
    case Options::AgeWeightRatioShape::CONVERGE:
      int ageDifference = targetAgeRatio - _ageRatio;
      int weightDifference = targetWeightRatio - _weightRatio;
      int bonus = is_converging ? 1 : -1;
      int ageUpdate = (ageDifference + bonus) / 2;
      int weightUpdate = (weightDifference + bonus) / 2;

      _ageRatio += ageUpdate;
      _weightRatio += weightUpdate;
   }
  }
  //std::cerr << _ageRatio << "\t" << _weightRatio << std::endl;
  _size--;

  Clause* cl;
  bool selByWeight = _opt.randomAWR() ? 
    // we respect the ratio, but choose probabilistically
    (Random::getInteger(_ageRatio+_weightRatio) < _weightRatio) : 
    // the deterministic way
    byWeight(_balance);

  if (selByWeight) {
    _balance -= _ageRatio;
    cl = _weightQueue.pop();
    _ageQueue.remove(cl);
  } else {
    _balance += _weightRatio;
    cl = _ageQueue.pop();
    _weightQueue.remove(cl);
  }

  if (_isOutermost) {
    selectedEvent.fire(cl);
  }

  return cl;
} // AWPassiveClauseContainer::popSelected

void AWPassiveClauseContainer::onLimitsUpdated()
{
  CALL("AWPassiveClauseContainer::onLimitsUpdated");

  if ( (_ageRatio > 0 && !ageLimited()) || (_weightRatio > 0 && !weightLimited()) )
  {
    return;
  }

  //Here we rely on (and maintain) the invariant, that
  //_weightQueue and _ageQueue contain the same set
  //of clauses, differing only in their order.
  //(unless one of _ageRation or _weightRatio is equal to 0)

  static Lib::Stack<Clause*> toRemove(256);
  ClauseQueue::Iterator wit(_weightQueue);
  while (wit.hasNext()) {
    Clause* cl=wit.next();
    if (!fulfilsAgeLimit(cl) && !fulfilsWeightLimit(cl)) {
      toRemove.push(cl);
    } else if (!childrenPotentiallyFulfilLimits(cl, cl->length())) {
      toRemove.push(cl);
    }
  }

#if OUTPUT_LRS_DETAILS
  if (toRemove.isNonEmpty()) {
    cout<<toRemove.size()<<" passive deleted, "<< (size()-toRemove.size()) <<" remains\n";
  }
#endif

  while (toRemove.isNonEmpty()) {
    Clause* removed=toRemove.pop();
    RSTAT_CTR_INC("clauses discarded from passive on weight limit update");
    env.statistics->discardedNonRedundantClauses++;
    remove(removed);
  }
}

void AWPassiveClauseContainer::simulationInit()
{
  CALL("AWPassiveClauseContainer::simulationInit");
  _simulationBalance = _balance;

  // initialize iterators
  if (_ageRatio > 0)
  {
    _simulationCurrAgeIt = ClauseQueue::Iterator(_ageQueue);
    _simulationCurrAgeCl = _simulationCurrAgeIt.hasNext() ? _simulationCurrAgeIt.next() : nullptr;
  }
  if (_weightRatio > 0)
  {
    _simulationCurrWeightIt = ClauseQueue::Iterator(_weightQueue);
    _simulationCurrWeightCl = _simulationCurrWeightIt.hasNext() ? _simulationCurrWeightIt.next() : nullptr;
  }

  if (_ageRatio > 0 && _weightRatio > 0)
  {
    // have to consider two possibilities for simulation:
    // standard case: both container are initially non-empty, then have invariants
    // - _simulationCurrAgeCl != nullptr
    // - _simulationCurrWeightCl != nullptr
    // degenerate case: both containers are initially empty (e.g. happens sometimes if layered clause selection is used), then have invariant
    // - _simulationCurrAgeCl == nullptr
    // - _simulationCurrWeightCl == nullptr
    ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
    ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);
  }
}

bool AWPassiveClauseContainer::simulationHasNext()
{
  CALL("AWPassiveClauseContainer::simulationHasNext");

  // Part 1: Return false if aw-container is empty
  if (_ageRatio == 0)
  {
    if (_simulationCurrWeightCl == nullptr)
    {
      // degenerate case: weight-container is empty (and we don't use the age-container), so return false
      return false;
    }
  }
  else if (_weightRatio == 0)
  {
    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: age-container is empty (and we don't use the weight-container), so return false
      return false;
    }
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
    ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
    ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);

    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: both containers are empty, so return false
      return false;
    }
  }

  // if we reach this point, we know that there is at least one clause in the aw-container (but it could already been deleted in the simulation)
  // Part 2: advance each iterator to point to a clause not deleted in the simulation (if possible)
  if (_ageRatio > 0)
  {
    // advance _simulationCurrAgeIt, until _simulationCurrAgeCl points to a
    // clause which has not been deleted in the simulation or _simulationCurrAgeIt
    // reaches the end of the age-queue
    // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrAgeCl is not deleted.
    while (_simulationCurrAgeCl->hasAux() && _simulationCurrAgeIt.hasNext())
    {
      _simulationCurrAgeCl = _simulationCurrAgeIt.next();
    }
    ASS(_simulationCurrAgeCl != nullptr);
  }
  if (_weightRatio > 0)
  {
    // advance _simulationCurrWeightIt, until _simulationCurrWeightCl points to a
    // clause which has not been deleted in the simulation or _simulationCurrWeightIt
    // reaches the end of the weight-queue
    // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrWeightCl is not deleted.
    while (_simulationCurrWeightCl->hasAux() && _simulationCurrWeightIt.hasNext())
    {
      _simulationCurrWeightCl = _simulationCurrWeightIt.next();
    }
    ASS(_simulationCurrWeightCl != nullptr);
  }

  // Part 3: return whether clause was found which is not deleted in the simulation
  if (_ageRatio == 0)
  {
    return !_simulationCurrWeightCl->hasAux();
  }
  else if (_weightRatio == 0)
  {
    return !_simulationCurrAgeCl->hasAux();
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
    ASS(!_simulationCurrAgeCl->hasAux() || _simulationCurrWeightCl->hasAux());
    ASS(_simulationCurrAgeCl->hasAux() || !_simulationCurrWeightCl->hasAux());

    return !_simulationCurrAgeCl->hasAux();
  }
}

// assumes that simulationHasNext() has been called before and returned true,
// so each iterator (if used) does point to a clause which is not deleted in the simulation
void AWPassiveClauseContainer::simulationPopSelected()
{
  CALL("AWPassiveClauseContainer::simulationPopSelected");

  // invariants:
  // - both queues share the aux-field which denotes whether a clause was deleted during the simulation
  // - if _ageRatio > 0 and _weightRatio > 0, then both queues contain the same clauses
  // note: byWeight() already takes care of the cases where _ageRatio == 0 or _weightRatio == 0
  if (byWeight(_simulationBalance)) {
    // simulate selection by weight
    _simulationBalance -= _ageRatio;
    ASS(!_simulationCurrWeightCl->hasAux());
    _simulationCurrWeightCl->setAux();
  } else {
    // simulate selection by age
    _simulationBalance += _weightRatio;
    ASS(!_simulationCurrAgeCl->hasAux());
    _simulationCurrAgeCl->setAux();
  }
}

bool AWPassiveClauseContainer::setLimitsToMax()
{
  CALL("AWPassiveClauseContainer::setLimitsToMax");
  return setLimits(UINT_MAX, UINT_MAX, UINT_MAX, UINT_MAX);
}

bool AWPassiveClauseContainer::setLimitsFromSimulation()
{
  CALL("AWPassiveClauseContainer::setLimitsFromSimulation");

  if (_ageRatio == 0)
  {
    if (_simulationCurrWeightCl == nullptr)
    {
      // degenerate case: weight-container is empty (and we don't use the age-container), so set limits to max.
      return setLimitsToMax();
    }
  }
  else if (_weightRatio == 0)
  {
    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: age-container is empty (and we don't use the weight-container), so set limits to max.
      return setLimitsToMax();
    }
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
    ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
    ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);

    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: both containers are empty, so set limits to max.
      return setLimitsToMax();
    }
    else
    {
      ASS(!_simulationCurrAgeCl->hasAux() || _simulationCurrWeightCl->hasAux());
      ASS(_simulationCurrAgeCl->hasAux() || !_simulationCurrWeightCl->hasAux());
    }
  }

  unsigned maxAgeQueueAge;
  unsigned maxAgeQueueWeight;
  unsigned maxWeightQueueWeight;
  unsigned maxWeightQueueAge;

  // compute limits for age-queue
  if (_ageRatio > 0)
  {
    if (_simulationCurrAgeIt.hasNext())
    {
      // the age-queue is in use and the simulation didn't get to the end of the age-queue => set limits on age-queue
      maxAgeQueueAge = _simulationCurrAgeCl->age();
      maxAgeQueueWeight = _simulationCurrAgeCl->weightForClauseSelection(_opt);
    }
    else
    {
      // the age-queue is in use and the simulation got to the end of the age-queue => set no limits on age-queue
      maxAgeQueueAge = UINT_MAX;
      maxAgeQueueWeight = UINT_MAX;
    }
  }
  else
  {
    // the age-queue is not in use, so no clause will be selected from the age-queue => set tighest possible bound on age-queue
    maxAgeQueueAge = 0;
    maxAgeQueueWeight = 0;
  }

  // compute limits for weight-queue
  if (_weightRatio > 0)
  {
    if (_simulationCurrWeightIt.hasNext())
    {
      // the weight-queue is in use and the simulation didn't get to the end of the weight-queue => set limits on weight-queue
      maxWeightQueueWeight = _simulationCurrWeightCl->weightForClauseSelection(_opt);
      maxWeightQueueAge = _simulationCurrWeightCl->age();
    }
    else
    {
      // the weight-queue is in use and the simulation got to the end of the weight-queue => set no limits on weight-queue
      maxWeightQueueWeight = UINT_MAX;
      maxWeightQueueAge = UINT_MAX;
    }
  }
  else
  {
    // the weight-queue is not in use, so no clause will be selected from the weight-queue => set tighest possible bound on weight-queue
    maxWeightQueueWeight = 0;
    maxWeightQueueAge = 0;
  }

  // note: we ignore the option lrsWeightLimitOnly() if weightRatio is set to 0
  // TODO: force in Options that weightRatio is positive if lrsWeightLimitOnly() is set to 'on'.
  if (_opt.lrsWeightLimitOnly() && _weightRatio > 0)
  {
    // if the option lrsWeightLimitOnly() is set, we want to discard all clauses which are too heavy, regardless of the age.
    // we therefore make sure that fulfilsAgeLimit() always fails.
    maxAgeQueueAge = 0;
    maxAgeQueueWeight = 0;
  }

  return setLimits(maxAgeQueueAge, maxAgeQueueWeight,maxWeightQueueWeight, maxWeightQueueAge);
}

bool AWPassiveClauseContainer::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const
{
  CALL("AWPassiveClauseContainer::childrenPotentiallyFulfilLimits");
  if (cl->age() == _ageSelectionMaxAge)
  {
    // creating a fake inference to represent our current (pessimistic) estimate potential
    // FromInput - so that there is no Unit ownership issue
    Inference inf = FromInput(UnitInputType::CONJECTURE); // CONJECTURE, so that derivedFromGoal is estimated as true
    inf.setAge(cl->age() + 1); // clauses inferred from the clause as generating inferences will be over age limit...

    int maxSelWeight=0;
    for(unsigned i=0;i<upperBoundNumSelLits;i++) {
      maxSelWeight=max((int)(*cl)[i]->weight(),maxSelWeight);
    }
    // TODO: this lower bound is not correct:
    //       if Avatar is used, then the child-clause could become splittable,
    //       in which case we don't know any lower bound on the resulting components.
    unsigned weightLowerBound = cl->weight() - maxSelWeight; // heuristic: we assume that at most one literal will be removed from the clause.
    unsigned numPositiveLiteralsParent = cl->numPositiveLiterals();
    unsigned numPositiveLiteralsLowerBound = numPositiveLiteralsParent > 0 ? numPositiveLiteralsParent-1 : numPositiveLiteralsParent; // heuristic: we assume that at most one literal will be removed from the clause
    if (!fulfilsWeightLimit(weightLowerBound, numPositiveLiteralsLowerBound, inf)) {
      //and also over weight limit
      return false;
    }
  }
  return true;
}

bool AWPassiveClauseContainer::setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge)
{
  CALL("AWPassiveClauseContainer::setLimits");

  bool atLeastOneTightened = false;
  if(newAgeSelectionMaxAge != _ageSelectionMaxAge || newAgeSelectionMaxWeight != _ageSelectionMaxWeight) {
    if(newAgeSelectionMaxAge < _ageSelectionMaxAge) {
      atLeastOneTightened = true;
    } else if (newAgeSelectionMaxAge == _ageSelectionMaxAge && newAgeSelectionMaxWeight < _ageSelectionMaxWeight) {
      atLeastOneTightened = true;
    }
    _ageSelectionMaxAge=newAgeSelectionMaxAge;
    _ageSelectionMaxWeight=newAgeSelectionMaxWeight;
  }
  if(newWeightSelectionMaxWeight != _weightSelectionMaxWeight || newWeightSelectionMaxAge != _weightSelectionMaxAge) {
    if(newWeightSelectionMaxWeight < _weightSelectionMaxWeight) {
      atLeastOneTightened = true;
    } else if (newWeightSelectionMaxWeight == _weightSelectionMaxWeight && newWeightSelectionMaxAge < _weightSelectionMaxAge) {
      atLeastOneTightened = true;
    }
    _weightSelectionMaxWeight=newWeightSelectionMaxWeight;
    _weightSelectionMaxAge=newWeightSelectionMaxAge;
  }
  return atLeastOneTightened;
}

bool AWPassiveClauseContainer::ageLimited() const
{
  CALL("AWPassiveClauseContainer::ageLimited");

  return _ageRatio > 0 && _ageSelectionMaxAge != UINT_MAX && _ageSelectionMaxWeight != UINT_MAX;
}

bool AWPassiveClauseContainer::weightLimited() const
{
  CALL("AWPassiveClauseContainer::weightLimited");
  return _weightRatio > 0 && _weightSelectionMaxWeight != UINT_MAX && _weightSelectionMaxAge != UINT_MAX;
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(Clause* cl) const
{
  CALL("AWPassiveClauseContainer::fulfilsAgeLimit(Clause*)");

  // don't want to reuse fulfilsAgeLimit(unsigned age,..) here, since we don't want to recompute weightForClauseSelection
  unsigned age = cl->age();
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("AWPassiveClauseContainer::fulfilsAgeLimit(unsigned, unsigned, const Inference&)");

  const unsigned age = inference.age();
  const unsigned numeralWeight = 0; // heuristic: we don't want to compute the numeral weight during estimates and conservatively assume that it is 0.
  const unsigned splitWeight = 0; // also conservatively assuming 0
  /* In principle, we could compute this from the Inference (and it's not so expensive)
   * but it's only relevant with avatar on (and avatar would later compute the splitset of the new clause again)
   * and nonliteralsInClauseWeight on, which is not the default. So keeping the cheap version for now.
   */
  const bool derivedFromGoal = inference.derivedFromGoal();
  // If the caller was too lazy to supply an Inference object we conservatively assume that the result is a goal-clause.
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, splitWeight, numeralWeight, derivedFromGoal, _opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool AWPassiveClauseContainer::fulfilsWeightLimit(Clause* cl) const
{
  CALL("AWPassiveClauseContainer::fulfilsWeightLimit(Clause*)");

  // don't want to reuse fulfilsWeightLimit(unsigned w,..) here, since we don't want to recompute weightForClauseSelection
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  unsigned age = cl->age();
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

bool AWPassiveClauseContainer::fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("AWPassiveClauseContainer::fulfilsWeightLimit(unsigned, unsigned, const Inference&)");

  const unsigned age = inference.age();
  const unsigned numeralWeight = 0; // heuristic: we don't want to compute the numeral weight during estimates and conservatively assume that it is 0.
  const unsigned splitWeight = 0; // also conservatively assuming 0
  /* In principle, we could compute this from the Inference (and it's not so expensive)
   * but it's only relevant with avatar on (and avatar would later compute the splitset of the new clause again)
   * and nonliteralsInClauseWeight on, which is not the default. So keeping the cheap version for now.
   */
  const bool derivedFromGoal = inference.derivedFromGoal();
  // If the caller was too lazy to supply an Inference object we conservatively assume that the result is a goal-clause.
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, splitWeight, numeralWeight, derivedFromGoal, _opt);
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

AWClauseContainer::AWClauseContainer(const Options& opt)
: _ageQueue(opt), _weightQueue(opt), _ageRatio(1), _weightRatio(1), _balance(0), _size(0), _randomized(opt.randomAWR())
{
}

bool AWClauseContainer::isEmpty() const
{
  CALL("AWClauseContainer::isEmpty");

  ASS(!_ageRatio || !_weightRatio || _ageQueue.isEmpty()==_weightQueue.isEmpty());
  return _ageQueue.isEmpty() && _weightQueue.isEmpty();
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWClauseContainer::add(Clause* cl)
{
  CALL("AWClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;
  addedEvent.fire(cl);
}

/**
 * Remove Clause from the container.
 */
bool AWClauseContainer::remove(Clause* cl)
{
  CALL("AWClauseContainer::remove");

  bool removed;
  if (_ageRatio) {
    removed = _ageQueue.remove(cl);
    if (_weightRatio) {
      ALWAYS(_weightQueue.remove(cl)==removed);
    }
  }
  else {
    ASS(_weightRatio);
    removed = _weightQueue.remove(cl);
  }

  if (removed) {
    _size--;
    removedEvent.fire(cl);
  }
  return removed;
}

/**
 * Return the next selected clause and remove it from the queue.
 */
Clause* AWClauseContainer::popSelected()
{
  CALL("AWClauseContainer::popSelected");
  ASS( ! isEmpty());

  _size--;

  bool byWeight;
  if (! _ageRatio) {
    byWeight = true;
  }
  else if (! _weightRatio) {
    byWeight = false;
  }
  else if (_randomized) {
    byWeight = (Random::getInteger(_ageRatio+_weightRatio) < _weightRatio);
  } else if (_balance > 0) {
    byWeight = true;
  }
  else if (_balance < 0) {
    byWeight = false;
  }
  else {
    byWeight = (_ageRatio <= _weightRatio);
  }

  Clause* cl;
  if (byWeight) {
    _balance -= _ageRatio;
    cl = _weightQueue.pop();
    ALWAYS(_ageQueue.remove(cl));
  }
  else {
    _balance += _weightRatio;
    cl = _ageQueue.pop();
    ALWAYS(_weightQueue.remove(cl));
  }
  selectedEvent.fire(cl);
  return cl;
}



}

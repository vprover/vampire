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
#include "Kernel/SoftmaxClauseQueue.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
#endif

#include "AWPassiveClauseContainer.hpp"

#define DEBUG_MODEL 0
#include <torch/utils.h>

namespace Saturation
{
using namespace std;
using namespace Lib;
using namespace Kernel;


LearnedPassiveClauseContainer::LearnedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _scores(), _queue(_scores), _size(0), _temperature(opt.npccTemperature())
{
  ASS(_isOutermost);
}

void LearnedPassiveClauseContainer::add(Clause* cl)
{
  std::pair<float,unsigned>* pair;
  if (_scores.getValuePtr(cl,pair)) {
    *pair = std::make_pair(scoreClause(cl),Random::getInteger(1073741824));
  }
  _queue.insert(cl);
  _size++;

  // cout << "Added " << cl->toString() << " size " << _size << endl;

  ASS(cl->store() == Clause::PASSIVE);
  addedEvent.fire(cl);
}

void LearnedPassiveClauseContainer::remove(Clause* cl)
{
  // we never delete from _scores, maybe that's not the best?
  _queue.remove(cl);

  _size--;

  // cout << "Removed " << cl->toString() << " size " << _size << endl;

  removedEvent.fire(cl);
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* LearnedPassiveClauseContainer::popSelected()
{
  // TODO: here it will get trickier with the temperature and softmax sampling!

  // we never delete from _scores, maybe that's not the best?
  Clause* cl = _queue.pop();
  _size--;

  // cout << "Popped " << cl->toString() << " size " << _size << endl;

  selectedEvent.fire(cl);
  return cl;
}

float LearnedPassiveClauseContainerExperNF12cLoop5::scoreClause(Clause* cl)
{
  Clause::FeatureIterator fit(cl);

  float features[12] = {(float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next(),
                        (float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next(),(float)fit.next()};

  float weight[] = {
    -2.0405941009521484, 0.12202191352844238, 0.20660847425460815, 0.8350633978843689, -0.14192698895931244, 0.6823735237121582, 0.8786749839782715, -0.11922553181648254, 0.5346186757087708, 0.2527293562889099, -0.48670780658721924, -1.396571397781372,
    0.34327173233032227, -0.11386033892631531, 0.3851318657398224, -1.944481372833252, 0.47715431451797485, -0.8444045782089233, -1.3999969959259033, 0.23372626304626465, -0.9005630612373352, 0.9059399962425232, 0.07302427291870117, -1.581055998802185,
    0.5451248288154602, 0.23543480038642883, 0.039707571268081665, -0.2643747329711914, -0.08209452033042908, 0.9222909212112427, -0.3640296459197998, 0.08987753093242645, -0.9831720590591431, -0.4468047320842743, -0.11443955451250076, 1.5496660470962524,
    -3.107799530029297, 0.22115907073020935, -0.2641993761062622, 0.3595792055130005, -0.5342901349067688, 0.5067926645278931, -0.03309682756662369, 0.19077888131141663, -0.46792128682136536, -1.739579439163208, -0.6812117695808411, -1.1918081045150757,
    0.8465003371238708, 0.042243655771017075, -0.1746903508901596, 0.24819599092006683, -0.32844430208206177, 0.8037562966346741, 0.1972443014383316, 0.18607524037361145, -0.5450467467308044, 0.05763491243124008, 0.0818820521235466, 1.1643238067626953,
    -0.05943622067570686, 0.09342581033706665, 0.34915491938591003, -0.10326356440782547, 0.7751635909080505, 0.6140362024307251, 0.5045745372772217, -0.9581993818283081, 0.9414848685264587, 1.5846697092056274, -0.026700519025325775, -1.7046382427215576,
    0.6129408478736877, -0.4079468548297882, -0.09116656333208084, 0.5605136752128601, -1.721616268157959, 2.0208377838134766, -0.2280556708574295, 0.06740489602088928, 0.8718560934066772, -0.7919328808784485, 0.03510770574212074, 0.15992459654808044,
    0.5424445271492004, 0.10199402272701263, -0.021819917485117912, 0.37965983152389526, -0.12451092153787613, 0.7016618847846985, 0.019443033263087273, 0.15037991106510162, -0.8367310166358948, 0.12205961346626282, 0.3608677387237549, 1.4494743347167969,
    0.39824023842811584, -0.0651693046092987, 0.15712572634220123, 0.4916081726551056, -0.08553516864776611, -0.17163175344467163, 0.18713459372520447, 0.12873928248882294, -0.746273398399353, -0.4054866135120392, 0.2539588510990143, 1.3716002702713013,
    0.8778604865074158, 0.056522175669670105, 0.16329514980316162, 0.11627950519323349, 0.032977260649204254, -0.11529311537742615, 0.03956061974167824, -0.037985362112522125, -0.9197039604187012, -1.4825650453567505, 0.37275660037994385, 1.1955711841583252,
    0.5749868750572205, 0.04442526772618294, 0.047122370451688766, 0.35504409670829773, 0.05695868656039238, 0.898934006690979, -0.1719825714826584, -0.0007673741201870143, -0.5014393329620361, -0.04191356524825096, 0.31047967076301575, 1.0618921518325806,
    -0.10317326337099075, -0.07561460137367249, -0.04910855367779732, -0.14195069670677185, -0.153847798705101, -0.26410049200057983, -0.14690853655338287, -0.21531906723976135, -0.22774572670459747, -0.194924458861351, 0.09902256727218628, -0.011355039663612843,
    0.0247220229357481, -0.49687010049819946, 0.8304696679115295, 0.09509161114692688, 0.5466886162757874, 0.184383362531662, 0.471223384141922, -0.015821756795048714, -1.1008623838424683, -0.31359875202178955, 0.0646572932600975, 1.4368337392807007,
    0.518570065498352, 0.1785249412059784, 0.13946658372879028, 0.3568970859050751, -0.17607930302619934, 0.4906843602657318, -0.333568811416626, -0.14993613958358765, -0.19920840859413147, -0.07193896174430847, 0.37689778208732605, 1.3621294498443604,
    -0.6101843118667603, 0.024073515087366104, 0.24759799242019653, -0.7292666435241699, 0.16373802721500397, -1.8925291299819946, 1.141858696937561, 0.139650359749794, -0.33725234866142273, 0.4965920150279999, -0.42264172434806824, -1.4773523807525635,
    0.5868123769760132, -0.3106329143047333, -0.20227579772472382, -0.09633610397577286, 0.4186137616634369, -0.41743332147598267, -0.4262687861919403, 0.31165263056755066, 1.8063807487487793, -0.40551140904426575, -0.16047526895999908, 0.3483814299106598};

  float bias[] = {2.8044779300689697, -1.3988730907440186, -0.034629229456186295, 1.1336582899093628, 1.174654483795166, 0.8624619841575623, 0.8874326348304749, -0.28390437364578247, 0.003475602250546217, -0.671423614025116, 0.42329445481300354, -0.15679511427879333, 0.30384835600852966, -0.05644775182008743, 1.1080713272094727, -0.08055964857339859};
  float kweight[] = {0.37144598364830017, 0.5145484805107117, -0.2039152830839157, 0.2875518500804901, -0.31656408309936523, 0.4513503313064575, 0.9311041831970215, -0.21673251688480377, -0.032943692058324814, -0.498897910118103, -0.21648238599300385, -0.036208927631378174, -1.37989342212677, -0.21697357296943665, 0.07956060022115707, 0.7410840392112732};

  float res = 0.0;
  for (int i = 0; i < 16; i++) {
      float tmp = bias[i];
      for (int j = 0; j < 12; j++) {
          tmp += features[j]*weight[12*i+j];
      }
      if (tmp < 0.0) {
          tmp = 0.0;
      }
      res += tmp*kweight[i];
  }
  return res;
}

NeuralPassiveClauseContainer::NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _size(0), _temp(opt.npccTemperature()), _reshuffleAt(opt.reshuffleAt())
{
  ASS(_isOutermost);

  if (_temp == 0.0) {
    _queue = SmartPtr<AbstractClauseQueue>(new ShuffledScoreQueue(_scores));
  } else {
    _queue = SmartPtr<AbstractClauseQueue>(new SoftmaxClauseQueue(_scores, opt.showPassiveTraffic()));
  }

  TIME_TRACE(TimeTrace::DEEP_STUFF);

#if DEBUG_MODEL
  auto start = env.timer->elapsedMilliseconds();
#endif

  // seems to be making this nicely single-threaded
  at::set_num_threads(1);
  at::set_num_interop_threads(1);

  torch::manual_seed(opt.randomSeed());

  _model = torch::jit::load(opt.neuralPassiveClauseContainer().c_str());
  _model.eval();

  const std::string& tweak_str = opt.neuralPassiveClauseContainerTweaks();
  if (!tweak_str.empty()) {
    if (auto m = _model.find_method("eatMyTweaks")) { // if the model is not interested in tweaks, it will get none!
      std::vector<float> tweaks;

      std::size_t i=0,j;
      while (true) {
        j = tweak_str.find_first_of(',',i);

        auto t = tweak_str.substr(i,j-i);
        if (t.empty()) {
          break;
        }

        float nextVal;
        ALWAYS(Int::stringToFloat(t.c_str(),nextVal));
        tweaks.push_back(nextVal);

        if (j == std::string::npos) {
          break;
        }

        i = j+1;
      }

      std::vector<torch::jit::IValue> inputs;
      inputs.push_back(torch::jit::IValue(torch::from_blob(tweaks.data(), {static_cast<long long>(tweaks.size())}, torch::TensorOptions().dtype(torch::kFloat32))));
      (*m)(std::move(inputs));
    }
  }

#if DEBUG_MODEL
  cout << "Model loaded in " << env.timer->elapsedMilliseconds() - start << " ms" << endl;
  cout << at::get_parallel_info() << endl;
#endif
}

void NeuralPassiveClauseContainer::add(Clause* cl)
{
  if (!_scores.find(cl)) {
    std::vector<torch::jit::IValue> inputs;

    // argument 1 - the clause id
    inputs.push_back((int64_t)cl->number());

    std::vector<float> features(_opt.numClauseFeatures());
    unsigned i = 0;
    Clause::FeatureIterator it(cl);
    while (i < _opt.numClauseFeatures() && it.hasNext()) {
      features[i] = it.next();
      i++;
    }
    ASS_EQ(features.size(),_opt.numClauseFeatures());
    inputs.push_back(torch::from_blob(features.data(), {_opt.numClauseFeatures()}, torch::TensorOptions().dtype(torch::kFloat32)));

    float logit = _model.forward(std::move(inputs)).toDouble();
    unsigned salt = Random::getInteger(1073741824); // 2^30, because why not

    float score;
    if (_temp == 0.0) {
      score = logit;
    } else {
      score = exp((logit-1.0)/_temp);
    }

    // cout << "New clause has " << make_pair(score,salt) << " with number " << cl->number() << endl;
    _scores.insert(cl,make_pair(score,salt));
  }

  // cout << "Inserting " << cl->number() << endl;
  _queue->insert(cl);
  _size++;

  ASS(cl->store() == Clause::PASSIVE);
  addedEvent.fire(cl);
}

void NeuralPassiveClauseContainer::remove(Clause* cl)
{
  ASS(cl->store()==Clause::PASSIVE);

  // cout << "Removing " << cl->number() << endl;
  _queue->remove(cl);
  _size--;

  removedEvent.fire(cl);
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* NeuralPassiveClauseContainer::popSelected()
{
  ASS(_size);

  static unsigned popCount = 0;

  if (++popCount == _reshuffleAt) {
    // cout << "reshuffled at "<< popCount << endl;
    Random::resetSeed();
  }

  // cout << "About to pop" << endl;
  Clause* cl = _queue->pop();
  // cout << "Got " << cl->number() << endl;
  // cout << "popped from " << _size << " got " << cl->toString() << endl;
  _size--;

  if (popCount == _reshuffleAt) {
    cout << "s: " << cl->number() << '\n';
  }

  selectedEvent.fire(cl);
  return cl;
}

AWPassiveClauseContainer::AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name) :
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
  if ( (_ageRatio > 0 && !ageLimited()) || (_weightRatio > 0 && !weightLimited()) )
  {
    return;
  }

  //Here we rely on (and maintain) the invariant, that
  //_weightQueue and _ageQueue contain the same set
  //of clauses, differing only in their order.
  //(unless one of _ageRation or _weightRatio is equal to 0)

  static Stack<Clause*> toRemove(256);
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
  return setLimits(UINT_MAX, UINT_MAX, UINT_MAX, UINT_MAX);
}

bool AWPassiveClauseContainer::setLimitsFromSimulation()
{
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
  return _ageRatio > 0 && _ageSelectionMaxAge != UINT_MAX && _ageSelectionMaxWeight != UINT_MAX;
}

bool AWPassiveClauseContainer::weightLimited() const
{
  return _weightRatio > 0 && _weightSelectionMaxWeight != UINT_MAX && _weightSelectionMaxAge != UINT_MAX;
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(Clause* cl) const
{
  // don't want to reuse fulfilsAgeLimit(unsigned age,..) here, since we don't want to recompute weightForClauseSelection
  unsigned age = cl->age();
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
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
  // don't want to reuse fulfilsWeightLimit(unsigned w,..) here, since we don't want to recompute weightForClauseSelection
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  unsigned age = cl->age();
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

bool AWPassiveClauseContainer::fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
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
  ASS(!_ageRatio || !_weightRatio || _ageQueue.isEmpty()==_weightQueue.isEmpty());
  return _ageQueue.isEmpty() && _weightQueue.isEmpty();
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWClauseContainer::add(Clause* cl)
{
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

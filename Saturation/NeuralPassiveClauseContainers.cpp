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
 * @file NeuralPassiveClauseContainer.cpp
 * Implements class NeuralPassiveClauseContainer and co.
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

#include "NeuralPassiveClauseContainers.hpp"

#define DEBUG_MODEL 0
#include <torch/utils.h>

namespace Saturation
{
using namespace std;
using namespace Lib;
using namespace Kernel;

NeuralClauseEvaluationModel::NeuralClauseEvaluationModel(const std::string modelFilePath, const std::string& tweak_str,
  uint64_t random_seed, unsigned num_features, float temperature) : _numFeatures(num_features), _temp(temperature)
{
  TIME_TRACE("neural model warmup");

#if DEBUG_MODEL
  auto start = env.timer->elapsedMilliseconds();
#endif

  // seems to be making this nicely single-threaded
  at::set_num_threads(1);
  at::set_num_interop_threads(1);

  torch::manual_seed(random_seed);

  _model = torch::jit::load(modelFilePath);
  _model.eval();

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

float NeuralClauseEvaluationModel::getScore(Clause* cl) {
  SaltedLogit* someVal = _scores.findPtr(cl->number());
  if (someVal) {
    return someVal->first;
  }
  return std::numeric_limits<float>::max();
}

NeuralClauseEvaluationModel::SaltedLogit NeuralClauseEvaluationModel::evalClause(Clause* cl) {
  SaltedLogit* someVal = _scores.findPtr(cl->number());
  if (someVal) {
    return *someVal;
  }

  float logit;
  {
    TIME_TRACE("neural model evaluation");

    std::vector<torch::jit::IValue> inputs;

    std::vector<float> features(_numFeatures);
    unsigned i = 0;
    Clause::FeatureIterator it(cl);
    while (i < _numFeatures && it.hasNext()) {
      features[i] = it.next();
      i++;
    }
    ASS_EQ(features.size(),_numFeatures);
    inputs.push_back(torch::from_blob(features.data(), {_numFeatures}, torch::TensorOptions().dtype(torch::kFloat32)));

    logit = _model.forward(std::move(inputs)).toTensor().item().toDouble();
  }

  float score = (_temp == 0.0) ? logit : exp(logit/_temp);
  unsigned salt = Random::getInteger(1073741824); // 2^30, because why not

  SaltedLogit res = make_pair(score,salt);
  // cout << "New clause has " << res << " with number " << cl->number() << endl;
  _scores.insert(cl->number(),res);
  return res;
}

void NeuralClauseEvaluationModel::evalClauses(Saturation::UnprocessedClauseContainer& clauses) {
  TIME_TRACE("neural model evaluation");

  unsigned sz = clauses.size();
  if (sz == 0) return;

  std::vector<float> features(_numFeatures*sz);
  {
    unsigned idx = 0;
    auto uIt = clauses.iter();
    while (uIt.hasNext()) {
      unsigned i = 0;
      Clause* cl = uIt.next();
      Clause::FeatureIterator cIt(cl);
      while (i++ < _numFeatures && cIt.hasNext()) {
        features[idx] = cIt.next();
        idx++;
      }
    }
  }

  std::vector<torch::jit::IValue> inputs;
  inputs.push_back(torch::from_blob(features.data(), {sz,_numFeatures}, torch::TensorOptions().dtype(torch::kFloat32)));
  auto logits = _model.forward(std::move(inputs)).toTensor();

  {
    auto uIt = clauses.iter();
    unsigned idx = 0;
    while (uIt.hasNext()) {
      Clause* cl = uIt.next();
      float logit = logits[idx++].item().toDouble();
      float score = (_temp == 0.0) ? logit : exp(logit/_temp);

      SaltedLogit* someVal = _scores.findPtr(cl->number());
      if (someVal) {
        ASS_L(abs(someVal->first-score),0.00001);
        // we don't insert, we don't want to change the salt
      } else {
        unsigned salt = Random::getInteger(1073741824); // 2^30, because why not
        SaltedLogit res = make_pair(score,salt);
        _scores.insert(cl->number(),res);
      }
    }
  }
}

NeuralPassiveClauseContainer::NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, NeuralClauseEvaluationModel& model)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _model(model), _size(0), _reshuffleAt(opt.reshuffleAt())
{
  ASS(_isOutermost);

  if (opt.npccTemperature() == 0.0) {
    _queue = SmartPtr<AbstractClauseQueue>(new ShuffledScoreQueue(_model.getScores()));
  } else {
    _queue = SmartPtr<AbstractClauseQueue>(new SoftmaxClauseQueue(_model.getScores(), opt.showPassiveTraffic()));
  }
}

void NeuralPassiveClauseContainer::add(Clause* cl)
{
  (void)_model.evalClause(cl); // make sure scores inside model know about this clauses (so that queue can insert it properly)

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

LearnedPassiveClauseContainer::LearnedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt)
  : LRSIgnoringPassiveClauseContainer(isOutermost, opt), _scores(), _queue(_scores), _size(0), _temperature(opt.npccTemperature())
{
  ASS(_isOutermost);
}

void LearnedPassiveClauseContainer::add(Clause* cl)
{
  std::pair<float,unsigned>* pair;
  if (_scores.getValuePtr(cl->number(),pair)) {
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

} // namespace Saturation

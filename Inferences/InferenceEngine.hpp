/**
 * @file InferenceEngine.hpp
 * Defines class InferenceEngine
 *
 */

#ifndef __InferenceEngine__
#define __InferenceEngine__

#include "../Forwards.hpp"

#include "../Lib/VirtualIterator.hpp"

namespace Inference
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

class InferenceEngine
{
public:
  InferenceEngine() : _salg(0) {}
  virtual ~InferenceEngine() {}
  virtual void attach(SaturationAlgorithm* salg)
  {
    ASS(!_salg);
    _salg=salg;
  }
protected:
  SaturationAlgorithm* _salg;
};

class GeneratingInferenceEngine
: public InferenceEngine
{
public:
  virtual ClauseIterator generateClauses(Clause* premise) = 0;
};

class ForwardSimplificationEngine
: public InferenceEngine
{
public:
  virtual void perform(Clause* cl, bool& keep, ClauseIterator& toAdd) = 0;
};

class BackwardSimplificationEngine
: public InferenceEngine
{
public:
  virtual void perform(Clause* premise, ClauseIterator& toRemove, ClauseIterator& toAdd) = 0;
};

class DummyGeneratingInferenceEngine
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise)
  {
    return ClauseIterator::getEmpty();
  }
};

class DummyForwardSimplificationEngine
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
  {
    keep=true;
    toAdd=ClauseIterator::getEmpty();
  }
};

class DummyBackwardSimplificationEngine
: public BackwardSimplificationEngine
{
public:
  void perform(Clause* premise, ClauseIterator& toRemove, ClauseIterator& toAdd)
  {
    toRemove=ClauseIterator::getEmpty();
    toAdd=ClauseIterator::getEmpty();
  }
};

};

#endif /*__InferenceEngine__*/

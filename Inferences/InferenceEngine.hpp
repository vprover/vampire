/**
 * @file InferenceEngine.hpp
 * Defines class InferenceEngine
 *
 */

#ifndef __InferenceEngine__
#define __InferenceEngine__

#include "../Forwards.hpp"
#include "../Lib/SmartPtr.hpp"

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/List.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

/**
 * InferenceEngine is a base class for classes representing possible
 * inferences -- generating inferences and forward and backward
 * simplifications. These inferences will take only the non-propositional
 * part of the clause into account. The caller must take care of the
 * propositional part, or be sure that the propositional part is not
 * being used at all.
 */
class InferenceEngine
{
public:
  InferenceEngine() : _salg(0) {}
  virtual ~InferenceEngine()
  {
    //the object has to be detached before destruction
    ASS(!_salg);
  }
  virtual void attach(SaturationAlgorithm* salg)
  {
    ASS(!_salg);
    _salg=salg;
  }
  virtual void detach()
  {
    ASS(_salg);
    _salg=0;
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
  /**
   * Perform forward simplification on @b cl
   *
   * If a simplification is appliable on @b cl, @b keep will be
   * set to false and @b toAdd iterator will contain results of
   * the simplification. Otherwise, @b keep will be set to true,
   * and @b toAdd will contain an empty iterator.
   *
   * @b premises will contain clauses that justify the simplification
   * performed.
   */
  virtual void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises) = 0;
};


struct BwSimplificationRecord
{
  BwSimplificationRecord() {}
  BwSimplificationRecord(Clause* toRemove)
  : toRemove(toRemove), replacements(ClauseIterator::getEmpty()) {}
  BwSimplificationRecord(Clause* toRemove, Clause* replacement);
  BwSimplificationRecord(Clause* toRemove, ClauseIterator replacements)
  : toRemove(toRemove), replacements(replacements) {}

  Clause* toRemove;
  ClauseIterator replacements;
};
typedef VirtualIterator<BwSimplificationRecord> BwSimplificationRecordIterator;

class BackwardSimplificationEngine
: public InferenceEngine
{
public:
  virtual void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) = 0;
};


class DummyGIE
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise)
  {
    return ClauseIterator::getEmpty();
  }
};

class DummyFSE
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises)
  {
    keep=true;
    toAdd=ClauseIterator::getEmpty();
    premises=ClauseIterator::getEmpty();
  }
};

class DummyBSE
: public BackwardSimplificationEngine
{
public:
  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
  {
    simplifications=BwSimplificationRecordIterator::getEmpty();
  }
};


class CompositeFSE
: public ForwardSimplificationEngine
{
public:
  CompositeFSE() : _inners(0) {}
  ~CompositeFSE();
  void addFront(ForwardSimplificationEngineSP fse);
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
  void attach(SaturationAlgorithm* salg);
  void detach();
private:
  typedef List<ForwardSimplificationEngineSP> FSList;
  FSList* _inners;
};

class CompositeGIE
: public GeneratingInferenceEngine
{
public:
  CompositeGIE() : _inners(0) {}
  ~CompositeGIE();
  void addFront(GeneratingInferenceEngineSP fse);
  ClauseIterator generateClauses(Clause* premise);
  void attach(SaturationAlgorithm* salg);
  void detach();
private:
  typedef List<GeneratingInferenceEngineSP> GIList;
  GIList* _inners;
};

class DuplicateLiteralRemovalFSE
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
};

class TrivialInequalitiesRemovalFSE
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
};

};

#endif /*__InferenceEngine__*/

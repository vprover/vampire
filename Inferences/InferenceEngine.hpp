
/*
 * File InferenceEngine.hpp.
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
 * @file InferenceEngine.hpp
 * Defines class InferenceEngine
 *
 */

#ifndef __InferenceEngine__
#define __InferenceEngine__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/List.hpp"

#include "Lib/Allocator.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;
using namespace Shell;

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
  CLASS_NAME(InferenceEngine);
  USE_ALLOCATOR(InferenceEngine);

  InferenceEngine() : _salg(0) {}
  virtual ~InferenceEngine()
  {
    //the object has to be detached before destruction
    ASS(!_salg);
  }
  virtual void attach(SaturationAlgorithm* salg)
  {
    CALL("InferenceEngine::attach");
    ASS(!_salg);
    _salg=salg;
  }
  virtual void detach()
  {
    CALL("InferenceEngine::detach");
    ASS(_salg);
    _salg=0;
  }

  /**
   * Return true if inference engine is attached to a saturation algorithm
   */
  bool attached() const { return _salg; }

  virtual const Options& getOptions() const;
protected:
  SaturationAlgorithm* _salg;
};


//struct GeneratingRecord
//{
//  GeneratingRecord() {}
//  GeneratingRecord(Clause* newClause)
//  : newClause(newClause), premises(ClauseIterator::getEmpty()) {}
//  GeneratingRecord(Clause* newClause, Clause* premise);
//  GeneratingRecord(Clause* newClause, ClauseIterator premises)
//  : newClause(newClause), premises(premises) {}
//
//  Clause* newClause;
//  ClauseIterator premises;
//};

class GeneratingInferenceEngine
: public InferenceEngine
{
public:
  virtual ClauseIterator generateClauses(Clause* premise) = 0;
};

class ImmediateSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform an immediate simplification on @b cl and return
   * the result. If the simplification is not applicable, return
   * @b cl, if @b cl should be deleted, return 0.
   *
   * When the simplification yields a simplified clause, repeated
   * run of the method on resulting clause can lead to another
   * simplification.
   *
   * A trivial simplification does not depend on any other clauses.
   * The simplified clause, if any, will have just one inference
   * premise, which will be equal to @b cl.
   *
   * An example of a trivial simplification is deletion of duplicate
   * literals.
   */
  virtual Clause* simplify(Clause* cl) = 0;
};

class ForwardSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform forward simplification on @b cl
   *
   * Return true if the simplification is applicable on @b cl,
   * set @b replacement to a replacing clause if there is one (otherwise keep @b replacement = nullptr)
   *
   * @b premises will contain clauses that justify the simplification
   * performed.
   */
  virtual bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) = 0;
};


struct BwSimplificationRecord
{
  BwSimplificationRecord() {}
  BwSimplificationRecord(Clause* toRemove)
  : toRemove(toRemove), replacement(0) {}
  BwSimplificationRecord(Clause* toRemove, Clause* replacement)
  : toRemove(toRemove), replacement(replacement) {}

  Clause* toRemove;
  Clause* replacement;
};
typedef VirtualIterator<BwSimplificationRecord> BwSimplificationRecordIterator;

class BackwardSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform backward simplification with @b premise.
   *
   * Descendant classes should pay attention to the possibility that
   * the premise could be present in the simplification indexes at
   * the time of call to this method.
   */
  virtual void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) = 0;
};


class DummyGIE
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(DummyGIE);
  USE_ALLOCATOR(DummyGIE);

  ClauseIterator generateClauses(Clause* premise)
  {
    return ClauseIterator::getEmpty();
  }
};

/*
class DummyFSE
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(DummyFSE);
  USE_ALLOCATOR(DummyFSE);

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
  CLASS_NAME(DummyBSE);
  USE_ALLOCATOR(DummyBSE);

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
  {
    simplifications=BwSimplificationRecordIterator::getEmpty();
  }
};
*/

class CompositeISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CompositeISE);
  USE_ALLOCATOR(CompositeISE);

  CompositeISE() : _inners(0) {}
  virtual ~CompositeISE();
  void addFront(ImmediateSimplificationEngine* fse);
  Clause* simplify(Clause* cl);
  void attach(SaturationAlgorithm* salg);
  void detach();
private:
  typedef List<ImmediateSimplificationEngine*> ISList;
  ISList* _inners;
};

class NonOwningWrapperISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(NonOwningWrapperISE);
  USE_ALLOCATOR(NonOwningWrapperISE);

  NonOwningWrapperISE(ImmediateSimplificationEngine* inner): _inner(inner) {}
  virtual ~NonOwningWrapperISE() { /* Primarily, just don't delete inner, that's the whole and only point */ }
  Clause* simplify(Clause* cl) { return _inner->simplify(cl); }
  void attach(SaturationAlgorithm* salg) {
    _inner->attach(salg);
  }
  void detach() {
    _inner->detach();
  }
private:
  ImmediateSimplificationEngine* _inner;
};



//class CompositeFSE
//: public ForwardSimplificationEngine
//{
//public:
//  CompositeFSE() : _inners(0) {}
//  ~CompositeFSE();
//  void addFront(ForwardSimplificationEngineSP fse);
//  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
//  void attach(SaturationAlgorithm* salg);
//  void detach();
//private:
//  typedef List<ForwardSimplificationEngineSP> FSList;
//  FSList* _inners;
//};

class CompositeGIE
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(CompositeGIE);
  USE_ALLOCATOR(CompositeGIE);

  CompositeGIE() : _inners(0) {}
  virtual ~CompositeGIE();
  void addFront(GeneratingInferenceEngine* fse);
  ClauseIterator generateClauses(Clause* premise);
  void attach(SaturationAlgorithm* salg);
  void detach();
private:
  typedef List<GeneratingInferenceEngine*> GIList;
  GIList* _inners;
};

class DuplicateLiteralRemovalISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(DuplicateLiteralRemovalISE);
  USE_ALLOCATOR(DuplicateLiteralRemovalISE);

  Clause* simplify(Clause* cl);
};

class TrivialInequalitiesRemovalISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
};

};

#endif /*__InferenceEngine__*/

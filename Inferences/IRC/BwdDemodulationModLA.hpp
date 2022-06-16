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
 * @file BwdDemodulationModLA.hpp
 * Defines class BwdDemodulationModLA.hpp
 *
 */

#ifndef __IRC_BwdDemodulationModLA__
#define __IRC_BwdDemodulationModLA__

#include "Forwards.hpp"

#include "Inferences/IRC/DemodulationModLA.hpp"
#include "Indexing/TermIndex.hpp"

namespace Indexing {

class BwdDemodulationModLAIndex
: public TermIndex<>
{
  using TermIndex = Indexing::TermIndex<>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<>;
public:
  CLASS_NAME(BwdDemodulationModLAIndex);
  USE_ALLOCATOR(BwdDemodulationModLAIndex);

  BwdDemodulationModLAIndex(TermIndexingStructure* is)
    : TermIndex(is) {}

  void setShared(shared_ptr<Kernel::IrcState> shared) { _shared = std::move(shared); }
// protected:
  void handleClause(Clause* c, bool adding) final override;
private:
  shared_ptr<Kernel::IrcState> _shared;
};

} // namespace Indexing


namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BwdDemodulationModLA
: public BackwardSimplificationEngine
{
public:
  CLASS_NAME(BwdDemodulationModLA);
  USE_ALLOCATOR(BwdDemodulationModLA);

  BwdDemodulationModLA(BwdDemodulationModLA&&) = default;
  BwdDemodulationModLA(shared_ptr<IrcState> shared) 
    : _shared(shared)
    , _index(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  virtual void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) final override;
#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) override;
#endif // VDEBUG

private:
  shared_ptr<IrcState> _shared;
  BwdDemodulationModLAIndex* _index;
};

} // namespace IRC
} // namespace Inferences

#endif /*__IRC_BwdDemodulationModLA__*/

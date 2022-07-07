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
 * @file FwdDemodulationModLA.hpp
 * Defines class FwdDemodulationModLA.hpp
 *
 */

#ifndef __LASCA_FwdDemodulationModLA__
#define __LASCA_FwdDemodulationModLA__

#include "Forwards.hpp"

#include "Inferences/LASCA/DemodulationModLA.hpp"
#include "Indexing/TermIndex.hpp"

namespace Indexing {

class FwdDemodulationModLAIndex
: public TermIndex<>
{
  using TermIndex = Indexing::TermIndex<>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<>;
public:
  CLASS_NAME(FwdDemodulationModLAIndex);
  USE_ALLOCATOR(FwdDemodulationModLAIndex);

  FwdDemodulationModLAIndex(TermIndexingStructure* is)
    : TermIndex(is) {}

  void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }
// protected:
  void handleClause(Clause* cl, bool adding) final override;
private:
  template<class NumTraits> void handle(Clause* cl, Literal* lit, LascaLiteral<NumTraits> norm, bool add);
                            void handle(Clause* cl, Literal* lit, LascaLiteral<IntTraits> norm, bool add) { /* do nothing */ }

  shared_ptr<Kernel::LascaState> _shared;
};

} // namespace Indexing


namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FwdDemodulationModLA
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(FwdDemodulationModLA);
  USE_ALLOCATOR(FwdDemodulationModLA);

  FwdDemodulationModLA(FwdDemodulationModLA&&) = default;
  FwdDemodulationModLA(shared_ptr<LascaState> shared) 
    : _shared(shared)
    , _index(nullptr)
  { ASS(_shared); }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  virtual bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) override;
#endif // VDEBUG

private:
  shared_ptr<LascaState> _shared;
  FwdDemodulationModLAIndex* _index;
};

} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_FwdDemodulationModLA__*/

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
 * @file FwdDemodulation.hpp
 * Defines class FwdDemodulation.hpp
 *
 */

#ifndef __LASCA_FwdDemodulation__
#define __LASCA_FwdDemodulation__

#include "Forwards.hpp"

#include "Inferences/LASCA/Demodulation.hpp"
#include "Indexing/LascaIndex.hpp"


namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FwdDemodulation
: public ForwardSimplificationEngine
{
  using Rhs = Demodulation::Rhs;
  using Lhs = Demodulation::Lhs;
public:
  USE_ALLOCATOR(FwdDemodulation);

  FwdDemodulation(FwdDemodulation&&) = default;
  FwdDemodulation(std::shared_ptr<LascaState> shared) 
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
  std::shared_ptr<LascaState> _shared;
  // FwdDemodulationIndex* _index;
  LascaIndex<Demodulation::Lhs>* _index;
};

} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_FwdDemodulation__*/

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

#ifndef __ALASCA_Inferences_FwdDemodulation__
#define __ALASCA_Inferences_FwdDemodulation__

#include "Forwards.hpp"

#include "Inferences/ALASCA/Demodulation.hpp"
#include "Kernel/ALASCA/Index.hpp"


namespace Inferences {
namespace ALASCA {

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
  FwdDemodulation(std::shared_ptr<AlascaState> shared) 
    : _shared(shared)
    , _index(nullptr)
  { ASS(_shared); }

  void attach(SaturationAlgorithm* salg) final ;
  void detach() final ;


  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) override;
#endif // VDEBUG

private:
  std::shared_ptr<AlascaState> _shared;
  // FwdDemodulationIndex* _index;
  AlascaIndex<Demodulation::Lhs>* _index;
};

} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_FwdDemodulation__*/

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
 * @file BwdDemodulation.hpp
 * Defines class BwdDemodulation.hpp
 *
 */

#ifndef __LASCA_BwdDemodulation__
#define __LASCA_BwdDemodulation__

#include "Forwards.hpp"

#include "Inferences/LASCA/Demodulation.hpp"
#include "Indexing/LascaIndex.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BwdDemodulation
: public BackwardSimplificationEngine
{
  using Rhs = Demodulation::Rhs;
  using Lhs = Demodulation::Lhs;
public:
  USE_ALLOCATOR(BwdDemodulation);

  BwdDemodulation(BwdDemodulation&&) = default;
  BwdDemodulation(std::shared_ptr<LascaState> shared) 
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
  std::shared_ptr<LascaState> _shared;
  LascaIndex<Rhs>* _index;
};

} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_BwdDemodulation__*/

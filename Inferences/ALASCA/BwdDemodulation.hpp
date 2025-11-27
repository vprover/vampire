/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Inferences_BwdDemodulation__
#define __ALASCA_Inferences_BwdDemodulation__

#include "Forwards.hpp"

#include "Inferences/ALASCA/Demodulation.hpp"
#include "Kernel/ALASCA/Index.hpp"

namespace Inferences {
namespace ALASCA {

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
  BwdDemodulation(std::shared_ptr<AlascaState> shared) 
    : _shared(shared)
    , _index(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final ;
  void detach() final ;


  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) final ;
#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) override;
#endif // VDEBUG

private:
  std::shared_ptr<AlascaState> _shared;
  AlascaIndex<Rhs>* _index;
};

} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_BwdDemodulation__*/

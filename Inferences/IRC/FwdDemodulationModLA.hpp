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

#ifndef __IRC_FwdDemodulationModLA__
#define __IRC_FwdDemodulationModLA__

#include "Forwards.hpp"

#include "Indexing/DemodulationModLA.hpp"

namespace Inferences {
namespace IRC {

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
  FwdDemodulationModLA(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    // , _index(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  virtual bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  shared_ptr<IrcState> _shared;
  // IRCFwdDemodulationModLAIndex* _index;
};

} // namespace IRC
} // namespace Inferences

#endif /*__IRC_FwdDemodulationModLA__*/

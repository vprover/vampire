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
 * @file VariableElimination.hpp
 * Defines class VariableElimination
 *
 */

#ifndef __Inferences_ALASCA_VIRAS__
#define __Inferences_ALASCA_VIRAS__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/ALASCA/VariableElimination.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Lib/Exception.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VirasQuantifierElimination
{
  std::shared_ptr<AlascaState> _shared;
public:

  VirasQuantifierElimination(VirasQuantifierElimination&&) = default;
  explicit VirasQuantifierElimination(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared))
  {  }

  Option<VirtualIterator<Clause*>> applyOnce(Clause* premise) const;
  template<class NumTraits>
  Option<VirtualIterator<Clause*>> applyOnce(NumTraits num, Clause* premise) const;
  Option<VirtualIterator<Clause*>> applyOnce(IntTraits num, Clause* premise) const { /* TODO impl cooper quantifier elimination (?) */ return {}; }
};


class VirasQuantifierEliminationSGI
: public QuantifierEliminationSGI<VirasQuantifierElimination>
{
public:
  explicit VirasQuantifierEliminationSGI(std::shared_ptr<AlascaState> state, bool simpl = true)
    : Inferences::ALASCA::QuantifierEliminationSGI<VirasQuantifierElimination>(VirasQuantifierElimination(state), simpl)
  {  }
};


class VirasQuantifierEliminationISE
: public QuantifierEliminationISE<VirasQuantifierElimination>
{
public:
  explicit VirasQuantifierEliminationISE(std::shared_ptr<AlascaState> shared)
    : QuantifierEliminationISE<VirasQuantifierElimination>(VirasQuantifierElimination(std::move(shared)))
  {  }
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_VIRAS__*/

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
 * @file ForwardGroundJoinability.hpp
 * Defines class ForwardGroundJoinability
 *
 */

#ifndef __ForwardGroundJoinability__
#define __ForwardGroundJoinability__

#include "Forwards.hpp"

#include "Indexing/TermIndex.hpp"

#include "Kernel/VarOrder.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardGroundJoinability
: public ForwardSimplificationEngine
{
public:
  USE_ALLOCATOR(ForwardGroundJoinability);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

#if VDEBUG
  void setTestIndices(const Stack<Indexing::Index*>& indices) override { _index = static_cast<DemodulationLHSIndex*>(indices[0]); }
#endif // VDEBUG

protected:
  struct State {
    State(VarOrder&& vo, TermList s, TermList t, bool cc_s, bool cc_t, TermList orig_s, TermList orig_t)
      : vo(std::move(vo)), s(s), t(t), cc_s(cc_s), cc_t(cc_t), orig_s(orig_s), orig_t(orig_t) {}
    VarOrder vo;
    TermList s;
    TermList t;

    // these are for checking completeness
    bool cc_s;
    bool cc_t;
    TermList orig_s;
    TermList orig_t;

    vstring toString() const {
      return "s: " + s.toString() + ", t: " + t.toString() + ", vo: " + vo.to_string() + ", cc: {" + Int::toString(cc_s) + "," + Int::toString(cc_t) + "}";
    }
  };

  bool join(TermList s, TermList t, bool checkCompleteness);
  void normalise(State& state);
  bool extend(TermList& t, bool& checkCompleteness, VarOrder& ext, TermList other);

  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  DemodulationLHSIndex* _index;
  DHSet<Clause*> _premises;
};

};

#endif /*__ForwardGroundJoinability__*/

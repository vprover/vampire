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
  CLASS_NAME(ForwardGroundJoinability);
  USE_ALLOCATOR(ForwardGroundJoinability);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  static void order_diff_helper(VarOrder& vo, const List<Edge>* edges, Stack<VarOrder>& res);
  static Stack<VarOrder> order_diff(const VarOrder& vo, const VarOrder& other);

#if VDEBUG
  void setTestIndices(const Stack<Indexing::Index*>& indices) override { _index = static_cast<DemodulationLHSIndex*>(indices[0]); }
#endif // VDEBUG

protected:
  struct State {
    VarOrder vo;
    TermList s;
    TermList t;
    std::pair<bool,bool> cflags;

    vstring toString() const {
      return "s: " + s.toString() + ", t: " + t.toString() + ", vo: " + vo.to_string() + ", cc: {" + Int::toString(cflags.first) + "," + Int::toString(cflags.second) + "}";
    }
  };

  bool join(TermList s, TermList t, bool checkCompleteness);
  void normalise(TermList& s, TermList& t, const VarOrder& vo, bool& cc_s, bool& cc_t);
  bool extend(TermList& t, bool& checkCompleteness, VarOrder& ext);

  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  DemodulationLHSIndex* _index;
  DHSet<Clause*> _premises;
};

};

#endif /*__ForwardGroundJoinability__*/

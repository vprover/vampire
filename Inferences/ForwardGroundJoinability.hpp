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

protected:
  struct State {
    VarOrder vo;
    TermList s;
    TermList t;
    std::pair<bool,bool> cflags;
  };

  bool join(TermList s, TermList t, bool checkCompleteness);
  void normalise(TermList& t, const VarOrder& vo, bool& checkCompleteness);
  bool extend(TermList& t, bool& checkCompleteness, VarOrder& ext);
  void order_diff_helper(VarOrder& vo, const List<Edge>* edges, Stack<VarOrder>& res);
  Stack<VarOrder> order_diff(const VarOrder& vo, const VarOrder& other);

  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  DemodulationLHSIndex* _index;
  DHSet<Clause*> _premises;
};

};

#endif /*__ForwardGroundJoinability__*/

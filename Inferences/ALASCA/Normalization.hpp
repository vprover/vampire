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
 * @file Normalization.hpp
 * Defines class Normalization
 *
 */

#ifndef __ALASCA_Inferences_Normalization__
#define __ALASCA_Inferences_Normalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Index.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Normalization
: public ImmediateSimplificationEngine 
{
  std::shared_ptr<AlascaState> _shared;
public: 
  Normalization(std::shared_ptr<AlascaState> shared) : _shared(std::move(shared)) {}
  USE_ALLOCATOR(Normalization);

  Clause* simplify(Clause* cl) final ;
};


class FloorElimination
: public ImmediateSimplificationEngine 
{
  std::shared_ptr<AlascaState> _shared;

  template<class NumTraits>
  bool deleteableSum(Monom<NumTraits> const& l, Monom<NumTraits> const& r_) const { 
    auto r = r_.tryNumeral();
    return r.isSome() 
        && NumTraits::isFloor(l.factors->denormalize()) 
        && !(*r / l.numeral).isInt();
  }

  bool deleteableLiteral(AnyAlascaLiteral const& l) const 
  { return l.apply([&](auto l) { return deleteableLiteral(l); }); }

  bool deleteableLiteral(AlascaLiteral<IntTraits> const& l) const 
  { return false; }

  template<class NumTraits>
  bool deleteableLiteral(AlascaLiteral<NumTraits> const& l) const { 
    return l.symbol() == AlascaPredicate::EQ 
        && l.term().nSummands() == 2 
        && (  deleteableSum(l.term().summandAt(0), l.term().summandAt(1))
           || deleteableSum(l.term().summandAt(1), l.term().summandAt(0)) );
  }

public: 
  FloorElimination(std::shared_ptr<AlascaState> shared) : _shared(std::move(shared)) {}
  USE_ALLOCATOR(FloorElimination);

  Clause* simplify(Clause* cl) final {
    auto res = RStack<Literal*>();
    for (auto l : cl->iterLits()) {
      auto norm = _shared->norm().tryNormalizeInterpreted(l);
      if (norm.isSome() && deleteableLiteral(*norm)) {
        /* we the deleted literal */
      } else {
        res->push(l);
      }
    }
    return res->size() == cl->size() ? cl 
      : Clause::fromStack(*res, Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_FLOOR_ELIMINATION, cl)));
  }
};

} // namespace ALASCA
} // namespace Inferences

#endif /*__ALASCA_Inferences_Normalization__*/

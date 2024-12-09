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

#ifndef __LASCA_Normalization__
#define __LASCA_Normalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Kernel/LASCA.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Normalization
: public ImmediateSimplificationEngine 
{
  std::shared_ptr<LascaState> _shared;
public: 
  Normalization(std::shared_ptr<LascaState> shared) : _shared(std::move(shared)) {}
  USE_ALLOCATOR(Normalization);

  virtual Clause* simplify(Clause* cl) final override;
};


template<class NumTraits>
class FloorElimination
: public ImmediateSimplificationEngine 
{
  std::shared_ptr<LascaState> _shared;

  bool deleteableSum(Monom<NumTraits> const& l, Monom<NumTraits> const& r_) const { 
    auto r = r_.tryNumeral();
    return r.isSome() 
        && NumTraits::isFloor(l.factors->denormalize()) 
        && !(*r / l.numeral).isInt();
  }

  bool deleteableLiteral(LascaLiteral<NumTraits> const& l) const { 
    return l.symbol() == LascaPredicate::EQ 
        && l.term().nSummands() == 2 
        && (  deleteableSum(l.term().summandAt(0), l.term().summandAt(1))
           || deleteableSum(l.term().summandAt(1), l.term().summandAt(0)) );
  }

public: 
  FloorElimination(std::shared_ptr<LascaState> shared) : _shared(std::move(shared)) {}
  USE_ALLOCATOR(FloorElimination);


  virtual Clause* simplify(Clause* cl) final override {
    auto res = RStack<Literal*>();
    for (auto l : cl->iterLits()) {
      auto norm = _shared->norm().renormalizeLasca<NumTraits>(l);
      if (norm.isSome() && deleteableLiteral(*norm)) {
        /* we the deleted literal */
      } else {
        res->push(l);
      }
    }
    return res->size() == cl->size() ? cl 
      : Clause::fromStack(*res, Inference(SimplifyingInference1(Kernel::InferenceRule::LASCA_FLOOR_ELIMINATION, cl)));
  }
};

} // namespace LASCA
} // namespace Inferences

#endif /*__LASCA_Normalization__*/

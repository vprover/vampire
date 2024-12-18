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
 * @file Normalization.cpp
 * Implements class Normalization.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/NumTraits.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/TypeList.hpp"


#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Normalization.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/ALASCA.hpp"
#include "Indexing/TermIndexingStructure.hpp"

#define DEBUG_NORMALIZE(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

using Kernel::InequalityLiteral;

namespace Inferences {
namespace ALASCA {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


template<class NumTraits, class CheckSymbol, class Semantics>
Option<bool> groundEval(Literal* l, CheckSymbol checkSymbol, Semantics semantics) {
  if (checkSymbol(l)) {
    auto a0 = NumTraits::tryNumeral(l->termArg(0));
    auto a1 = NumTraits::tryNumeral(l->termArg(1));
    if (a0.isSome() && a1.isSome()) {
      return some(semantics(*a0, *a1) == l->polarity());
    }
  }
  return {};
}

Option<bool> trivial(Literal* l) {
  return tryNumTraits([&](auto n){
      return groundEval<decltype(n)>(l, [](auto l) { return decltype(n)::isGreater(l->functor()); }, [](auto l, auto r) { return l > r; })
          || groundEval<decltype(n)>(l, [](auto l) { return decltype(n)::isGeq    (l->functor()); }, [](auto l, auto r) { return l >= r; })
          || groundEval<decltype(n)>(l, [](auto l) { return l->isEquality()                     ; }, [](auto l, auto r) { return l == r; });
  });
}

Clause* Normalization::simplify(Clause* cl) 
{
  TIME_TRACE("perform alasca normalization")
  bool altered = false; 
  Recycled<Stack<Literal*>> out;
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = _shared->norm().normalizeLiteral((*cl)[i]);
    altered |= lit != (*cl)[i];
    auto triv = trivial(lit);
    if (triv.isSome()) {
      if (*triv) {
        /* trivialy true literal makes the literal redundant */
        return nullptr;
      } else {
        /* trivialy false literals don't have to be added to the output */
        altered = true;
      }
    } else {
      out->push(lit);
    }
  }
  if (altered) {
    Inference inf(SimplifyingInference1(Kernel::InferenceRule::ALASCA_NORMALIZATION, cl));
    auto outCl = Clause::fromStack(*out, inf);
    DEBUG_NORMALIZE(0, *cl, " ==> ", *outCl)
    return outCl;
  } else {
    DEBUG_NORMALIZE(1, *cl, " stays the same")
    return cl;
  }

}

} // namespace ALASCA
} // namespace Inferences

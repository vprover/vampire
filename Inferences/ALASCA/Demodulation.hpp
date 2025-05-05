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
 * @file Demodulation.hpp
 *
 * Shared code between  FwdDemodulation and BwdDemodulation.
 */

#ifndef __ALASCA_Inferences_Demodulation__
#define __ALASCA_Inferences_Demodulation__

#include "Forwards.hpp"
#include "Kernel/ALASCA.hpp"
#include "Kernel/TermIterators.hpp"

#define UNIMPLEMENTED ASSERTION_VIOLATION

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Demodulation
{
public:
  USE_ALLOCATOR(Demodulation);

  // ±ks + t ≈ 0          C[sσ]
  // ============================
  //         C[sσ -> (∓ (1/k) t)σ]
  // where
  // • sσ ≻ tσ
  // • C[sσ] ≻ (±ks + t ≈ 0)σ

  struct Lhs : public SelectedEquality {
    Lhs(SelectedEquality self) : SelectedEquality(std::move(self)) {}
    static const char* name() { return "alasca demodulation lhs"; }
    TypedTermList key() { return TypedTermList(SelectedEquality::biggerSide().term()); }

    static auto iter(AlascaState& shared, Clause* simplifyWith) {
      return iterTraits(iterItems(simplifyWith))
        .filter([](Clause* cl) { return cl->size() == 1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive(); })
        .flatMap([&](Clause* cl)
            { return shared.selectedEqualities(cl,
                /* literals */ SelectionCriterion::ANY,
                /* terms */    SelectionCriterion::STRICTLY_MAX,
                /* unshielded vars */ false); })
        .filter([](auto x) { return !x.biggerSide().isVar(); })
        .map([](auto x) { return Lhs(std::move(x)); })
        .timeTraced("alasca demodulation lhs");
    }
  };

  struct Rhs {
    static const char* name() { return "alasca demodulation rhs"; }
    TypedTermList term;
    bool ordOptimization;
    Clause* clause;
    auto key() const { return term; }
    auto sort() const { return SortHelper::getResultSort(term.term()); }
    auto asTuple() const { return std::tie(term, clause, ordOptimization); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs)

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << *self.clause << "[ " << self.term << " ]"; }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      // TIME_TRACE("alasca demodulation rhs")
      return iterTraits(cl->iterLits())
        .flatMap([cl](Literal* lit) {

          return iterTraits(vi(new NonVariableNonTypeIterator(lit)))
            // TODO filter our things that can never be rewritten
            .map([=](auto t) { return Rhs { .term = TypedTermList(t), .ordOptimization = !(lit->isEquality() && lit->isPositive()), .clause = cl, }; })
            ;
        })
      .timeTraced("alasca demodulation rhs");

    }
  };


  static Option<Clause*> apply(
                      AlascaState& shared,
                      Lhs lhs,               // <- { ±ks + t ≈ 0 }
                      Rhs rhs);              // <- C[sσ]

};


} // namespace ALASCA
} // namespace Inferences

#endif /*__ALASCA_Inferences_Demodulation__*/

/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Inferences_Demodulation__
#define __ALASCA_Inferences_Demodulation__

#include "Forwards.hpp"
#include "Kernel/ALASCA.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/ALASCA/Coherence.hpp"
#include "Kernel/TermIterators.hpp"

#define UNIMPLEMENTED ASSERTION_VIOLATION

#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)
namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct SuperpositionDemodConf
{
  std::shared_ptr<AlascaState> _shared;

  SuperpositionDemodConf(std::shared_ptr<AlascaState> shared) : _shared(shared) {  }

  static const char* name() { return "alasca superposition demodulation"; }

  struct Condition {
    Term* bigger;
    TermList smaller;
    Clause* cl;

    Clause* clause() const { return cl; }
    TypedTermList key() const { return bigger; };
    auto asTuple() const { return std::tie(bigger, smaller); };
    IMPL_COMPARISONS_FROM_TUPLE(Condition);
    auto smallerSide() const { return smaller; }
    auto biggerSide() const { return bigger; }

    friend std::ostream& operator<<(std::ostream& out, Condition const& self)
    { return out << self.bigger << " -> " << self.smaller; }

    static auto iter(AlascaState& shared, Clause* cl)
    { return ifElseIter(cl->size() != 1 || !(*cl)[0]->isEquality()
        , []() { return iterItems<Condition>(); }
        , [&]() { return SuperpositionConf::Lhs::iter(shared, cl)
                          .map([](auto lhs) { 
                              ASS_REP(lhs.biggerSide().isTerm(), "rewriting a variable to something does not make any sense") 
                              return Condition { .bigger = lhs.biggerSide().term(), .smaller = lhs.smallerSide(), .cl = lhs.clause()  }; }); }); }

    static const char* name() { return "superposition demod condition"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_DEMOD_CONDITION_SUBST_TREE; }
  };

  struct ToSimpl {
    Term* term;
    Clause* cl;
    Clause* clause() const { return cl; }
    TypedTermList key() const { return term; };
    auto asTuple() const { return std::tie(term, cl); };
    IMPL_COMPARISONS_FROM_TUPLE(ToSimpl);

    friend std::ostream& operator<<(std::ostream& out, ToSimpl const& self)
    { return out << *self.clause() << "[ " << *self.term << " ]"; }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      return iterTraits(cl->iterLits())
        .flatMap([=](auto lit) {
            // TODO remove the new stuff and virtualization here
            return iterTraits(vi(new NonVariableNonTypeIterator(lit)))
              .map([=](Term* t) -> ToSimpl { return ToSimpl { .term = t, .cl = cl, }; });
        });
    }

    static const char* name() { return "superposition demod toSimpl"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_DEMOD_TO_SIMPL_SUBST_TREE; }
  };

  // s ≈ t           C[sσ]       
  // ====================
  //       C[tσ]
  //
  // where
  // - sσ ≻ tσ
  // - C[sσ] ≻ (s = t)σ
  template<class Sigma>
  Option<Clause*> apply(
      Condition const& cond,
      ToSimpl const& simpl,
      Sigma sigma
      ) const 
  {
    DEBUG(1, "cond:   ", cond)
    DEBUG(1, "simpl:  ", simpl)
    auto s = cond.biggerSide();
    auto t = cond.smallerSide();
    auto sσ = simpl.key();
    auto tσ = sigma(t);


// TODO unify this aproach among all alasca rules
#define check_side_condition(cond, cond_code)                                             \
    if (!(cond_code)) {                                                                   \
      DEBUG(1, "side condition not fulfiled: ", cond)                                     \
      return {};                                                                   \
    }                                                                                     \

    ASS_EQ(sigma(TermList(s)), sσ)

    check_side_condition("sσ ≻ tσ", 
        _shared->greater(TermList(sσ), tσ))

    auto condσ = Literal::createEquality(true, sσ, tσ, sσ.sort());
    check_side_condition("C[sσ] ≻ (s ≈ t)σ", 
         /* optimization for alasca literal ordering:
          * if we have some literal L[sσ] ∈ C[sσ] that is not a positive equality, 
          * then we know that  L[sσ] ≻ (s ≈ t)σ  in alasca's literal ordering */
        (_shared->ordering->isAlascaLiteralOrdering() && 
           /* check L[sσ] ≻ (s ≈ t)σ */
           iterTraits(simpl.clause()->iterLits())
             .any([](auto lit) { return !lit->isEquality() || lit->isNegative(); }))

       || iterTraits(simpl.clause()->iterLits())
            .any([&](auto lit)
                { return _shared->greater(lit, condσ); })
        )

#undef check_side_condition

    auto cl =  Clause::fromIterator(
            iterTraits(simpl.clause()->iterLits())
              .map([&](auto lit) { return EqHelper::replace(lit, sσ, tσ); }),
            Inference(SimplifyingInference2(
                Kernel::InferenceRule::ALASCA_SUPERPOSITION_DEMOD, 
                simpl.clause(), cond.clause()))
            );
    DEBUG(1, "result: ", *cl)
    DEBUG(1, "")
    return some(cl);
  }
};

template<class NumTraits>
struct CoherenceDemodConf
{
  std::shared_ptr<AlascaState> _shared;

  CoherenceDemodConf(std::shared_ptr<AlascaState> shared) : _shared(shared) {  }

  static const char* name() { return "alasca superposition demodulation"; }

  // a clause of the form ⌊...⌋ = j s + u
  struct Condition {
    typename CoherenceConf<NumTraits>::Lhs self;

    Clause* clause() const { return self.clause(); }
    TypedTermList key() const { return self.key(); };
    auto asTuple() const { return std::tie(self); };
    IMPL_COMPARISONS_FROM_TUPLE(Condition);

    friend std::ostream& operator<<(std::ostream& out, Condition const& self)
    { return out << self.self; }

    static auto iter(AlascaState& shared, Clause* cl)
    { return ifElseIter(cl->size() != 1 || !(*cl)[0]->isEquality()
        , []() { return iterItems<Condition>(); }
        , [&]() { return CoherenceConf<NumTraits>::Lhs::iter(shared, cl)
                          .map([](auto lhs) { 
                              return Condition { .self = std::move(lhs), }; }); }); }

    static const char* name() { return "coherence demod condition"; }
    static IndexType indexType() { return Indexing::ALASCA_COHERENCE_DEMOD_CONDITION_SUBST_TREE; }
  };

  // a clause of the form D \/ L[⌊k s + t⌋]
  struct ToSimpl {
    Clause* cl;
    Term* toRewrite; // <- the term ⌊k s + t⌋
    typename CoherenceConf<NumTraits>::SharedSum ks_t; // <- the term k s + t
    unsigned sIdx; // <- the index of `s` in the sum `k s + t`

    Clause* clause() const { return cl; }
    
    TypedTermList key() const { return TypedTermList((**ks_t)[sIdx].first, NumTraits::sort()); }
    auto asTuple() const { return std::tie(cl, /* ks_t redundant */ toRewrite, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(ToSimpl);

    friend std::ostream& operator<<(std::ostream& out, ToSimpl const& self)
    { return out << *self.clause() << "[ " << *self.toRewrite << " ]"; }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      return iterTraits(cl->iterLits())
        .flatMap([&shared, cl](Literal* lit) {
            // TODO remove the new stuff and virtualization here
            return iterTraits(vi(new NonVariableNonTypeIterator(lit)))
              // .map([=](Term* t) -> ToSimpl { return ToSimpl { .term = t, .cl = cl, }; })
              .flatMap([&shared, cl](Term* toRewrite) {
                  return CoherenceConf<NumTraits>::Rhs::iterApplicableSummandsUnderFloor(shared, TermList(toRewrite))
                    .map([toRewrite,cl](auto pair) {
                        return ToSimpl {
                          .cl = cl,
                          .toRewrite = toRewrite,
                          .ks_t = pair.first,
                          .sIdx = pair.second,
                        };
                    });
               });
        });
    }

    static const char* name() { return "coherence demod toSimpl"; }
    static IndexType indexType() { return Indexing::ALASCA_COHERENCE_DEMOD_TO_SIMPL_SUBST_TREE; }
  };

  // isInt(s + t)                C[⌊sσ + u⌋]
  // =======================================
  //     C[⌊sσ + u - i(s + t)σ⌋ + i(s + t)σ]
  //
  // where
  // - i is as in the cohrerence rule
  // - sσ ≻ tσ
  // - C[sσ] ≻ isInt(s + t)σ
  template<class Sigma>
  Option<Clause*> apply(
      Condition const& cond,
      ToSimpl const& simpl,
      Sigma sigma
      ) const 
  {

    auto j = cond.self.j();
    auto k = (**simpl.ks_t)[simpl.sIdx].second;
    auto i = CoherenceConf<NumTraits>::computeI(j, k);

    return {};
//     DEBUG(1, "cond:   ", cond)
//     DEBUG(1, "simpl:  ", simpl)
//     auto s = cond.biggerSide();
//     auto t = cond.smallerSide();
//     auto sσ = simpl.key();
//     auto tσ = sigma(t);
//
//
// // TODO unify this aproach among all alasca rules
// #define check_side_condition(cond, cond_code)                                             \
//     if (!(cond_code)) {                                                                   \
//       DEBUG(1, "side condition not fulfiled: ", cond)                                     \
//       return {};                                                                   \
//     }                                                                                     \
//
//     ASS_EQ(sigma(TermList(s)), sσ)
//
//     check_side_condition("sσ ≻ tσ", 
//         _shared->greater(TermList(sσ), tσ))
//
//     auto condσ = Literal::createEquality(true, sσ, tσ, sσ.sort());
//     check_side_condition("C[sσ] ≻ (s ≈ t)σ", 
//          /* optimization for alasca literal ordering:
//           * if we have some literal L[sσ] ∈ C[sσ] that is not a positive equality, 
//           * then we know that  L[sσ] ≻ (s ≈ t)σ  in alasca's literal ordering */
//         (_shared->ordering->isAlascaLiteralOrdering() && 
//            /* check L[sσ] ≻ (s ≈ t)σ */
//            iterTraits(simpl.clause()->iterLits())
//              .any([](auto lit) { return !lit->isEquality() || lit->isNegative(); }))
//
//        || iterTraits(simpl.clause()->iterLits())
//             .any([&](auto lit)
//                 { return _shared->greater(lit, condσ); })
//         )
//
// #undef check_side_condition
//
//     auto cl =  Clause::fromIterator(
//             iterTraits(simpl.clause()->iterLits())
//               .map([&](auto lit) { return EqHelper::replace(lit, sσ, tσ); }),
//             Inference(SimplifyingInference2(
//                 Kernel::InferenceRule::ALASCA_SUPERPOSITION_DEMOD, 
//                 simpl.clause(), cond.clause()))
//             );
//     DEBUG(1, "result: ", *cl)
//     DEBUG(1, "")
//     return some(cl);
  }
};

#undef DEBUG
} // namespace ALASCA
} // namespace Inferences

#endif /*__ALASCA_Inferences_Demodulation__*/

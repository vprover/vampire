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
 * @file Coherence.hpp
 * Defines class Coherence
 *
 */

#ifndef __LASCA_Coherence__
#define __LASCA_Coherence__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/LASCA/Superposition.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "BinInf.hpp"
#include "Lib/Recycled.hpp"
#include "Shell/Options.hpp"
#include "Debug/Output.hpp"
#include "Kernel/EqHelper.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class A, class Iter>
Iter assertIter(Iter iter) {
  static_assert(std::is_same_v<A   ,ELEMENT_TYPE(Iter)> 
             && std::is_same_v<A   , decltype(iter.next())>
             && std::is_same_v<bool, decltype(iter.hasNext())>
             );
  return iter;
}

template<class NumTraits>
struct CoherenceConf
{
public:
  struct Lhs
  {
    LASCA::SuperpositionConf::Lhs _self;
    Perfect<Polynom<NumTraits>> smallerSide;
    TermList _summand;

    static const char* name() { return "lasca coherence lhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_LHS_SUBST_TREE; }

    TypedTermList key() const { return TypedTermList(_summand, NumTraits::sort()); }
    Clause* clause() const { return _self.clause(); }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Lhs::iter(shared, cl))
        .filterMap([&shared](auto lhs) { return NumTraits::ifFloor(lhs.key(), 
              [&shared, lhs](auto...) { 
                auto smallerSide = shared.normalize(lhs.smallerSide())
                        .template wrapPoly<NumTraits>();
                auto atoms = smallerSide->iterSummands()
                  .map([](auto m) { return m.factors->denormalize(); })
                  .filter([](auto f) { return !f.isVar(); });
                // TODO we can choose *any* summand for the rule to work. which summand is important though as it is our primary filter to preselect the number of potential applications in indexing. Try out which terms are good here!!!
                auto selectedAtom = atoms.tryNext();
                return selectedAtom.map([=](auto t) { return Lhs { lhs, smallerSide, t }; });
              }).flatten(); 
            });
    }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << self._self << "[" << self._summand << "]"; }

    auto asTuple() const { return std::tie(_self, _summand); }
    IMPL_COMPARISONS_FROM_TUPLE(Lhs)
  };


  struct Rhs 
  {
    LASCA::Superposition::Rhs _self;
    Perfect<Polynom<NumTraits>> polynom;
    Monom<NumTraits> _summand;

    static const char* name() { return "lasca coherence rhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_RHS_SUBST_TREE; }

    TypedTermList key() const { return TypedTermList(_summand.denormalize(), NumTraits::sort()); }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Rhs::iter(shared, cl))
        .filterMap([&shared](auto rhs) { return NumTraits::ifFloor(rhs.key(), 
              [&shared, rhs](auto t) { 
                auto polynom = shared.normalize(t).template wrapPoly<NumTraits>();
                return polynom->iterSummands()
                      .map([=](auto& m) { return Rhs{ rhs, polynom, m}; }); 
              }); 
            })
        .flatten();
    }

      

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << self._self << "[" << self._summand << "]"; }

    auto asTuple() const { return std::tie(_self, _summand); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs)
  };

  // fancyMap :: (a -> Option (Iter a)) -> Iter a -> Iter a
  // fancyMap f i = case (next i) of
  //   x : xs  -> (f x) 
  //   []      ->  []

  struct IdxEntry {
    IdxEntry(TermList t) : term(t) {}
    TermList term;
  };

  struct LIdxEntry {
    TermList term;
    unsigned equalTo;
    friend std::ostream& operator<<(std::ostream& out, LIdxEntry const& self)
    { return out << self.term << " -> " << self.equalTo; }
  };

  struct MiniIndex {
    unsigned lhsVarBank;

    Map<unsigned, RStack<unsigned>> eqClasses;
    Recycled<Stack<IdxEntry>> rhs;
    unsigned rhsVarBank;
    BacktrackData bd;

    auto unify(AbstractingUnifier& uwa, TermList l, unsigned lIdx) {
      return arrayIter(*rhs)
        .zipWithIndex()
        .filterMap([this, l, lIdx, &uwa](auto r) -> Option<AbstractingUnifier*> { 
            uwa.bdRecord(bd);
            if (uwa.unify(l, lhsVarBank, r.first.term, rhsVarBank)) {
              eqClasses.getOrInit(r.second, []() { return RStack<unsigned>(); })
                ->push(lIdx);
              uwa.bdDone();
              return some(&uwa);
            } else {
              return {};
            }
        });
    }
  };

    using N = typename NumTraits::ConstantType;

  struct SubSumUnif {
      AbstractingUnifier* uwa;
      // TODO change to ptr
      Stack<std::pair<TermList, N>> sum0; 
      unsigned bank0;
      // TODO change to ptr
      Stack<std::pair<TermList, N>> sum1;
      unsigned bank1;
      // on a return from next stack[i] = j means that sum0[i] has been unified with sum1[j - 1]
      Stack<unsigned> crossEqual;

      // Set<unsigned> sum1Classes;

      struct Sum1Class {
        Stack<unsigned> idx;
        N numeral;

      };

      Map<unsigned, std::shared_ptr<Sum1Class>> sum1ClassMap;
      Stack<unsigned> sum1ClassRoots;
      Stack<std::pair<unsigned, unsigned>> merges;

      SubSumUnif(
        AbstractingUnifier* uwa, 
        Stack<std::pair<TermList, N>> sum0,
        unsigned bank0,
        Stack<std::pair<TermList, N>> sum1,
        unsigned bank1
      ) 
        : uwa(uwa)
        , sum0(std::move(sum0))
        , bank0(bank0)
        , sum1(std::move(sum1))
        , bank1(bank1)
        , crossEqual({0}) 
        , sum1ClassRoots()
        , merges()
        {}
      DECL_ELEMENT_TYPE(SubSumUnif*);

      Option<SubSumUnif*> tryNext() {
        auto unify = [&](auto... args) {
          auto result = uwa->unify(args...);
          DBG("unify: ", std::tie(args...), " -> ", result);
          return result;
        };
        while (!merges.isEmpty()) {
          auto& pair = merges.top();
          if (pair.first >= sum1ClassRoots.size()) {
            merges.pop();

          } else if (pair.second >= sum1ClassRoots.size()) {
            pair.first++;
            pair.second = pair.first + 1;

          } else {

            auto success = unify(sum1[pair.first].first, bank1, sum1[pair.second].first, bank1);
            // TODO merge classes
            // TODO undoing saving
            pair.second++;
            if (success) {
              auto c1 = sum1ClassMap.get(sum1ClassRoots[pair.first]);
              auto c2 = sum1ClassMap.get(sum1ClassRoots.swapRemove(pair.second - 1));
              c1->numeral = c1->numeral + c2->numeral;
              c2 = c1;
              // TODO backup c1 and c2
              merges.push(std::make_pair(0,1));
              return some(this);
            }
          }
        }


        while (crossEqual.size() > 0) {
          auto i0 = crossEqual.size() - 1;
          auto i1 = crossEqual.top();
          if (i1 >= sum1.size()) {
            crossEqual.pop();
          } else {
            auto success = unify(
                sum0[i0].first, bank0, 
                sum1[i1].first, bank1);
            // TODO undo/redo
            sum1ClassMap.getOrInit(i1, [&]() {
                sum1ClassRoots.push(i1);
                return std::make_shared<Sum1Class>(Sum1Class{ .idx = { i1 }, .numeral = sum1[i1].second, });
            });
            // TODO reverting and stuff
            crossEqual.top()++;
            if (success) {
              if (crossEqual.size() == sum0.size()) {
                merges.push(std::make_pair(0,1));
                return some(this);
              } else {
                crossEqual.push(0);
              }
            }
          }
        }
        return {};
      }
  };

  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  {
    DBG("isInt: ", lhs.smallerSide)
    DBG("floor term: ", rhs.polynom)

    auto idx  = std::shared_ptr<MiniIndex>(move_to_heap(MiniIndex{
      .lhsVarBank = lhsVarBank,
      .rhs = RStack<IdxEntry>(),
      .rhsVarBank = rhsVarBank,
    }));

    for (auto m : rhs.polynom->iterSummands()) {
      auto atom = m.factors->denormalize();
      idx->rhs->push(IdxEntry(atom));
    }


    auto toStack = [](auto& x) {
      return x->iterSummands()
          .map([](auto m) { return std::make_pair(m.factors->denormalize(), m.numeral); })
          .template collect<Stack>();
    };

    struct State {

    };

    // TODO pre-compute these as stacks in the Lhs/Rhs struct
    auto ls = toStack(lhs.smallerSide);
    auto rs = toStack(rhs.polynom);

    return iterTraits(iterFromTryNext(SubSumUnif(&uwa, ls, lhsVarBank, rs, rhsVarBank)))
      .filter([&lhs, &rhs, lhsVarBank, rhsVarBank](SubSumUnif* state) {
          DBG("atoms match: ")
          DBG("lhs term: ", state->uwa->subs().apply(lhs.smallerSide->denormalize(), lhsVarBank));
          DBG("rhs term: ", state->uwa->subs().apply(rhs.polynom->denormalize(), rhsVarBank));
          if (state->uwa->maxNumberOfConstraints() != 0) {
            DBG("modulo constarints: ", *state->uwa)
          }
          return true;
      })
      .map([&lhs, &rhs, lhsVarBank, rhsVarBank](auto* state) -> Clause* {

          // TODO
          // DBGE(*bla->uwa)
          // DBG("lhs term: ", bla->uwa->subs().apply(lhs.smallerSide->denormalize(), lhsVarBank));
          // DBG("rhs term: ", bla->uwa->subs().apply(rhs.polynom->denormalize(), rhsVarBank));
          auto& subs = state->uwa->subs();
          auto u = NumTraits::ifFloor(rhs._self.toRewrite(), [](auto t) { return t; }).unwrap();
          auto t = lhs._self.smallerSide();

          auto Lσ = subs.apply(rhs._self.literal(), rhsVarBank);
          auto uσ = subs.apply(u, rhsVarBank);
          auto tσ = subs.apply(t, lhsVarBank);
          Literal* rLit = EqHelper::replace(Lσ, 
              NumTraits::floor(uσ), 
              NumTraits::add(tσ, NumTraits::floor(NumTraits::add(uσ, NumTraits::minus(tσ)))));
          auto constr= state->uwa->computeConstraintLiterals();
          
          return Clause::fromIterator(
              concatIters(
                rhs._self.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, lhsVarBank); }),
                rhs._self.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, rhsVarBank); }),
                iterItems(rLit),
                arrayIter(*constr)
              ),
              // TODO proper rule
              Inference(GeneratingInference2(InferenceRule::LASCA_COHERENCE, lhs.clause(), rhs.clause())));
      });
      // .flatMapStar([rhs, rhsVarBank, idx](AbstractingUnifier* uwa) mutable {
      //     RStack<unsigned> eqClasses;
      //     for (auto& e : iterTraits(idx->eqClasses.iter())) {
      //       eqClasses->push(e.key());
      //     }
      //     return assertIter<AbstractingUnifier*>(range(0, eqClasses->size())
      //        .flatMap([eqClasses = std::make_shared<RStack<unsigned>>(std::move(eqClasses)), uwa, rhs, rhsVarBank](auto i) mutable { return 
      //            assertIter<AbstractingUnifier*>(range(i + 1, (*eqClasses)->size())
      //              .filterMap([uwa, rhs, i, rhsVarBank, eqClasses](auto j) mutable -> Option<AbstractingUnifier*> { 
      //                  auto unif = uwa->unify(
      //                      rhs.polynom->summandAt((*eqClasses)[i]).factors->denormalize(), rhsVarBank, 
      //                      rhs.polynom->summandAt((*eqClasses)[j]).factors->denormalize(), rhsVarBank); 
      //                  return someIf(unif, [=](){ return uwa; });
      //                  }));
      //              ; }));
      // });
      //
      // // TODO the flatMapStar stuff



    // [summands] -> 

  }
};

template<class NumTraits>
struct Coherence : public BinInf<CoherenceConf<NumTraits>> {
  Coherence(std::shared_ptr<LascaState> shared) 
    : BinInf<CoherenceConf<NumTraits>>(shared, {}) 
    {}
};

#undef DEBUG

} // namespace LASCA 
} // namespace Inferences

#endif /*__LASCA_Coherence__*/

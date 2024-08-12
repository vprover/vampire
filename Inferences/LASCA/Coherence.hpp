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
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Reflection.hpp"
#include "Shell/Options.hpp"
#include "Lib/BacktrackableCollections.hpp"
#include "Debug/Output.hpp"
#include "Kernel/EqHelper.hpp"

#define DEBUG_COHERENCE(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

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
  using N = typename NumTraits::ConstantType;
  using SharedSum =  std::shared_ptr<RStack<std::pair<TermList, N>>>;
  static SharedSum toSum(LascaState& shared, TermList t) {
    RStack<std::pair<TermList, N>> rstack; 
    rstack->loadFromIterator( 
        shared.normalize(t)
          .template wrapPoly<NumTraits>()
          ->iterSummands()
          .map([](auto monom) { return std::make_pair(monom.factors->denormalize(), monom.numeral); }));
    return SharedSum(move_to_heap(std::move(rstack)));
  }
public:
  struct Lhs
  {
    LASCA::SuperpositionConf::Lhs _self;
    TermList sumTerm;
    SharedSum sum;
    unsigned _summandIdx;

    TermList atom(unsigned i) const { return (**sum)[i].first; }
    N numeral(unsigned i) const { return (**sum)[i].second; }
    unsigned nSummands() const { return (**sum).size(); }

    static const char* name() { return "lasca coherence lhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_LHS_SUBST_TREE; }

    TypedTermList key() const { return TypedTermList((*sum)[_summandIdx].first, NumTraits::sort()); }
    Clause* clause() const { return _self.clause(); }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Lhs::iter(shared, cl))
        .filterMap([&shared](auto lhs) { return NumTraits::ifFloor(lhs.key(), 
              [&shared, lhs](auto...) { 
                auto sum = toSum(shared, lhs.smallerSide());
                auto atoms = range(0, unsigned((*sum)->size()))
                  .filter([=](auto i) { return !(**sum)[i].first.isVar(); });
                // TODO we can choose *any* summand for the rule to work. which summand is important though as it is our primary filter to preselect the number of potential applications in indexing. Try out which terms are good here!!!
                auto selectedAtom = atoms.tryNext();
                return selectedAtom.map([=](auto i) { return Lhs { lhs, lhs.smallerSide(), sum, i }; });
              }).flatten(); 
            }) ;
    }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << self._self << "[" << self._summandIdx << "]"; }

    auto asTuple() const { return std::tie(_self, _summandIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Lhs)
  };


  struct Rhs 
  {
    LASCA::Superposition::Rhs _self;
    TermList sumTerm;
    SharedSum sum;
    unsigned _summandIdx;

    TermList atom(unsigned i) const { return (**sum)[i].first; }
    N numeral(unsigned i) const { return (**sum)[i].second; }
    unsigned nSummands() const { return (**sum).size(); }

    static const char* name() { return "lasca coherence rhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_RHS_SUBST_TREE; }

    TypedTermList key() const { return TypedTermList((*sum)[_summandIdx].first, NumTraits::sort()); }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Rhs::iter(shared, cl))
        .filterMap([&shared](auto rhs) { return NumTraits::ifFloor(rhs.key(), 
              [&shared, rhs](auto t) { 
                auto sum = toSum(shared, t);
                return range(0, (*sum)->size())
                      .map([=](unsigned i) { return Rhs { rhs, t, sum, i }; }); 
              }); 
            })
        .flatten();
    }

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << self._self << "[" << self._summandIdx << "]"; }

    auto asTuple() const { return std::tie(_self, _summandIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs)
  };

  // TODO coherence for varibles!!!

  struct SubSumUnif {
      AbstractingUnifier* uwa;
      Lhs const& sum0; unsigned bank0;
      Rhs const& sum1; unsigned bank1;
      // on a return from next stack[i] = j means that sum0[i] has been unified with sum1[j - 1]
      Stack<unsigned> crossEqual;
      Stack<BacktrackData> bds;

      struct Sum1Class {
        unsigned idx1;
        N numeral0;
        N numeral1;
        auto asTuple() const { return std::tie(idx1,numeral0,numeral1); }
        IMPL_COMPARISONS_FROM_TUPLE(Sum1Class);
        friend std::ostream& operator<<(std::ostream& out, Sum1Class const& self)
        { return out << self.asTuple(); }
      };

      BdDHMap<unsigned, std::shared_ptr<Sum1Class>> sum1ClassMap;
      BdStack<unsigned> sum1ClassRoots;
      Stack<std::pair<unsigned, unsigned>> merges;

      SubSumUnif(
        AbstractingUnifier* uwa, 
        Lhs const& sum0, unsigned bank0,
        Rhs const& sum1, unsigned bank1
      ) 
        : uwa(uwa)
        , sum0(sum0), bank0(bank0)
        , sum1(sum1), bank1(bank1)
        , crossEqual({0}) 
        , bds({ BacktrackData() })
        , sum1ClassRoots()
        , merges()
        {}
      DECL_ELEMENT_TYPE(SubSumUnif*);

      Option<SubSumUnif*> tryNext() {


        auto DBG_CLASSES = [&](auto... msg) {
          DBG(msg...)
          for (auto c : sum1ClassRoots) {
            auto& cls = *sum1ClassMap.get(c);
            DBG("    ", sum1.atom(cls.idx1), ": ", cls.numeral0, " ", cls.numeral1)
          }
        };
        auto unify = [&](auto... args) {
          auto result = uwa->unify(args...);
          // DBG("unify: ", std::tie(args...), " -> ", result, "(subs: ", *uwa, ")");
          return result;
        };
        while (!merges.isEmpty()) {
          auto& pair = merges.top();
          if (pair.first >= sum1ClassRoots.size()) {
            // DBG_CLASSES("before backtrack: ", merges);
            bds.pop().backtrack();
            // DBG_CLASSES("after backtrack: ", merges);
            merges.pop();

          } else if (pair.second >= sum1ClassRoots.size()) {
            // DBG_CLASSES("before backtrack: ", merges);
            bds.top().backtrack();
            // DBG_CLASSES("after backtrack: ", merges);
            pair.first++;
            pair.second = pair.first + 1;

          } else {
            DEBUG_COHERENCE(2, "merging: ", merges.top())

            uwa->bdRecord(bds.top());

            auto success = unify(sum1.atom(pair.first), bank1, sum1.atom(pair.second), bank1);
            uwa->bdDone();
            pair.second++;
            if (success) {
              auto c1 = sum1ClassMap.get(sum1ClassRoots[pair.first]);
              auto c2 = sum1ClassMap.replace(sum1ClassRoots.swapRemove(pair.second - 1, bds.top()), c1, bds.top());
              bds.top().addClosure([c1, origC1 = *c1]() {
                  *c1 = origC1;
              });
              c1->numeral0 = c1->numeral0 + c2->numeral0;
              c1->numeral1 = c1->numeral1 + c2->numeral1;
              merges.push(std::make_pair(0,1));
              bds.push(BacktrackData());
              return some(this);
            }
          }
        }


        while (crossEqual.size() > 0) {
          auto i0 = crossEqual.size() - 1;
          auto i1 = crossEqual.top();
          if (i1 >= sum1.nSummands()) {
            crossEqual.pop();
            bds.pop().backtrack();

          } else {
            bds.top().backtrack();
            uwa->bdRecord(bds.top());
            DEBUG_COHERENCE(2, "matching ", std::make_pair(i0, i1))
            auto success = unify(
                sum0.atom(i0), bank0, 
                sum1.atom(i1), bank1);
            uwa->bdDone();
            auto found = sum1ClassMap.find(i1);
            if (!found) {
              sum1ClassRoots.push(i1, bds.top());
              bds.top().addClosure([this,i1]() {
                  auto res = sum1ClassMap.remove(i1);
                  ASS_EQ(res.unwrap().second->numeral0, N(0));
              });
              sum1ClassMap.insert(i1, std::make_shared<Sum1Class>(Sum1Class{ 
                  .idx1 = i1, 
                  .numeral0 = N(0), 
                  .numeral1 = sum1.numeral(i1), 
              }));
            }
            auto& clas = *sum1ClassMap.find(i1);
            auto num0 = sum0.numeral(i0);
            clas->numeral0 += num0;
            bds.top().addClosure([clas,num0]() { clas->numeral0 -= num0; });
            crossEqual.top()++;
            if (success) {
              if (crossEqual.size() == sum0.nSummands()) {
                merges.push(std::make_pair(0,1));
                bds.push(BacktrackData());
                return some(this);
              } else {
                crossEqual.push(0);
                bds.push(BacktrackData());
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
    // DBG("isInt: ", lhs.smallerSide)
    // DBG("floor term: ", rhs.polynom)

    return iterTraits(iterFromTryNext(SubSumUnif(&uwa, lhs, lhsVarBank, rhs, rhsVarBank)))
      .filter([&lhs, &rhs, lhsVarBank, rhsVarBank](SubSumUnif* state) {
          DEBUG_COHERENCE(2, "atoms match: ")
          DEBUG_COHERENCE(2, "lhs term: ", state->uwa->subs().apply(lhs.sumTerm, lhsVarBank));
          DEBUG_COHERENCE(2, "rhs term: ", state->uwa->subs().apply(rhs.sumTerm, rhsVarBank));
          if (state->uwa->maxNumberOfConstraints() != 0) {
            DEBUG_COHERENCE(2, "modulo constarints: ", *state->uwa)
          }
          return true;
      })
      .filterMap([&lhs, &rhs, lhsVarBank, rhsVarBank](auto* state) -> Option<Clause*> {
          Option<IntegerConstantType> factor;
          for (auto c : state->sum1ClassRoots) {
            auto& cls = *state->sum1ClassMap.get(c);

            // DBG("class: ", state->sum1.atom(cls.idx1), ": ", cls.numeral0, " ", cls.numeral1)
            auto f = (cls.numeral1.abs() / cls.numeral0.abs()).floor();
            if (f == IntegerConstantType(0)) {
              DEBUG_COHERENCE(2, "factors don't fit: ", state->sum1.atom(cls.idx1), ": ", cls.numeral0, " ", cls.numeral1)
              return {};
            }
            if (cls.numeral0.sign() != cls.numeral1.sign()) {
              f = -f;
            }
            if (factor) {
              if (factor->sign() != f.sign()) {
                DEBUG_COHERENCE(2, "factors with wrong sign: ", state->sum1.atom(cls.idx1), ": ", cls.numeral0, " ", cls.numeral1)
                return {};
              } else {
                factor = some(f.abs().gcd(factor->abs()));
                if (f.sign() == Sign::Neg) {
                  *factor = -*factor;
                }
              }
            } else {
              factor = some(f);
            }
          }
          DEBUG_COHERENCE(2, "factors match with gcd: ", factor)
          DEBUG_COHERENCE(0, "match: gcd ", factor)
          DEBUG_COHERENCE(0, "lhs term: ", state->uwa->subs().apply(lhs.sumTerm, lhsVarBank));
          DEBUG_COHERENCE(0, "rhs term: ", state->uwa->subs().apply(rhs.sumTerm, rhsVarBank));
          DEBUG_COHERENCE(1, "eq classes: ")
          for (auto c1 : state->sum1ClassRoots) {
            // auto term = state->uwa->subs().apply(state->sum1ClassMap.get(c1).idx1, rhsVarBank);
            auto term = state->uwa->subs().apply(state->sum1.atom(c1), rhsVarBank);
            DEBUG_COHERENCE(1, "  ", term, "\t{ ", outputInterleaved(", ",
            range(0, state->sum0.nSummands())
              .filter([&](auto i) { return c1 == state->sum1ClassMap.get(state->crossEqual[i] - 1)->idx1; })
              .map([&](auto i) { return (**state->sum0.sum)[i]; })
              ), " }", " <--> ", "{ ", 
                outputInterleaved(", ", 
            range(0, state->sum1.nSummands())
            .filter([&](auto i) { return c1 == state->sum1ClassMap.get(i)->idx1; })
              .map([&](auto i) { return (**state->sum1.sum)[i]; })
                  )
                ," }");
          }

          auto& subs = state->uwa->subs();
          auto u = NumTraits::ifFloor(rhs._self.toRewrite(), [](auto t) { return t; }).unwrap();
          auto t = lhs._self.smallerSide();

          auto Lσ = subs.apply(rhs._self.literal(), rhsVarBank);
          auto uσ = subs.apply(u, rhsVarBank);
          auto f_tσ = NumTraits::mul(NumTraits::constantTl(*factor), subs.apply(t, lhsVarBank));
          Literal* rLit = EqHelper::replace(Lσ, 
              NumTraits::floor(uσ), 
              NumTraits::add(f_tσ, NumTraits::floor(NumTraits::add(uσ, NumTraits::minus(f_tσ)))));
          auto constr = state->uwa->computeConstraintLiterals();

          
          return some(Clause::fromIterator(
              concatIters(
                rhs._self.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, lhsVarBank); }),
                rhs._self.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, rhsVarBank); }),
                iterItems(rLit),
                arrayIter(*constr)
              ),
              Inference(GeneratingInference2(InferenceRule::LASCA_COHERENCE, lhs.clause(), rhs._self.clause()))));
      });
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

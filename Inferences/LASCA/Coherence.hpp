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

#define DEBUG_COHERENCE(lvl, ...) if (lvl < 4) DBG(__VA_ARGS__)
#define DBG_PARTITION_ITER(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

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

struct OtherPartitionIter {
  Stack<unsigned> elems;
  Stack<Stack<unsigned>> _history;
  Stack<std::pair<unsigned, unsigned>> merges;
  Set<Stack<unsigned>> set;
  unsigned depth;

  struct Subset {
    OtherPartitionIter const* parent;
    unsigned idx;
    friend std::ostream& operator<<(std::ostream& out, Subset const& self)
    { return out << "[" << 
      outputInterleaved(", ", 
        range(0, self.parent->elems.size())
        .filterMap([&](auto i) { return someIf(self.parent->_history.top()[i] == self.idx, [&]() { return self.parent->elems[i]; } ); })
        )
        << "]"; 
    }
  };

  OtherPartitionIter(unsigned N) 
    : elems(range(0, N).template collect<Stack>())
    , _history({range(0, N).template collect<Stack>()})
    , depth(0)
  {  }

  unsigned maxPartition() const { return elems.size() - _history.size(); }

  auto currentSubsets() const {
    return range(0, maxPartition() + 1) // TODO
      .map([this](auto i) { return Subset { .parent = this, .idx = i, };  });
  }

  friend std::ostream& operator<<(std::ostream& out, OtherPartitionIter const& self)
  { return out << outputInterleaved("", self.currentSubsets()); }

  unsigned parentPartAt(unsigned i) 
  { return _history.size() == 1 ? i : _history[_history.size() - 2][i]; } 

  auto merge(std::pair<unsigned, unsigned> pair) 
  { return merge(pair.first, pair.second); }


  bool merge(unsigned p0, unsigned p1) {
    auto res = merge_(p0,p1);
    return res;
  }

  bool merge_(unsigned p0, unsigned p1) {
    ASS(std::make_pair(p0,p1) == merges.top())
    // symmetry breaking: TODO explain
    if (merges.size() >= 2 && merges[merges.size() - 2].first > p0) {
      return false;
    }
    if (p0 < merges.top().first)
    ASS(p0 < p1)
    ASS(depth >= 1)
    auto p1Found = false;
    for (auto i : range(0, elems.size())) {
      auto oldVal = _history[depth - 1][i];
      if (oldVal == p0 && p1Found == 1) {
        // symmetry breaking: TODO explain
        return false;
      } else if (oldVal == p1) {
        // symmetry breaking: only allow merging singletons to partition p0
        if (p1Found) 
          return false;
        p1Found = true;
        _history[depth][i] = p0;
      } else if (oldVal > p1) {
        _history[depth][i] = oldVal - 1;
      } else {
        ASS(oldVal < p1)
        _history[depth][i] = oldVal;
      }
    }
    ASS_EQ(p1Found, 1)
    ASS_REP(!set.contains(_history.top()),  outputToString("duplicate value: ",_history.top()))
    set.insert(_history.top());
    return true;
  }

  auto maxDepth() 
  { return _history.top().size() - 1; }

  auto maxPartition() 
  { return _history.top().size() - depth; }

  bool increment(std::pair<unsigned, unsigned>& pair) {
    auto maxPartition = this->maxPartition();
    if (pair.second < maxPartition) {
      pair.second++;
      return true;
    } else {
      ASS_EQ(pair.second, maxPartition)
      pair.first++;
      pair.second = pair.first + 1;
      return pair.second <= maxPartition;
    }
  }

  bool nextPartition() {
    if (depth != maxDepth()) {
      depth++;
      _history.push(_history.top());
      merges.push(std::pair<unsigned, unsigned>(0, 1));
      if (merge(merges.top())) {
        return true;
      }
    }
    while (merges.isNonEmpty()) {
      if (increment(merges.top())) {
        if (merge(merges.top())) {
          return true;
        }
      } else {
        merges.pop();
        _history.pop();
        depth--;
      }
    }
    return false;
  }
};

struct PartitionIter {
  Stack<unsigned> elems;
  Stack<unsigned> partitions;

  struct Subset {
    PartitionIter const* parent;
    unsigned idx;
    friend std::ostream& operator<<(std::ostream& out, Subset const& self)
    { return out << "[" << 
      outputInterleaved(", ", 
        range(0, self.parent->elems.size())
        .filterMap([&](auto i) { return someIf(self.parent->partitions[i] == self.idx, [&]() { return self.parent->elems[i]; } ); })
        )
        << "]"; 
    }
  };

  PartitionIter(unsigned N) 
    : elems(range(0, N).template collect<Stack>())
    , partitions(range(0, N).template collect<Stack>())
  { }

  // TODO
  auto maxPartition() const { return arrayIter(partitions).map([](auto& x) -> unsigned { return x; }).max().unwrap(); }

  auto currentSubsets() const {
    return range(0, maxPartition() +  1)
      .map([this](auto i) { return Subset { .parent = this, .idx = i, };  });
  }

  friend std::ostream& operator<<(std::ostream& out, PartitionIter const& self)
  { return out << outputInterleaved("", self.currentSubsets()); }

  void decrement(unsigned i) {
    partitions[i]--;
    auto max = maxPartition();
    for (auto j : range(i + 1, partitions.size())) {
      partitions[j] = ++max;
    }
    ASS_EQ(maxPartition(), max)
  }

  bool isDecrementable(unsigned i) 
  { return partitions[i] != 0; }

  bool nextPartition() {
    ASS_EQ(partitions[0], 0)
    if (maxPartition() == 0) {
      return false;
    }
    for (unsigned i : range(0, partitions.size()).reverse()) {
      if (isDecrementable(i)) {
        decrement(i);
        return true;
      }
    }
    return false;
  }
};

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

  template<class Inner>
  struct Side : public Inner {

    Side(Inner inner, TermList sumTerm, SharedSum sum, unsigned idx) 
      : Inner(std::move(inner)) 
        , sumTerm(std::move(sumTerm))
        , sum(std::move(sum))
        , _summandIdx(idx) {}

    TermList sumTerm;
    SharedSum sum;
    unsigned _summandIdx;

    TermList atom(unsigned i) const { return (**sum)[i].first; }
    N numeral(unsigned i) const { return (**sum)[i].second; }
    unsigned nSummands() const { return (**sum).size(); }

    static const char* name() { return "lasca coherence lhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_LHS_SUBST_TREE; }

    TypedTermList key() const { return TypedTermList((*sum)[_summandIdx].first, NumTraits::sort()); }

    friend std::ostream& operator<<(std::ostream& out, Side const& self)
    { return out << (Inner const&)self << "[" << self._summandIdx << "]"; }

    auto asTuple() const { return std::tuple_cat(Inner::asTuple(), std::tie(_summandIdx)); }
    IMPL_COMPARISONS_FROM_TUPLE(Side)
  };


  struct Lhs : public Side<LASCA::SuperpositionConf::Lhs>
  {
    using Side<LASCA::SuperpositionConf::Lhs>::Side;
    static const char* name() { return "lasca coherence lhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_LHS_SUBST_TREE; }

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
                return selectedAtom.map([=](auto i) { return Lhs( lhs, lhs.smallerSide(), sum, i ); });
              }).flatten(); 
            }) ;
    }
  };

  struct Rhs : public Side<LASCA::Superposition::Rhs>
  {
    using Side<LASCA::SuperpositionConf::Rhs>::Side;
    static const char* name() { return "lasca coherence rhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_RHS_SUBST_TREE; }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Rhs::iter(shared, cl))
        .filterMap([&shared](auto rhs) { return NumTraits::ifFloor(rhs.key(), 
              [&shared, rhs](auto t) { 
                auto sum = toSum(shared, t);
                return range(0, (*sum)->size())
                      .map([=](unsigned i) { return Rhs(LASCA::Superposition::Rhs(rhs), t, sum, i); }); 
              }); 
            })
        .flatten();
    }
  };

  // TODO coherence for varibles!!!

  struct SubSumUnif {

      struct Sum1Class {
        unsigned idx1;
        N numeral0;
        N numeral1;
        auto asTuple() const { return std::tie(idx1,numeral0,numeral1); }
        IMPL_COMPARISONS_FROM_TUPLE(Sum1Class);
        friend std::ostream& operator<<(std::ostream& out, Sum1Class const& self)
        { return out << self.asTuple(); }
      };

      AbstractingUnifier* uwa;
      Lhs const& sum0; unsigned bank0;
      Rhs const& sum1; unsigned bank1;
      // on a return from next stack[i] = j means that sum0[i] has been unified with sum1[j - 1]
      Stack<unsigned> crossEqual;
      Stack<BacktrackData> bds;

      // TODO use RStack everywhere
      // every element is a sorted stack of indices. 
      //
      // partitions[0] subset {1 .. N}
      // partitions[1] subset {1 .. N - partitions[0].size()}
      // partitions[2] subset {1 .. N - partitions[0].size() - partitions[1].size()}
      // ...
      // partitions[n] subset {1 .. N - partitions[0].size() ... - partitions[n - 1].size()}
      //
      // They encode partittions as follows:
      //
      // - We have n partitions of the set {0 .. N}
      // - i in partition 0 <=> i == 0 or i in partitions[0]
      // - i in partition 1 <=>     i - partitions[0].size() - 1 == 0
      //                        or  i - partitions[0].size() - 1 in partitions[1]
      // - i in partition 2 <=>     i - partitions[0].size() - 1 - partitions[1].size() - 1 == 
      //                        or  i - partitions[0].size() - 1 - partitions[1].size() - 1 in partitions[2]
      // ...
      // - i in partition j <=>     i - partitions[0].size() - 1 ... - partitions[j].size() - 1 == 
      //                        or  i - partitions[0].size() - 1 ... - partitions[1].size() - 1 in partitions[2]
      Stack<Stack<unsigned>> partitions;


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
        , partitions()
        , sum1ClassRoots()
        , merges()
        {
        }
      DECL_ELEMENT_TYPE(SubSumUnif*);

      

      bool nextPartition() {
        auto last = partitions.pop();
        auto left = last.size();
        if (partitions.size() == 0) {
          return false;
        } else {
          auto p = partitions.top();
          auto pSize = p.size();
          auto topSize = p.size() + 1 + left;
        
          /* trying to count up */

          /* popping "overflowing digits" */
          auto leftCnt = 0;
          while(p.top() == topSize - leftCnt) {
            p.pop();
            leftCnt++;
          }

          if (p.isEmpty()) {
            /* counting up not possible. we need to grow p */
            p.loadFromIterator(range(1, pSize + 2));
            left--;
          } else {
            /* actual counting up */
            p.top()++;
            while (leftCnt != 0) {
              leftCnt--;
              p.push(p.top() + 1);
            }
            ASS_EQ(p.size(), pSize)
          }
          while (left != 0) {
            partitions.push(Stack<unsigned>());
            left--;
          }
        }
      }

      Option<SubSumUnif*> tryNext() {
        

        // auto DBG_CLASSES = [&](auto... msg) {
        //   DBG(msg...)
        //   for (auto c : sum1ClassRoots) {
        //     auto& cls = *sum1ClassMap.get(c);
        //     DBG("    ", sum1.atom(cls.idx1), ": ", cls.numeral0, " ", cls.numeral1)
        //   }
        // };
        auto unify = [&](auto... args) {
          auto result = uwa->unify(args...);
          // DBG("unify: ", std::tie(args...), " -> ", result, "(subs: ", *uwa, ")");
          return result;
        };
        while (!merges.isEmpty()) {
          auto& pair = merges.top();
          DBGE(sum1ClassRoots)
          if (pair.first >= sum1ClassRoots.size()) {
            bds.pop().backtrack();
            merges.pop();

          } else if (pair.second >= sum1ClassRoots.size()) {
            bds.top().backtrack();
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
            DEBUG_COHERENCE(2, "matching ", outputInterleaved(", ", 
                  arrayIter(crossEqual, crossEqual.size() - 1)
                    .zipWithIndex()
                    .map([](auto x){ return std::make_tuple(x.second, x.first - 1); })),
                ", ", std::make_pair(i0, i1));
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
          auto u = NumTraits::ifFloor(rhs.toRewrite(), [](auto t) { return t; }).unwrap();
          auto t = lhs.smallerSide();

          auto Lσ = subs.apply(rhs.literal(), rhsVarBank);
          auto uσ = subs.apply(u, rhsVarBank);
          auto f_tσ = NumTraits::mul(NumTraits::constantTl(*factor), subs.apply(t, lhsVarBank));
          Literal* rLit = EqHelper::replace(Lσ, 
              NumTraits::floor(uσ), 
              NumTraits::add(f_tσ, NumTraits::floor(NumTraits::add(uσ, NumTraits::minus(f_tσ)))));
          auto constr = state->uwa->computeConstraintLiterals();

          
          return some(Clause::fromIterator(
              concatIters(
                rhs.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, lhsVarBank); }),
                rhs.contextLiterals()
                  .map([&](auto lit) { return subs.apply(lit, rhsVarBank); }),
                iterItems(rLit),
                arrayIter(*constr)
              ),
              Inference(GeneratingInference2(InferenceRule::LASCA_COHERENCE, lhs.clause(), rhs.clause()))));
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

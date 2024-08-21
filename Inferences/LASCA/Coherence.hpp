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

template<class MergeFilter>
struct MergingPartitionsIterRaw 
{
  Stack<unsigned> _elems;
  Recycled<DArray<unsigned>> _history;
  RStack<std::pair<unsigned, unsigned>> _merges;
  bool _finished;
  MergeFilter _filter;
  unsigned  _filterMerges;
#if VDEBUG
  Set<Stack<unsigned>> set;
#endif // VDEBUG

  struct Subset {
    MergingPartitionsIterRaw const* parent;
    unsigned idx;
    unsigned depth;
    friend std::ostream& operator<<(std::ostream& out, Subset const& self)
    { return out << "[" << 
      outputInterleaved(", ", self.toIter())
        << "]"; 
    }

    auto toStack() const 
    { return toIter().template collect<Stack>(); }

    auto toIter() const
    {
      return range(0, parent->_elems.size())
        .filterMap([&](auto i) { return someIf(parent->partitionOf(depth, i) == idx, [&]() { return parent->_elems[i]; } ); });
    }
  };

  MergingPartitionsIterRaw(unsigned N, MergeFilter filter) 
    : _elems(range(0, N).template collect<Stack>())
    , _history()
    , _finished(false)
    , _filter(std::move(filter))
    , _filterMerges(0)
  { 
    _history->ensure(N * N);
    for (auto i : range(0, N)) {
      partitionOf(0, i) = i;
    }
  }

  auto subset(unsigned depth, unsigned idx) const {
    return Subset { .parent = this, .idx = idx, .depth = depth, };
  }


  auto subsets(unsigned depth) const {
    return range(0, maxPartition(depth) + 1)
      .map([this, depth](auto i) { return this->subset(depth, i);  });
  }

  auto currentSubsets() const 
  { return subsets(depth()); }

  friend std::ostream& operator<<(std::ostream& out, MergingPartitionsIterRaw const& self)
  { return out << outputInterleaved("", self.currentSubsets()); }

  auto merge(std::pair<unsigned, unsigned> pair) 
  { return merge(pair.first, pair.second); }

  bool merge(unsigned p0, unsigned p1) {
    auto res = merge_(p0,p1);
    return res;
  }

  unsigned currentMaxPartition() const { return maxPartition(depth()); }
  unsigned maxPartition(unsigned depth) const { return _elems.size() - 1 - depth; }

  unsigned& partitionOf(unsigned depth, unsigned elem) 
  { return (*_history)[depth * _elems.size() + elem]; }

  unsigned const& partitionOf(unsigned depth, unsigned elem) const 
  { return (*_history)[depth * _elems.size() + elem]; }

  auto partition(unsigned depth) 
  { return range(0, _elems.size()).map([this,depth](auto i) { return this->partitionOf(depth, i); }); }

  auto lastPartition() 
  { return partition(depth()); }

  bool merge_(unsigned p0, unsigned p1) {
    ASS(std::make_pair(p0,p1) == _merges->top())
    // symmetry breaking: TODO explain
    if (_merges->size() >= 2 && (*_merges)[_merges.size() - 2].first > p0) {
      return false;
    }
    if (p0 < _merges->top().first)
    ASS(p0 < p1)
    ASS(depth() >= 1)
    // auto p1Found = false;
    Option<unsigned> i0 = {};
    Option<unsigned> i1 = {};
    for (auto i : range(0, unsigned(_elems.size()))) {
      auto oldVal = partitionOf(depth() - 1,i);
      if (oldVal == p0 && i0.isNone()) {
        i0 = some(i);
      }
      if (oldVal == p0 && i1.isSome()) {
        // symmetry breaking: TODO explain
        return false;
      } else if (oldVal == p1) {
        // symmetry breaking: only allow merging singletons to partition p0
        if (i1) 
          return false;
        i1 = some(i);
        partitionOf(depth(),i) = p0;
      } else if (oldVal > p1) {
        partitionOf(depth(),i) = oldVal - 1;
      } else {
        ASS(oldVal < p1)
        partitionOf(depth(),i) = oldVal;
      }
    }
    ASS(i0.isSome())
    ASS(i1.isSome())
#if VDEBUG
    { /* compute set of all partitions for debugging purposes */
      auto lastPart = lastPartition().template collect<Stack>();
      ASS_REP(!set.contains(lastPart),  outputToString("duplicate value: ",lastPart))
      set.insert(lastPart);
    }
#endif // VDEBUG
    // DBG(outputInterleaved("", subsets(depth() - 1)), ".merge(", p0, ", ",  p1, ") -> ", outputInterleaved("", subsets(depth())))
    while (_filterMerges != depth() - 1) {
      _filter.undoLastMerge();
      _filterMerges--;
    }
    auto merged = _filter.tryMerge(p0, *i0, p1, *i1);
    // DBG("tryMerge(", p0, ", ", *i0, ", ", p1, ", ", *i1,") = ", merged)
    if (merged) {
      _filterMerges++;
      return true;
    } else {
      return false;
    }
  }

  auto maxDepth() 
  { return _elems.size() - 1; }

  bool increment(std::pair<unsigned, unsigned>& pair) {
    auto oldMaxPartition = this->currentMaxPartition() + 1;
    if (pair.second < oldMaxPartition) {
      pair.second++;
      return true;
    } else {
      ASS_EQ(pair.second, oldMaxPartition)
      pair.first++;
      pair.second = pair.first + 1;
      return pair.second <= oldMaxPartition;
    }
  }

  unsigned depth() const { return _merges->size(); }

  bool nextPartition() 
  {
    if (_finished) return false;

    if (depth() != maxDepth()) {
      _merges->push(std::pair<unsigned, unsigned>(0, 1));
      do {
        if (merge(_merges->top())) {
          return true;
        }
      } while (increment(_merges->top()));
      _merges->pop();
    }

    while (_merges->isNonEmpty()) {
      if (increment(_merges->top())) {
        if (merge(_merges->top())) {
          return true;
        }
      } else {
        _merges->pop();
      }
    }
    _finished = true;
    return false;

    if (depth() != maxDepth()) {
      _merges->push(std::pair<unsigned, unsigned>(0, 1));
      if (merge(_merges->top())) {
        return true;
      }
    }
    while (_merges->isNonEmpty()) {
      if (increment(_merges->top())) {
        if (merge(_merges->top())) {
          return true;
        }
      } else {
        _merges->pop();
      }
    }
    _finished = true;
    return false;
  }
};

template<class Filter>
struct MergingPartitionsIter {
  MergingPartitionsIterRaw<Filter> _self;
  bool _initial;
  MergingPartitionsIter(unsigned N, Filter filter) 
    : _self(N, std::move(filter)) 
    , _initial(true)
    {}

  DECL_ELEMENT_TYPE(Filter const*);

  Option<Filter const*> tryNext() {
    if (_initial) {
      _initial = false;
      return some(static_cast<Filter const*>(&this->_self._filter));
    } else {
      return someIf(_self.nextPartition(), [&]() { return static_cast<Filter const*>(&this->_self._filter); });
    }
  }
};

template<class MergeFilter>
MergingPartitionsIterRaw<MergeFilter> mergingPartitionIterRaw(unsigned N, MergeFilter filter)
{ return MergingPartitionsIterRaw<MergeFilter>(N, std::move(filter)); }

template<class MergeFilter>
MergingPartitionsIter<MergeFilter> mergingPartitionIter(unsigned N, MergeFilter filter)
{ return MergingPartitionsIter<MergeFilter>(N, std::move(filter)); }

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

      struct UnificationMergeFilter {
        AbstractingUnifier* unifier;
        Rhs const& sum1;
        unsigned bank1;
        Stack<BacktrackData> bds;
        Stack<Stack<std::pair<unsigned, N>>> allClasses;
        friend std::ostream& operator<<(std::ostream& out, UnificationMergeFilter const& self)
        { return out << self.allClasses; }

        UnificationMergeFilter(
                AbstractingUnifier* unifier,
                Rhs const& sum1,
                unsigned bank1)
        : unifier(unifier)
        , sum1(sum1)
        , bank1(bank1)
        , bds()
        , allClasses({ range(0, sum1.nSummands())
            .map([&](auto i) { return std::make_pair(i, sum1.numeral(i)); })
            .template collect<Stack>() })
        {}

        unsigned nPartitions() const { return allClasses.top().size(); }
        TermList atom(unsigned partition) const { return sum1.atom(allClasses.top()[partition].first); }
        N numeral1(unsigned partition) const { return allClasses.top()[partition].second; }

        void undoLastMerge() { return bds.pop().backtrack(); }

        bool tryMerge(unsigned p0, unsigned i0, unsigned p1, unsigned i1) {
          bds.push(BacktrackData());
          unifier->bdRecord(bds.top());
          auto success = unifier->unify(sum1.atom(i0), bank1, sum1.atom(i1), bank1);
          unifier->bdDone();
          if (!success) {
            bds.pop();
          } else {
            ASS(p0 < p1);
            Stack<std::pair<unsigned, N>> newClasses;
            auto& oldClasses = allClasses.top();
            newClasses.reserve(oldClasses.size() - 1);
            for (unsigned i : range(0, oldClasses.size())) {
              if (i != p0 && i != p1) {
                newClasses.push(oldClasses[i]);
              } else if (i == p0) {
                newClasses.push(oldClasses[i]);
                newClasses[i].second += oldClasses[p1].second;
              } else {
                ASS_EQ(i, p1)
                /* skip */
              }
            }
            allClasses.push(std::move(newClasses));
            bds.top().addClosure([this]() { allClasses.pop(); });
          }
          return success;
        }
      };

      AbstractingUnifier* uwa;
      Lhs const& sum0; unsigned bank0;
      Rhs const& sum1; unsigned bank1;
      MergingPartitionsIterRaw<UnificationMergeFilter> sum1Partitions;
      bool partitionsFinished;

      // on a return from next stack[i] = j means that sum0[i] has been unified with sum1[j - 1]
      Stack<unsigned> crossEqual;
      // crossEqualNumSum[i] = n means the sum of all sum0 that are matched to currentSum1Partition[i] is n
      Stack<N> crossEqualNumSum;
      Stack<BacktrackData> bds;
      Option<std::pair<unsigned, unsigned>> preUnif;

      SubSumUnif(
        AbstractingUnifier* uwa, 
        Lhs const& sum0, unsigned bank0,
        Rhs const& sum1, unsigned bank1
      ) : SubSumUnif(uwa, 
        sum0, bank0,
        sum1, bank1,
        Option<std::pair<unsigned, unsigned>>()
        )
      { }


      SubSumUnif(
        AbstractingUnifier* uwa, 
        Lhs const& sum0, unsigned bank0,
        Rhs const& sum1, unsigned bank1,
        Option<std::pair<unsigned, unsigned>> preUnif
      ) 
        : uwa(uwa)
        , sum0(sum0), bank0(bank0)
        , sum1(sum1), bank1(bank1)
        , sum1Partitions(mergingPartitionIterRaw(sum1.nSummands(), UnificationMergeFilter{uwa, sum1, bank1}))
        , partitionsFinished(false)
        , crossEqual() 
        , crossEqualNumSum(range(0, sum1.nSummands()).map([](auto) { return N(0); }).template collect<Stack>())
        , bds()
        , preUnif(std::move(preUnif))
      {
        pushCrossEqual();
      }

      void pushCrossEqual() {
        if (preUnif.isSome() && crossEqual.size() == preUnif->first) {
          crossEqual.push(sum1Partitions.partitionOf(sum1Partitions.depth(), preUnif->second));
          bds.push(BacktrackData());
        } else {
          crossEqual.push(0);
          bds.push(BacktrackData());
        }
      }


      DECL_ELEMENT_TYPE(SubSumUnif*);

      Option<SubSumUnif*> tryNext() {

        auto unify = [&](auto... args) {
          auto result = uwa->unify(args...);
          // DBG("unify: ", std::tie(args...), " -> ", result, "(subs: ", *uwa, ")");
          return result;
        };
       
        while (!partitionsFinished) {
          ASS_EQ(crossEqualNumSum.size(), sum1Partitions._filter.nPartitions())
          while (crossEqual.size() > 0) {
            auto i0 = crossEqual.size() - 1;
            auto i1 = crossEqual.top();
            if (i1 >= sum1Partitions._filter.nPartitions() 
                || (preUnif.isSome() && preUnif->first == i0 && i1 == 1 + sum1Partitions.partitionOf(sum1Partitions.depth(), preUnif->second))) {
              crossEqual.pop();
              bds.pop().backtrack();

            } else {
              bds.top().backtrack();

              bool success;
              if (preUnif.isSome() && preUnif->first == i0) {
                /* we already know that they two are unified */
                success = true;
              } else {
                uwa->bdRecord(bds.top());
                DEBUG_COHERENCE(2, "matching ", outputInterleaved(", ", 
                      arrayIter(crossEqual, crossEqual.size() - 1)
                        .zipWithIndex()
                        .map([](auto x){ return std::make_tuple(x.second, x.first - 1); })),
                    ", ", std::make_pair(i0, i1));
                success = unify(
                    sum0.atom(i0), bank0, 
                    sum1Partitions._filter.atom(i1), bank1);
                uwa->bdDone();
              }

              auto num0 = sum0.numeral(i0);
              crossEqualNumSum[i1] += num0;
              bds.top().addClosure([this, i1, num0]() { crossEqualNumSum[i1] -= num0; });
              crossEqual.top()++;
              if (success) {
                if (crossEqual.size() == sum0.nSummands()) {
                  return some(this);
                } else {
                  pushCrossEqual();
                }
              }
            }
          }
          partitionsFinished = !sum1Partitions.nextPartition();
          if (!partitionsFinished) {
            if (crossEqualNumSum.size() > sum1Partitions._filter.nPartitions()) {
              crossEqualNumSum.pop(crossEqualNumSum.size() - sum1Partitions._filter.nPartitions());
            } else {
              crossEqualNumSum.loadFromIterator(range(0, sum1Partitions._filter.nPartitions() - crossEqualNumSum.size()).map([](auto) { return N(0); }));
            }
            ASS(crossEqualNumSum.size() == sum1Partitions._filter.nPartitions())
            ASS_EQ(crossEqual.size(), 0)
            ASS_EQ(bds.size(), 0)
            pushCrossEqual();
          }
        }
        ASS_EQ(bds.size(), 0)
        while (sum1Partitions._filter.bds.isNonEmpty()) {
          sum1Partitions._filter.bds.pop().backtrack();
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
    return iterTraits(iterFromTryNext(SubSumUnif(&uwa, lhs, lhsVarBank, rhs, rhsVarBank, 
            some(std::make_pair(lhs._summandIdx, rhs._summandIdx)))))
      .filterMap([&lhs, &rhs, lhsVarBank, rhsVarBank](SubSumUnif* state) -> Option<Clause*> {

          // DBGE(state->sum1Partitions)
          // DBGE(state->crossEqual)

          Option<IntegerConstantType> factor;
          for (auto i : range(0, state->sum1Partitions._filter.nPartitions())) {
            auto numeral1 = state->sum1Partitions._filter.numeral1(i);
            auto numeral0 = state->crossEqualNumSum[i];
            if (numeral0 != N(0)) {
              auto f = (numeral1.abs() / numeral0.abs()).floor();
              if (f == IntegerConstantType(0)) {
                DEBUG_COHERENCE(2, "factors don't fit: ", state->sum1Partitions._filter.atom(i), ": ", numeral0, " ", numeral1)
                return {};
              }
              if (numeral0.sign() != numeral1.sign()) {
                f = -f;
              }
              if (factor) {
                if (factor->sign() != f.sign()) {
                  DEBUG_COHERENCE(2, "factors with wrong sign: ", state->sum1Partitions._filter.atom(i), ": ", numeral0, " ", numeral1)
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
          }

          DEBUG_CODE(
            DEBUG_COHERENCE(0, "atoms match: ")
            DEBUG_COHERENCE(0, "lhs term: ", state->uwa->subs().apply(lhs.sumTerm, lhsVarBank));
            DEBUG_COHERENCE(0, "rhs term: ", state->uwa->subs().apply(rhs.sumTerm, rhsVarBank));
            if (state->uwa->maxNumberOfConstraints() != 0) {
              DEBUG_COHERENCE(0, "modulo constarints: ", *state->uwa)
            }
            DEBUG_COHERENCE(1, "factors match with gcd: ", factor)
            DEBUG_COHERENCE(1, "eq classes: ")

            for (auto p : range(0, state->sum1Partitions._filter.nPartitions())) {
              DEBUG_COHERENCE(1, "  ", "\t{ ", 
                outputInterleaved(", ",
                  range(0, state->sum0.nSummands())
                    .filter([&](auto i) { return p == state->crossEqual[i] - 1; })
                .map([&](auto i) { return (**state->sum0.sum)[i]; })
                ), " }", " <--> ", "{ ", 
                  outputInterleaved(", ", 
                    state->sum1Partitions.subset(state->sum1Partitions.depth(), p).toIter()
                      .map([&](auto i) { return (**state->sum1.sum)[i]; })
                    )
                  ," }");
            }
          ) // DEBUG_CODE

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
                arrayIter(*constr)),
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

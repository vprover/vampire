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
 * @file VariableElimination.cpp
 * Defines class VariableElimination
 *
 */

#include "VariableElimination.hpp"
#include "Lib/Map.hpp"
#include "Lib/Set.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/TermIterators.hpp"

#define TODO ASSERTION_VIOLATION
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING STUFF
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  
void VariableElimination::attach(SaturationAlgorithm* salg) 
{ }

void VariableElimination::detach() 
{ }

#if VDEBUG
void VariableElimination::setTestIndices(Stack<Indexing::Index*> const&) 
{ }
#endif

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ACTUAL RULE
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Option<VariableElimination::AnyFoundVariable> VariableElimination::findUnshieldedVar(Clause* premise) const
{
  Stack<Variable> vars; // contains the same data as the keys in the map. just there to deterministically iterate over map entries.
  Map<Variable, AnyFoundVariable, StlHash> unshielded;
  Set<Variable, StlHash> shielded;
  for (unsigned i = 0; i < premise->size(); i++) {
    auto lit = (*premise)[i];
    auto norm = _shared->norm().tryNormalizeInterpreted(lit);
    if (norm.isSome()) {
      norm.unwrap().apply([&](auto& lit) -> void {
      //                            ^^^-->  t1 + ... + tn <> 0 
        using NumTraits = typename std::remove_reference<decltype(lit)>::type::NumTraits;
        for (auto s : lit.term().iterSummands()) {
          // lit = t1 + ... + s + ... + tn <> 0 
          auto k = s.numeral;
          auto var = s.factors->tryVar();
          if (var.isSome()) {
            auto v = var.unwrap();
    
            // lit = t1 + ... + k * v + ... + tn <> 0  
            if (!shielded.contains(v)) {
              auto& found = unshielded.getOrInit(v, [&]() { 
                                           vars.push(v);
                                           return AnyFoundVariable(FoundVariable<NumTraits>(s.factors)); 
                                         })
                                       .template unwrap<FoundVariable<NumTraits>>();
              auto entry = FoundVarInLiteral<NumTraits>(i, k, lit);
              switch(lit.symbol()) {
              case AlascaPredicate:: EQ: found. eq.push(std::move(entry)); break;
              case AlascaPredicate::NEQ: found.neq.push(std::move(entry)); break;
              case AlascaPredicate::GREATER:
              case AlascaPredicate::GREATER_EQ:
                      if (k.isPositive()) found.posIneq.push(std::move(entry));
                 else if (k.isNegative()) found.negIneq.push(std::move(entry));
                 else { ASSERTION_VIOLATION_REP(*premise) }
                 break;
              }
            }
          } else {

            // lit = t1 + ... + k * f(...) + ... + tn <> 0  
            for (auto t : s.factors->iterSubterms()) {
              t.tryVar()
               .andThen([&](auto var) 
                   { shielded.insert(var); });
            }
          }
        }
      });
    } else {
      VariableIterator vars(lit);
      while (vars.hasNext()) {
        auto v = Variable(vars.next().var());
        shielded.insert(v);
      }
    }
  }
  auto out = Option<AnyFoundVariable>();

  for (auto v : vars) {
    if (!shielded.contains(v)) {
      auto& var = unshielded.get(v);
      if (out.isNone() 
          || (!isOneSideBounded(out.unwrap()) && isOneSideBounded(var))) {
        out = Option<AnyFoundVariable>(std::move(var));
      }
    }
  }
  return out;
}

SimplifyingGeneratingInference::ClauseGenerationResult VariableElimination::generateSimplify(Clause* premise) 
{
  TIME_TRACE("alasca variable elimination generate")
  auto var = this->findUnshieldedVar(premise);
  if (var.isSome()) {
    return ClauseGenerationResult {
      .clauses          = std::move(var).unwrap().apply([&](auto var) { return applyRule(premise, std::move(var)); }),
      .premiseRedundant = _simplify,
    };
  } else {
    return ClauseGenerationResult {
      .clauses          = ClauseIterator::getEmpty(),
      .premiseRedundant = false,
    };
  }
}

// C \/ { x + bi >i 0 | i ∈ I } \/ { -x + bj >j 0 | j ∈ J } \/ { x + bk == 0 | k ∈ K } \/ { x + bh /= 0 | l ∈ L }
// ==========================================================================================================================
// C \/ { bi + bj >ij 0 | i ∈ I, j ∈ J } \/ {  bi - bk  >= 0 |   i ∈ I,   k ∈ Km } \/ {  bi - bl  >i 0 |  i ∈ I,  l ∈ L }
//                                       \/ {  bj + bk  >= 0 |   j ∈ J,   k ∈ Kp } \/ {  bj + bl  >j 0 |  j ∈ J,  l ∈ L }
//                                       \/ { bk1 - bk2 >= 0 |  k1 ∈ Kp, k2 ∈ Km } \/ {  bk - bl  >= 0 |  k ∈ Kp, l ∈ L }              <--- row not common
//                                                                                 \/ {  bl - bk  >= 0 |  k ∈ Km, l ∈ L }              <--- row not common
//                                                                                 \/ { bl1 - bl2 /= 0 | ordered pairs (l1, l2) of L }
//                                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^<-------------------------------------------------------- col not common
//
// for all partitions (Kp, Km) of K

template<class A>
class PartitionIter {
  Stack<A> _orig;
  Option<std::vector<bool>> _partition;
  bool _finished;
public:
  DECL_ELEMENT_TYPE(PartitionIter&);
  PartitionIter(Stack<A> orig) : _orig(std::move(orig)), _partition(), _finished(false) {}
  bool hasNext() { return !_finished; }
  PartitionIter& next() { 
    if (_partition.isNone()) {
      _partition = some(std::vector<bool>(_orig.size(), false));
      if (_orig.size() == 0) {
        _finished = true;
      }
    } else {
      auto& par = _partition.unwrap();
      unsigned i = 0;
      for (; par[i]; i++) {
        par[i] = !par[i];
      }
      par[i] = !par[i];
      if (i + 1 >= _orig.size()) {
        _finished = true;
      }
    }
    return *this;
  }

  auto partition(bool lhs) 
  { return iterTraits(getRangeIterator((unsigned)0, (unsigned)_orig.size()))
      .filterMap([this, lhs](auto i) -> Option<A&> { return _partition.unwrap()[i] == lhs ? Option<A&>(_orig[i]) : Option<A&>(); }); }

  auto partitionSize(bool lhs) 
  { return iterTraits(range(0, (unsigned)_orig.size()))
      .filter([this, lhs](auto i) { return _partition.unwrap()[i] == lhs; })
      .count(); }

  friend std::ostream& operator<<(std::ostream& out, PartitionIter const& self)
  {
    out << "[";
    for (auto b : self._partition.unwrap()) {
      out << b;
    }
    return out << "]";
  }
};

template<class A> PartitionIter<A> partitionIter(Stack<A> orig) { return PartitionIter<A>(std::move(orig)); }

template<class NumTraits>
ClauseIterator VariableElimination::applyRule(Clause* premise, FoundVariable<NumTraits> found) const
{
  TIME_TRACE("alasca vampire elimination")
  using Numeral = typename NumTraits::ConstantType;
  auto x = found.var;
  DEBUG("eliminating var: ", x)
  auto& I = found.posIneq;
  auto& J = found.negIneq;
  auto& L = found.neq;
  auto& K = found.eq;
  auto Ksize = K.size();

  auto Csize = premise->size() - Ksize - I.size() - J.size() - L.size();

  auto withoutX = [x](auto foundVarInLiteral) 
    { return foundVarInLiteral.literal.term().iterSummands()
                              .filter([&](auto monom) { return monom.factors != x; }); };


  Stack<Literal*> common(Csize + I.size() * J.size() + I.size() * L.size() + J.size() * L.size());

  { /* adding C */

    Stack<unsigned> nonCInd;
    auto addNonCInd = [&](auto& x) { for (auto idxd : x) { nonCInd.push(idxd.idx); } };
    addNonCInd(found.eq);
    addNonCInd(found.neq);
    addNonCInd(found.posIneq);
    addNonCInd(found.negIneq);
    std::sort(nonCInd.begin(), nonCInd.end());

    auto iter = nonCInd.iterFifo();
    auto skip = iter.hasNext() ? iter.next() : premise->size();
    for (unsigned i = 0; i < premise->size(); i++) {
      if (skip == i) {
        skip = iter.hasNext() ? iter.next() : premise->size();
      } else {
        ASS(skip > i)
        common.push((*premise)[i]);
      }
    }
  }

  auto b = [x](auto& i) {
    return iterTraits(i.literal.term().iterSummands())
      .filter([&](auto monom) { return monom.factors != x; })
      .map([&](auto t) { return (t / i.numeral.abs()); })
      .map([&](auto t) { return (i.literal.symbol() == AlascaPredicate::EQ || i.literal.symbol() == AlascaPredicate::NEQ) && i.numeral.isNegative()
                                ? -t : t; });
  };

  auto sum = [](auto l, auto r) {
    return NumTraits::sum(
      l.map([](auto monom){ return monom.denormalize(); }),
      r.map([](auto monom){ return monom.denormalize(); })); };

  auto minus = [](auto i) { return i.map([](auto monom) { return Numeral(-1) * monom; }); };

  { 
    // adding { bi + bj >ij 0 | i ∈ I, j ∈ J } 
    for (auto& i : I) {
      for (auto& j : J) {
        auto gr = i.literal.symbol() == AlascaPredicate::GREATER && j.literal.symbol() == AlascaPredicate::GREATER 
          ?  NumTraits::greater
          : NumTraits::geq;
        ASS(i.numeral.isPositive())
        ASS(j.numeral.isNegative())

        common.push(gr(true, sum(b(i), b(j)), NumTraits::zero()));
      }
    }
  }

  {
    // adding {  bi - bl  >i 0 |  i ∈ I,  l ∈ L }
    for (auto& i : I) {
      for (auto& l : L) {
        auto gr = i.literal.symbol() == AlascaPredicate::GREATER ? NumTraits::greater
                                                              : NumTraits::geq;
        common.push(gr(true, sum(b(i), minus(b(l))), NumTraits::zero()));
      }
    }
  }

  {
    // adding {  bj + bl  >j 0 |  j ∈ J,  l ∈ L }
    for (auto& j : J) {
      for (auto& l : L) {
        auto gr = j.literal.symbol() == AlascaPredicate::GREATER ? NumTraits::greater
                                                              : NumTraits::geq;
        common.push(gr(true, sum(b(j), b(l)), NumTraits::zero()));
      }
    }
  }

  { // adding { bl1 - bl2 /= 0 | ordered pairs (l1, l2) of L }
    // TODO write a test for me
    for (auto i1 : iterTraits(getRangeIterator(0u, (unsigned)L.size()))) {
      for (auto i2 : iterTraits(getRangeIterator(i1 + 1, (unsigned)L.size()))) {
        auto& l1 = L[i1];
        auto& l2 = L[i2];
        common.push(NumTraits::eq(false, sum(b(l1), minus(b(l2))), NumTraits::zero()));
      }
    }
  }


  return pvi(iterTraits(partitionIter(std::move(K)))
      .map([common = std::move(common), 
            I = std::move(I), 
            J = std::move(J), 
            L = std::move(L), 
            withoutX, 
            premise, 
            Ksize,
            sum, minus, b](auto& par) {

        auto Kp = [&]() { return par.partition(0);};
        auto Km = [&]() { return par.partition(1); };

        auto Kpsize = par.partitionSize(0);
        auto Kmsize = Ksize - Kpsize;

        Stack<Literal*> concl(common.size() + I.size() * Kpsize + + J.size() * Kmsize);
        concl.loadFromIterator(common.iterFifo());

        // adding {  bi - bk  >= 0 |   i ∈ I,   k ∈ Km }
        for (auto& k : Km()) {
          for (auto& i : I) {
            concl.push(NumTraits::geq(true, sum(b(i), minus(b(k))), NumTraits::zero()));
          }
        }

        // adding {  bj + bk  >= 0 |   j ∈ J,   k ∈ Kp }
        for (auto& k : Kp()) {
          for (auto& j : J) {
            concl.push(NumTraits::geq(true, sum(b(j), b(k)), NumTraits::zero()));
          }
        }

        // adding { bk1 - bk2 >= 0 |  k1 ∈ Kp, k2 ∈ Km }
        for (auto& k1 : Kp()) {
          for (auto& k2 : Km()) {
            // TODO test me
            concl.push(NumTraits::geq(true, sum(b(k1), minus(b(k2))), NumTraits::zero()));
          }
        }

        // adding {  bk - bl  >= 0 |  k ∈ Kp, l ∈ L }
        for (auto& k : Kp()) {
          for (auto& l : L) {
            // TODO test me
            concl.push(NumTraits::geq(true, sum(b(k), minus(b(l))), NumTraits::zero()));
          }
        }

        // adding {  bl - bk  >= 0 |  k ∈ Km, l ∈ L }
        for (auto& k : Km()) {
          for (auto& l : L) {
            // TODO test me
            concl.push(NumTraits::geq(true, sum(b(l), minus(b(k))), NumTraits::zero()));
          }
        }

        Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_VARIABLE_ELIMINATION, premise));
        auto out = Clause::fromStack(concl, inf);
        return out;
      }));
}

} // namespace ALASCA 
} // namespace Inferences 

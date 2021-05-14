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
#include "Kernel/TermIterators.hpp"

#define TODO ASSERTION_VIOLATION
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

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
  Map<Variable, AnyFoundVariable> unshielded;
  Set<Variable> shielded;
  for (unsigned i = 0; i < premise->size(); i++) {
    auto lit = (*premise)[i];
    auto norm = _shared->normalize(lit);
    if (norm.isSome()) {
      norm.unwrap().apply([&](auto& lit) -> void {
      //                            ^^^-->  t1 + ... + tn <> 0 
        using NumTraits = typename remove_reference<decltype(lit)>::type::NumTraits;
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
              case IrcPredicate:: EQ: found. eq.push(std::move(entry)); break;
              case IrcPredicate::NEQ: found.neq.push(std::move(entry)); break;
              case IrcPredicate::GREATER:
              case IrcPredicate::GREATER_EQ:
                      if (k.isPositive()) found.posIneq.push(std::move(entry));
                 else if (k.isNegative()) found.negIneq.push(std::move(entry));
                 else { ASSERTION_VIOLATION }
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
  for (auto v : vars) {
    if (!shielded.contains(v)) {
      return Option<AnyFoundVariable>(std::move(unshielded.get(v)));
    }
  }
  return Option<AnyFoundVariable>();
}

SimplifyingGeneratingInference::ClauseGenerationResult VariableElimination::generateSimplify(Clause* premise) 
{
  auto var = this->findUnshieldedVar(premise);
  if (var.isSome()) {
    return ClauseGenerationResult {
      .clauses          = std::move(var).unwrap().apply([&](auto var) { return eliminateVar(premise, std::move(var)); }),
      .premiseRedundant = true,
    };
  } else {
    return ClauseGenerationResult {
      .clauses          = ClauseIterator::getEmpty(),
      .premiseRedundant = false,
    };
  }
}

// C \/ { ci x + ti >i 0 | i ∈ I } \/ { -cj x + tj >j 0 | j ∈ J } \/ { ck x + tk == 0 | k ∈ K } \/ { ch x + th /= 0 | h ∈ H }
// ==========================================================================================================================
//
// C \/ { cj ti + ci tj >ij 0 | i ∈ I, j ∈ J } \/ { ch ti - ci th >i 0 | i ∈ I, h ∈ H } 
// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ \/ { ch tj + cj th >j 0 | j ∈ J, h ∈ H } 
//                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^--> Common
//                                             \/ { ck ti - ci tk >= 0 | i ∈ I, k ∈ K0 } 
//                                             \/ { ck tj + cj tk >= 0 | j ∈ J, k ∈ K1 } 
//
// for all partitions (K0, K1) of K

template<class A>
class PartitionIter {
  Stack<A> _orig;
  Option<vvector<bool>> _partition;
  bool _finished;
public:
  DECL_ELEMENT_TYPE(PartitionIter&);
  PartitionIter(Stack<A> orig) : _orig(std::move(orig)), _partition(), _finished(false) {}
  bool hasNext() { return !_finished; }
  PartitionIter& next() { 
    if (_partition.isNone()) {
      _partition = Option<vvector<bool>>(vvector<bool>(_orig.size(), false));
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
      .filterMap([this, lhs](auto i) { return _partition.unwrap()[i] == lhs ? Option<A&>(_orig[i]) : Option<A&>(); }); }

  auto partitionSize(bool lhs) 
  { return iterTraits(getRangeIterator((unsigned)0, (unsigned)_orig.size()))
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
ClauseIterator VariableElimination::eliminateVar(Clause* premise, FoundVariable<NumTraits> found) const
{

  auto x = found.var;
  DEBUG("eliminating var: ", x)
  auto& I = found.posIneq;
  auto& J = found.negIneq;
  auto& H = found.neq;
  auto& K = found.eq;
  auto Ksize = K.size();
  auto Csize = premise->size() - Ksize - I.size() - J.size() - H.size();

  auto withoutX = [x](auto foundVarInLiteral) 
    { return foundVarInLiteral.literal.term().iterSummands()
                              .filter([&](auto monom) { return monom.factors != x; }); };


  Stack<Literal*> common(Csize + I.size() * J.size() + I.size() * H.size() + J.size() * H.size());

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

  { 
    // adding { cj ti + ci tj >ij 0 | i ∈ I, j ∈ J }
    for (auto& i : I) {
      for (auto& j : J) {
        auto gr = i.literal.symbol() == IrcPredicate::GREATER && j.literal.symbol() == IrcPredicate::GREATER 
          ?  NumTraits::greater
          : NumTraits::geq;
        auto ci =  i.numeral;
        auto cj = -j.numeral;
        ASS(ci.isPositive())
        ASS(cj.isPositive())

        auto term = NumTraits::sum(
            withoutX(i).map([&](auto ti) { return (cj * ti).denormalize(); }),
            withoutX(j).map([&](auto tj) { return (ci * tj).denormalize(); })
        );
        common.push(gr(true, term, NumTraits::zero()));
      }
    }
  }

  {
    // adding { ch ti - ci th >i 0 | i ∈ I, h ∈ H } 
    for (auto& i : I) {
      for (auto& h : H) {
        auto gr = i.literal.symbol() == IrcPredicate::GREATER ? NumTraits::greater
                                                              : NumTraits::geq;
        auto ci = i.numeral;
        auto ch = h.numeral;
        auto sign = ch.isNegative() ? NumTraits::constant(-1) : NumTraits::constant(1);
        auto term = NumTraits::sum(
            withoutX(i).map([&](auto ti) { return ( sign * ch * ti).denormalize(); }),
            withoutX(h).map([&](auto th) { return (-sign * ci * th).denormalize(); })
        );
        common.push(gr(true,term, NumTraits::zero()));
      }
    }
  }

  {
    // adding { ch tj + cj th >j 0 | j ∈ J, h ∈ H } 
    for (auto& j : J) {
      for (auto& h : H) {
        auto gr = j.literal.symbol() == IrcPredicate::GREATER ? NumTraits::greater
                                                              : NumTraits::geq;
        auto cj = j.numeral;
        auto ch = h.numeral;
        auto sign = ch.isNegative() ? NumTraits::constant(-1) : NumTraits::constant(1);
        auto term = NumTraits::sum(
            withoutX(j).map([&](auto tj) { return ( sign * ch * tj).denormalize(); }),
            withoutX(h).map([&](auto th) { return ( sign * cj * th).denormalize(); })
        );
        common.push(gr(true,term, NumTraits::zero()));
      }
    }
  }


  return pvi(iterTraits(partitionIter(std::move(K)))
      .map([common = std::move(common), I = std::move(I), J = std::move(J), withoutX, premise, Ksize](auto& par) {
        // DBGE(par)

        auto K0 = par.partition(0);
        auto K1 = par.partition(1);

        auto K0size = par.partitionSize(0);
        auto K1size = Ksize - K0size;

        Stack<Literal*> concl(common.size() + I.size() * K0size + + J.size() * K1size);
        concl.loadFromIterator(common.iterFifo());

        // { ck ti + ci tk >= 0 | i ∈ I, k ∈ K0 } 
        for (auto& k : K0) {
          for (auto& i : I) {
            auto ci = i.numeral;
            auto ck = k.numeral;
            auto sign = ck.isNegative() ? NumTraits::constant(-1) : NumTraits::constant(1);
            auto term = NumTraits::sum(
                withoutX(i).map([&](auto ti) { return ( sign * ck * ti).denormalize(); }),
                withoutX(k).map([&](auto tk) { return (-sign * ci * tk).denormalize(); })
            );
            concl.push(NumTraits::geq(true, term, NumTraits::zero()));
          }
        }

        // { ck tj + cj tk >= 0 | j ∈ J, k ∈ K1 } 
        for (auto& k : K1) {
          for (auto& j : J) {
            auto cj = j.numeral;
            auto ck = k.numeral;
            auto sign = ck.isNegative() ? NumTraits::constant(-1) : NumTraits::constant(1);
            auto term = NumTraits::sum(
                withoutX(j).map([&](auto tj) { return ( sign * ck * tj).denormalize(); }),
                withoutX(k).map([&](auto tk) { return (-sign * cj * tk).denormalize(); })
            );
            concl.push(NumTraits::geq(true,term, NumTraits::zero()));
          }
        }


        Inference inf(GeneratingInference1(Kernel::InferenceRule::IRC_VARIABLE_ELIMINATION, premise));
        auto out = Clause::fromStack(concl, inf);
        return out;
      }));
}

} // namespace IRC 
} // namespace Inferences 

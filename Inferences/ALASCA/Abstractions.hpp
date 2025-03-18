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
 * @file VariableElimination.hpp
 * Defines class VariableElimination
 *
 */

#ifndef __Inferences_ALASCA_ABSTRACTION__
#define __Inferences_ALASCA_ABSTRACTION__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/EqHelper.hpp"
#include <type_traits>


namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class NumTraits>
class Abstraction
: public ImmediateSimplificationEngine
{
  using ASig = AlascaSignature<NumTraits>;
  std::shared_ptr<AlascaState> _shared;

  struct Path {

    struct ClauseEntry {
      Clause* current;
      unsigned idx;

      Literal* deref() const { return (*current)[idx]; }
      Option<TermList> derefTermList() const { return {}; }
      bool isShielded() const { return false; }
      bool inBounds() const { return idx < current->size(); }
      bool isUnderFloorOrSum() const { return false; }
      bool canPush() const { return deref()->numTermArguments() > 0; }
    };

    struct LiteralEntry {
      Literal* current;
      unsigned idx;
      bool shielded;

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool isShielded() const { return shielded; }
      bool inBounds() const { return idx < current->numTermArguments(); }
      bool isUnderFloorOrSum() const { return false; }
      bool canPush() const { return deref().isTerm() && deref().term()->numTermArguments() > 0; }
    };

    struct TermEntry {
      Term* current;
      unsigned idx;
      bool shielded;
      bool underFloorOrSum;

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool inBounds() const { return idx < current->numTermArguments(); }
      bool isShielded() const { return shielded; }
      bool isUnderFloorOrSum() const { return underFloorOrSum; }
      bool canPush() const { return deref().isTerm() && deref().term()->numTermArguments() > 0; }
    };

    template<class F>
    auto iterElems(F f) const
    { return concatIters(
          iterItems(f(clause)),
          litIdx.map([&](auto& x){ return f(x); }).intoIter(),
          arrayIter(*termIdx).map([&](auto& x){ return f(x); })
        ); }

    friend std::ostream& operator<<(std::ostream& out, Path const& self)
    { return out << *self.clause.current << "[" << Output::interleaved(".", self.iterElems([](auto& e) { return e.idx; })) << "]"
      << " -> " << self.top([](auto& t) { return t.derefTermList(); }); }

    ClauseEntry clause;
    Option<LiteralEntry> litIdx;
    RStack<TermEntry> termIdx;

    Path(ClauseEntry cl, decltype(litIdx) li, decltype(termIdx) ti) : clause(std::move(cl)), litIdx(std::move(li)), termIdx(std::move(ti)) {}
    Path(ClauseEntry cl) : clause(std::move(cl)) {}
    Path(Clause* cl, unsigned idx) : clause(ClauseEntry { .current = cl, .idx = idx }) { ASS(clause.inBounds()) }

    auto depth() const 
    { return 1 + termIdx.size() + unsigned(litIdx.isSome()); }

    template<class F>
    auto get(unsigned i, F f) const {
      return i == 0 ? f(clause) 
           : i == 1 ? f(*litIdx)
           : f(termIdx[i - 2]);
    }

    template<class F>
    auto get(unsigned i, F f) {
      return i == 0 ? f(clause) 
           : i == 1 ? f(*litIdx)
           : f(termIdx[i - 2]);
    }

    template<class F> auto top(unsigned i, F f) const { return get(depth() - 1 - i, std::move(f)); }
    template<class F> auto top(            F f) const { return top(0, std::move(f)); }

    template<class F> auto top(unsigned i, F f) { return get(depth() - 1 - i, std::move(f)); }
    template<class F> auto top(            F f) { return top(0, std::move(f)); }

    bool nextStep(unsigned baseDepth) {
      if (top([](auto t){ return t.canPush(); })) {
        push(0);
        return true;
      } else {
        top([](auto& x) { x.idx++; });
        while(depth() > 1 && depth() >= baseDepth && !top([&](auto t) { return t.inBounds(); })) {
          pop();
          top([](auto& x) { x.idx++; });
        }
        if (depth() < baseDepth || depth() == 1) {
          return false;
        } else {
          return true;
        }
      }
    }
 
    Path clone() const
    { return Path (
        clause,
        litIdx,
        termIdx.clone([](auto& s, auto& t) { s = t; })
      );
    };

    Option<TermList> currentTerm() const { return top([](auto t) { return t.derefTermList(); }); }

    void popToUninterpreted() {
      while ( top([](auto& t) { return t.isUnderFloorOrSum(); })) {
        pop();
      }
    }

    Clause* abstract() const {
      auto newVar = TermList::var(1 + clause.current->iterLits()
        .flatMap([&](auto x) { return VariableIterator(x); })
        .map([&](auto t) { return t.var(); })
        .max().unwrapOr(0));
      return Clause::fromIterator(
          concatIters(
            iterItems(ASig::eq(false, newVar, currentTerm().unwrap())),
            range(0, clause.current->size())
             .map([&](auto i) -> Literal* {
               if (i != clause.idx) {
                 return (*clause.current)[i];
               } else {
                 return abstractLiteral(newVar);
               }
             })
           ),
           // TODO two different abstraction InferenceRules
           Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_ABSTRACTION, clause.current)));
    }

    TermList abstractTerm(unsigned depth, TermList newVar) const {
      // TODO de-recursif
      if (depth == termIdx.size()) {
        return newVar;
      } else {
        auto t = termIdx[depth].current;
        auto idx = termIdx[depth].idx;
        return TermList(Term::createFromIter(t->functor(), 
            concatIters(
              typeArgIter(t),
              range(0, t->numTermArguments())
                .map([&](auto i) {
                  return i != idx ? t->termArg(i)
                       : abstractTerm(depth + 1, newVar);
                  })
              )
              ));
      }
    }

    Literal* abstractLiteral(TermList newVar) const {
      auto l = litIdx->current;
      auto idx = litIdx->idx;
      return Literal::createFromIter(l, 
          concatIters(
            typeArgIter(l),
            range(0, l->numTermArguments())
              .map([&](auto i) {
                return i != idx ? l->termArg(i)
                     : abstractTerm(0, newVar);
                })
            ));
    }

    
    void push(unsigned i) { 
      if (auto cur = currentTerm()) {
        auto curT = cur->term();
        termIdx->push(TermEntry { 
            .current = curT, 
            .idx = i, 
            .shielded = top([](auto& t) { return t.isShielded(); }) || ASig::isUninterpreted(curT),
            .underFloorOrSum = ASig::isFloor(curT) 
            || ASig::isAdd(curT) 
            || (ASig::isLinMul(curT) &&  top([](auto& t) { return t.isUnderFloorOrSum(); })),
        });
      } else {
        ASS(litIdx.isNone())
        litIdx = some(LiteralEntry { .current = clause.deref(), .idx = i, .shielded = !ASig::isAlascaLiteral(clause.deref())});
      }
    }

    void pop() { 
      if (termIdx.size() > 0) {
        termIdx->pop();
      } else {
        litIdx.take().unwrap();
      }
    }
  };

public:

  Abstraction(Abstraction&&) = default;

  explicit Abstraction(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared))
  {  }

  // TODO theory make sure that variables can be shielded or unshielded or not top-level containted

  bool simplify(Clause* premise, Path& path, Set<TermList>& topLevelVars) {
    auto baseDepth = path.depth();
    while (path.nextStep(baseDepth)) {
      if (path.currentTerm().unwrap().isVar() 
          && path.top([](auto& t) { return t.isUnderFloorOrSum() && t.isShielded(); })
          ) {
        path.popToUninterpreted();
        return true;
      }
    }
    return false;
  }

  void collectTopLevelVars(Path& path, TermList t, Set<TermList>& topLevelVars, RStack<Path>& todoT) {
    if (t.isVar()) {
      topLevelVars.insert(t);
    } else {
      auto term = t.term();
          ASig::ifAdd(term, [&](auto t0, auto t1) {
              path.push(0);
              collectTopLevelVars(path, t0,topLevelVars, todoT);
              path.top([](auto& x) { x.idx = 1; });
              collectTopLevelVars(path, t1,topLevelVars, todoT);
              path.pop();
              return 0;
          })
      .orElse([&](){ return 
          ASig::ifLinMulWithPath(term, path, [&](auto k, auto t) { 
              collectTopLevelVars(path, t, topLevelVars, todoT); 
              return 0;
          }); })
      .orElse([&](){ return 
          ASig::ifFloor(term, [&](auto t) { 
              path.push(0);
              collectTopLevelVars(path, t, topLevelVars, todoT); 
              path.pop();
              return 0;
          }); })
      .orElse([&]() { 
          todoT->push(path.clone());
          return 0;
      });
    }
  }

  // virtual Clause* simplify(Clause* premise) final override {
  //   if (premise->size() == 0) {
  //     // TODO why do we ever get the empty clause here?
  //     return premise;
  //   }
  //   Set<TermList> topLevelVars;
  //   auto todo = RStack<Path>();
  //   auto path = Path(premise, 0);
  //   for (auto lit : premise->iterLits()) {
  //     ASig::ifAlascaLiteralWithPath(lit, [&](auto p, auto t, unsigned i) { 
  //         path.push(i);
  //         collectTopLevelVars(path, t, topLevelVars, todo);
  //         path.pop();
  //         return 0;
  //     })
  //     .orElse([&]() { todo->push(path.clone()); return 0; });
  //     path.top([](auto& t) { t.idx++; });
  //   }
  //   for (auto& path : *todo) {
  //     if (simplify(premise, path, topLevelVars)) {
  //       return path.abstract();
  //     }
  //   }
  //   return premise;
  // }

  template<class N, class F1, class F2>
  std::invoke_result_t<F1, TermList> iterUninterpretedOrVarSummands(
      AlascaTermItp<N> term, 
      F1 var,
      F2 nonVar
      ) 
  {
    for (AlascaMonom<N> s : term.iterSummands()) {
      std::invoke_result_t<F1, TermList> result;
      if (s.atom().isVar()) {
        result = var(s.atom());
      } else if (N::isFloor(s.atom().term()->functor())) {
        auto normArg = AnyAlascaTerm::normalize(TypedTermList(s.atom().term()->termArg(0), N::sort()))
            .template asSum<N>().unwrap();
        result = iterUninterpretedOrVarSummands(normArg, var, nonVar);
      } else {
        result = nonVar(s.atom().term());
      }
      if (result) {
        return result;
      }
    }
    return {};
  }

  Clause* applyAbstraction(Clause* clause, TypedTermList toAbstract) {

    auto maxVar = clause->iterLits()
          .flatMap([&](auto x) { return VariableIterator(x); })
          .map([&](auto t) { return t.var(); })
          .max()
          .unwrap();
    auto newVar = TermList::var(1 + maxVar);

    return Clause::fromIterator(
      concatIters(
        iterItems(Literal::createEquality(false, newVar, toAbstract, toAbstract.sort())),
        clause->iterLits()
         .map([&](auto l) -> Literal* {
           return EqHelper::replace(l, toAbstract, newVar);
         })
       ),
       Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_ABSTRACTION, clause)));
  }

  Option<Clause*> trySimplifiy(Clause* premise, Term* termOrLit)  {
    for (auto a : termArgIterTyped(termOrLit)) {
      auto normA = AnyAlascaTerm::normalize(a);
      for (auto subterm : normA.topDownIter()) {
        if (auto itp = subterm.asSum()) {
          auto result = itp->apply([&](auto itp) -> Option<Clause*> {

              if (itp.nSummands() == 1 && itp[0].atom().isVar()) {
                return {};
              }

              auto unshieldedVar = iterUninterpretedOrVarSummands(itp, 
                  [&](TermList var) { return true; }, 
                  [&](Term*       ) { return false; });

              if (unshieldedVar) {
                return some(applyAbstraction(premise, subterm.toTerm()));
              } else {
                return {};
              }
          });
          if (result) {
            return result;
          }
        }
      }
    }
    return {};
  }

  virtual Clause* simplify(Clause* premise) final override {
    if (premise->size() == 0) {
      // TODO why do we ever get the empty clause here?
      return premise;
    }
    // TODO get rid of this set
    Recycled<Set<TermList>> topLevelVars;
    auto todo = RStack<Term*>();
    for (auto lit : premise->iterLits()) {
      auto norm = InequalityNormalizer::normalize(lit);
      Option<Clause*> result;
      if (auto itp = norm.asItp()) {
        result = itp->apply([&](auto itp) {
            return iterUninterpretedOrVarSummands(itp.term(), 
                [&](TermList v) { return Option<Clause*>{}; },
                [&](Term*    t) { return trySimplifiy(premise, t); });
        });
      } else {
        result = trySimplifiy(premise, lit);
      }
      if (result) {
        return *result;
      }
    }
    return premise;
  }

};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_ABSTRACTION__*/

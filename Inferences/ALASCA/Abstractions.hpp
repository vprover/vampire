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

#define UNSTABILITY_ABSTRACTION 0

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
// TODO use this abstraction rule also in normal alasca not only in the integer case

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
      bool isUnderFloor() const { return false; }
      bool isShielded() const { return false; }
      bool inBounds() const { return idx < current->size(); }
      // bool canPush() const { return true; }
      bool canPush() const { return deref()->numTermArguments() > 0; }
#if UNSTABILITY_ABSTRACTION
      bool isUnstable() const { return false; }
#endif // UNSTABILITY_ABSTRACTION
    };

    struct LiteralEntry {
      Literal* current;
      unsigned idx;
      bool shielded;

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool isUnderFloor() const { return false; }
      bool isShielded() const { return shielded; }
#if UNSTABILITY_ABSTRACTION
      bool isUnstable() const { return false; }
#endif // UNSTABILITY_ABSTRACTION
      bool inBounds() const { return idx < current->numTermArguments(); }
      // bool canPush() const { return current->numTermArguments() > 0; }
      bool canPush() const { return deref().isTerm() && deref().term()->numTermArguments() > 0; }
    };

    struct TermEntry {
      Term* current;
      unsigned idx;
      bool underFloor;
      bool shielded;
#if UNSTABILITY_ABSTRACTION
      bool unstable;
#endif // UNSTABILITY_ABSTRACTION

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool isUnderFloor() const { return underFloor; }
      bool inBounds() const { return idx < current->numTermArguments(); }
#if UNSTABILITY_ABSTRACTION
      bool isUnstable() const { return unstable; }
#endif // UNSTABILITY_ABSTRACTION
      bool isShielded() const { return shielded; }
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

// private:
//     unsigned arity(TermList t) const { return t.isTerm() ? t.term()->numTermArguments() : 0; }
//     unsigned arity(Literal* l) const { return l->numTermArguments(); }
// public:
//     unsigned currentArity() const { return derefCurrent([&](auto t) { return arity(t); }); }

    Option<TermList> currentTerm() const { return top([](auto t) { return t.derefTermList(); }); }

    void popToFloor() {
      while (!(ASig::isFloor(currentTerm().unwrap()) &&  top([](auto x) { return !x.isUnderFloor(); }))) {
        pop();
      }
    }

    bool isUnshieldedUnderFloor() const 
    { return top([&](auto& t) { return t.isUnderFloor(); }); }

#if UNSTABILITY_ABSTRACTION
    void popToUnstable() { 
      // ASSERTION_VIOLATION
      // ASS(top([](auto x) { return x.derefIsUnstable(); }))
      while (top([](auto x) { return x.isUnstable(); })) {
        pop();
      }
    }
    bool isUnstable() const { return top([](auto x) { return x.isUnstable(); }); }
#endif // UNSTABILITY_ABSTRACTION

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
        auto unshieldedUnderFloor = 
            ASig::isFloor(curT)                             ? true
          : (ASig::isLinMul(curT) || ASig::isAdd(curT)) ? top([](auto& x) { return x.isUnderFloor(); })
           /* uninterpretd */                                   : false;
        termIdx->push(TermEntry { 
            .current = curT, 
            .idx = i, 
            .underFloor = unshieldedUnderFloor, 
            .shielded = top([](auto& t) { return t.isShielded(); }) || ASig::isUninterpreted(curT),
#if UNSTABILITY_ABSTRACTION
            .unstable = top([](auto& t) { return t.isUnstable(); })  
                    || (top([](auto& t) { return t.isShielded(); }) && ASig::isAdd(curT)),
#endif // UNSTABILITY_ABSTRACTION
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

  // TODO theory make sure that variables can be shielded or unshielded or not top-level contained

  bool simplify(Clause* premise, Path& path, Set<TermList>& topLevelVars) {
    auto baseDepth = path.depth();
    while (path.nextStep(baseDepth)) {
#if UNSTABILITY_ABSTRACTION
      if (topLevelVars.contains(path.currentTerm().unwrap()) && path.isUnstable()) {
        // unstably shielded var
        path.popToUnstable();
        return true;
      }
#endif // UNSTABILITY_ABSTRACTION
      if (path.isUnshieldedUnderFloor() && path.currentTerm().unwrap().isVar()) {
        path.popToFloor();
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

  Clause* simplify(Clause* premise) final {
    if (premise->size() == 0) {
      // TODO why do we ever get the empty clause here?
      return premise;
    }
    Set<TermList> topLevelVars;
    auto todo = RStack<Path>();
    auto path = Path(premise, 0);
    for (auto lit : premise->iterLits()) {
      ASig::ifAlascaLiteralWithPath(lit, [&](auto p, auto t, unsigned i) { 
          path.push(i);
          collectTopLevelVars(path, t, topLevelVars, todo);
          path.pop();
          return 0;
      })
      .orElse([&]() { todo->push(path.clone()); return 0; });
      path.top([](auto& t) { t.idx++; });
    }
    for (auto& path : *todo) {
      if (simplify(premise, path, topLevelVars)) {
        return path.abstract();
      }
    }
    return premise;
  }
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_ABSTRACTION__*/

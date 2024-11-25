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

#ifndef __Inferences_LASCA_ABSTRACTION__
#define __Inferences_LASCA_ABSTRACTION__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Lib/Exception.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
// TODO use this abstraction rule also in normal lasca not only in the integer case

// TODO move somewhere else and use
template<class NumTraits, class F>
Option<std::invoke_result_t<F, LascaPredicate, TermList, unsigned>> ifLascaLiteral(Literal* lit, F f) {
  // TODO assert normalized
  if (NumTraits::isGreater(lit->functor())) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(LascaPredicate::GREATER   , lit->termArg(0), 0));
  }
  if (NumTraits::isGeq(lit->functor())    ) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(LascaPredicate::GREATER_EQ, lit->termArg(0), 0));
  }
  if (lit->isEquality() && SortHelper::getEqualityArgumentSort(lit) == NumTraits::sort()) {
    auto i = 0;
    if (auto n = NumTraits::tryNumeral(lit->termArg(0))) {
      if (*n == 0) {
        i++;
      }
    }
    return some(f(lit->isPositive() ? LascaPredicate::EQ : LascaPredicate::NEQ, lit->termArg(i), i));
  }
  return {};
}

// TODO move somewhere else and use
template<class NumTraits, class T, class F>
auto ifNumMul(T term, F f) {
  return NumTraits::ifMul(term, [&](auto l, auto r) {
      ASS(!NumTraits::isNumeral(r))
      return NumTraits::ifNumeral(l, [&](auto l) { return f(l, r, 1); });
  }).flatten()
  .orElse([&](){
      return NumTraits::ifMinus(term, [&](auto t) { return  f(NumTraits::constant(-1), t, 0); });
      });
}

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isNumMul(T term) 
{ return ifNumMul<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isLascaLiteral(T term) 
{ return ifLascaLiteral<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isUninterpreted(T t) 
{ return !NumTraits::isFloor(t) && !NumTraits::isAdd(t) && !isNumMul<NumTraits>(t); }

template<class NumTraits>
class Abstraction
: public ImmediateSimplificationEngine
{
  std::shared_ptr<LascaState> _shared;

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
      bool isUnstable() const { return false; }
    };

    struct LiteralEntry {
      Literal* current;
      unsigned idx;
      bool shielded;

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool isUnderFloor() const { return false; }
      bool isShielded() const { return shielded; }
      bool isUnstable() const { return false; }
      bool inBounds() const { return idx < current->numTermArguments(); }
      // bool canPush() const { return current->numTermArguments() > 0; }
      bool canPush() const { return deref().isTerm() && deref().term()->numTermArguments() > 0; }
    };

    struct TermEntry {
      Term* current;
      unsigned idx;
      bool underFloor;
      bool shielded;
      bool unstable;

      TermList deref() const { return current->termArg(idx); }
      Option<TermList> derefTermList() const { return some(deref()); }
      bool isUnderFloor() const { return underFloor; }
      bool inBounds() const { return idx < current->numTermArguments(); }
      bool isUnstable() const { return unstable; }
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
    { return out << *self.clause.current << "[" << outputInterleaved(".", self.iterElems([](auto& e) { return e.idx; })) << "]"
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
      while (!(NumTraits::isFloor(currentTerm().unwrap()) &&  top([](auto x) { return !x.isUnderFloor(); }))) {
        pop();
      }
    }

    bool isUnshieldedUnderFloor() const 
    { return top([&](auto& t) { return t.isUnderFloor(); }); }

    // TODO
    void popToUnstable() { 
      // ASSERTION_VIOLATION
      // ASS(top([](auto x) { return x.derefIsUnstable(); }))
      while (top([](auto x) { return x.isUnstable(); })) {
        pop();
      }
    }
    // TODO
    bool isUnstable() const { return top([](auto x) { return x.isUnstable(); }); }

    Clause* abstract() const {
      auto newVar = TermList::var(1 + clause.current->iterLits()
        .flatMap([&](auto x) { return VariableIterator(x); })
        .map([&](auto t) { return t.var(); })
        .max().unwrapOr(0));
      return Clause::fromIterator(
          concatIters(
            iterItems(NumTraits::eq(false, newVar, currentTerm().unwrap())),
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
           Inference(SimplifyingInference1(Kernel::InferenceRule::LASCA_ABSTRACTION, clause.current)));
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
            NumTraits::isFloor(curT)                             ? true
          : (isNumMul<NumTraits>(curT) || NumTraits::isAdd(curT)) ? top([](auto& x) { return x.isUnderFloor(); })
           /* uninterpretd */                                   : false;
        auto shielded = top([](auto& t) { return t.isShielded(); }) || isUninterpreted<NumTraits>(curT);
        auto unstable = top([](auto& t) { return t.isUnstable(); })  
          || (top([](auto& t) { return t.isShielded(); }) && NumTraits::isAdd(curT));
        termIdx->push(TermEntry { 
            .current = curT, 
            .idx = i, 
            .underFloor = unshieldedUnderFloor, 
            .shielded = shielded,
            .unstable = unstable,
        });
      } else {
        ASS(litIdx.isNone())
        litIdx = some(LiteralEntry { .current = clause.deref(), .idx = i, .shielded = !isLascaLiteral<NumTraits>(clause.deref())});
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

  explicit Abstraction(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
  {  }

  // TODO theory make sure that variables can be shielded or unshielded or not top-level containted

  bool simplify(Clause* premise, Path& path, Set<TermList>& topLevelVars) {
    auto baseDepth = path.depth();
    while (path.nextStep(baseDepth)) {
      if (topLevelVars.contains(path.currentTerm().unwrap()) && path.isUnstable()) {
        // unstably shielded var
        path.popToUnstable();
        return true;
      }
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
          NumTraits::ifAdd(term, [&](auto t0, auto t1) {
              path.push(0);
              collectTopLevelVars(path, t0,topLevelVars, todoT);
              path.top([](auto& x) { x.idx = 1; });
              collectTopLevelVars(path, t1,topLevelVars, todoT);
              path.pop();
              return 0;
          })
      .orElse([&](){ return 
          ifNumMul<NumTraits>(term, [&](auto k, auto t, auto i) { 
              path.push(i);
              collectTopLevelVars(path, t, topLevelVars, todoT); 
              path.pop();
              return 0;
          }); })
      .orElse([&](){ return 
          NumTraits::ifFloor(term, [&](auto t) { 
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

  virtual Clause* simplify(Clause* premise) final override {
    if (premise->size() == 0) {
      // TODO why do we ever get the empty clause here?
      return premise;
    }
    Set<TermList> topLevelVars;
    auto todo = RStack<Path>();
    auto path = Path(premise, 0);
    for (auto lit : premise->iterLits()) {
      ifLascaLiteral<NumTraits>(lit, [&](auto p, auto t, unsigned i) { 
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

} // namespace LASCA 
} // namespace Inferences 

#endif /*__Inferences_LASCA_ABSTRACTION__*/

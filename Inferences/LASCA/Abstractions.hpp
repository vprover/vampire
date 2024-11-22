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

template<class NumTraits>
class Abstraction
: public ImmediateSimplificationEngine
{
  std::shared_ptr<LascaState> _shared;
  struct Path {
    Path(Clause* cl, unsigned clIdx, Option<std::tuple<Literal*, unsigned>> litIdx, RStack<std::tuple<Term*, unsigned, /* unshieldedUnderFloor */ bool>> termIdx) : cl(cl), clIdx(clIdx), litIdx(std::move(litIdx)), termIdx(std::move(termIdx)) {}
    Path(Clause* cl, unsigned clIdx) : cl(cl), clIdx(clIdx) {}
    Clause* cl;
    unsigned clIdx;
    Option<std::tuple<Literal*, unsigned>> litIdx;
    RStack<std::tuple<Term*, unsigned, /* unshieldedUnderFloor */ bool>> termIdx;

    unsigned depth() const { return litIdx.isNone() ? 0 : 1 + termIdx->size(); }

    bool nextStep(unsigned baseDepth) {
      auto topInBounds = [&]() { 
        if (depth() == 1) return std::get<0>(*litIdx)->numTermArguments() > std::get<1>(*litIdx);
        else              return std::get<0>(termIdx->top())->numTermArguments() > std::get<1>(termIdx->top());
      };
      if (currentTerm().isTerm() && currentTerm().term()->numTermArguments() > 0) {
        push(0);
        return true;
      } else {
        top()++;
        while(depth() >= baseDepth && !topInBounds()) {
          pop();
          top()++;
        }
        if (depth() < baseDepth) {
          return false;
        } else {
          return true;
        }
      }
    }
 
    Path clone() const
    { return Path (
        cl,
        clIdx,
        litIdx,
        termIdx.clone([](auto& s, auto& t) { s = t; })
      );
    };


    TermList currentTerm() const {
      ASS(litIdx.isSome())
        // for (auto pair : *termIdx) {
        //   DBG(*std::get<0>(pair), " @ ", std::get<1>(pair))
        // }
        //   DBG("")
      auto deref = [](auto& pair) { return std::get<0>(pair)->termArg(std::get<1>(pair)); };
      return termIdx.size() > 0 ? deref(termIdx->top())
                                : deref(*litIdx);
    }

    void popToFloor() {
      while (!NumTraits::isFloor(currentTerm())) {
        pop();
      }
    }
    bool isUnshieldedUnderFloor() const 
    { return std::get<2>(termIdx->top()); }

    // TODO
    void popToUnstable() { ASSERTION_VIOLATION  }
    // TODO
    bool isUnstable() const { return false; }

    Clause* abstract(TermList newVar) const {
      return Clause::fromIterator(
          range(0, cl->size())
           .map([&](auto i) -> Literal* {
             if (i != clIdx) {
               return (*cl)[i];
             } else {
               return abstractLiteral(newVar);
             }
           }),
           // TODO two different abstraction InferenceRules
           Inference(SimplifyingInference1(Kernel::InferenceRule::LASCA_ABSTRACTION, cl)));
    }

    TermList abstractTerm(unsigned depth, TermList newVar) const {
      if (depth == termIdx.size()) {
        return newVar;
      } else {
        auto t = std::get<0>(termIdx[depth]);
        auto idx = std::get<1>(termIdx[depth]);
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
      auto l = std::get<0>(*litIdx);
      auto idx = std::get<1>(*litIdx);
      return Literal::createFromIter(l, 
          concatIters(
            typeArgIter(l),
            range(0, l->numTermArguments())
              .map([&](auto i) {
                return i != idx ? l->termArg(i)
                     : abstractTerm(0, newVar);
                })
            )
            );
    }

    void push(unsigned i) { 
      if (termIdx.size() > 0) {
        auto cur = currentTerm();
        auto unshieldedUnderFloor = 
            NumTraits::isFloor(cur)                             ? true
          : (isNumMul<NumTraits>(cur) || NumTraits::isAdd(cur)) ? std::get<2>(termIdx->top())
           /* uninterpretd */                                   : false;
        termIdx->push(std::make_tuple(std::get<0>(termIdx->top())->termArg(std::get<1>(termIdx->top())).term(), i, unshieldedUnderFloor));
      } else if (litIdx.isSome()) {
        termIdx->push(std::make_tuple(std::get<0>(*litIdx)->termArg(std::get<1>(*litIdx)).term(), i, /* unshieldedUnderFloor */ false));
      } else {
        litIdx = some(std::make_tuple((*cl)[clIdx], i));
      }
    }

    unsigned& top() { 
      if (termIdx.size() > 0) {
        return std::get<1>(termIdx->top());
      } else if (litIdx.isSome()) {
        return std::get<1>(*litIdx);
      } else {
        return clIdx;
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
      if (topLevelVars.contains(path.currentTerm()) && path.isUnstable()) {
        // unstably shielded var
        path.popToUnstable();
        return true;
      }
      if (path.isUnshieldedUnderFloor() && path.currentTerm().isVar()) {
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
              path.top() = 1;
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
    Set<TermList> topLevelVars;
    unsigned maxVar = -1; // TODO use a different var number ???
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
      path.top()++;
    }
    for (auto& path : *todo) {
      if (simplify(premise, path, topLevelVars)) {
        return path.abstract(TermList::var(maxVar + 1));
      }
    }
    return premise;
  }
};

} // namespace LASCA 
} // namespace Inferences 

#endif /*__Inferences_LASCA_ABSTRACTION__*/

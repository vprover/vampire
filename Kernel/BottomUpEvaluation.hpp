/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LIB__BOTTOM_UP_EVALUATION_HPP__
#define __LIB__BOTTOM_UP_EVALUATION_HPP__

#define DEBUG(...) // DBG(__VA_ARGS__)

/**
 * @file Kernel/BottomUpEvaluation.hpp
 *
 * This file contains mainly the function Lib::evaluateBottomUp, that can be used to evaluate an arbitrary 
 * acyclic graph structure bottom up. It uses iteration instead of recursion and can be equipped with memoization structures 
 * found in Lib::Memo.
 *
 * \see UnitTests/tBottomUpEvaluation.cpp
 * \see Lib::evaluateBottomUp
 */ 

#include "Lib/Stack.hpp"
#include "Lib/Option.hpp"
#include "Lib/TypeList.hpp"

namespace Lib {

namespace Memo {

  /** a mocked memoization that does not store any results */
  template<class Arg, class Result>
  struct None 
  {
    Option<Result> get(Arg) 
    { return Option<Result>(); }

    template<class Init> Result getOrInit(Arg const& orig, Init init) 
    { return init(); }
  };

  /** a memoization realized as a hashmap */
  template<class Arg, class Result>
  class Hashed 
  {
    Map<Arg, Result> _memo;

  public:
    Hashed() : _memo(decltype(_memo)()) {}

    template<class Init> Result getOrInit(Arg const& orig, Init init) 
    { return _memo.getOrInit(Arg(orig), init); }

    Option<Result> get(const Arg& orig) 
    { 
      auto out = _memo.getPtr(orig);
      if (out) {
        return Option<Result>(*out);
      } else {
        return Option<Result>();
      }
    }
  };

} // namespace Memo

/** 
 * An iterator over the children of a node in a Directed Acyclic Graph (DAG). 
 * The DAG is a structure to be evaluate bottom up using evaluateBottomUp. 
 * A template-specialization of this struct with the methods like in this template 
 * must be implemented for a class in order to bottom-up evaluatable.
 */
template<class A> 
struct BottomUpChildIter
{
  /** constructs an iterator over the children of the current node */
  BottomUpChildIter(A a);

  /** returns the node this iterator was constructed with */
  A self();

  /** returns the next child of the node this this object was constructed with */
  A next();

  /** returns the next child of the current node in the structure to be traversed */
  bool hasNext();

  /** returns how many children this node has */
  unsigned nChildren();
};

template<class A> BottomUpChildIter<A> bottomUpChildIter(A a) 
{ return BottomUpChildIter<A>(a); }

/** 
 * Evaluates a term-like datastructure (i.e.: a Directed Acyclic Graph (DAG)), without using recursion.
 *
 * Optionly a memoization method (i.e. a class from Kernel::Memo) can be specified. The memo can be a static,
 * variable, in order to keep cached results for multiple runs of the funcion. 
 *
 * The term-ish structure is evaluated according to the structure EvalFn. It is expected to have the following structure:
 * class EvalFn {
 *    using Arg    = ...; // <- the term-ish structure that will be evaluated. 
 *                        //    A specialization template<> BottomUpChildIter<Arg> must exist
 *    using Result = ...; // <- the type the structure will be evaluated to
 *
 *    // The actual evaluation function. It will be called once for each node in the directed acyclic graph, together with 
 *    // the already recursively evaluated children.
 *    Result operator()(Arg const& orig, Result* evaluatedChildren); 
 * }
 * 
 * The term to be evaluated will be traversed using a BottomUpChildIter<Arg>. 
 */
template<class EvalFn, class Memo>
typename EvalFn::Result evaluateBottomUp(typename EvalFn::Arg const& term, EvalFn evaluateStep, Memo& memo) 
{
  CALL("evaluateBottomUp(...)")
  using Result = typename EvalFn::Result;
  using Arg    = typename EvalFn::Arg;

  static_assert(std::is_same<ResultOf<EvalFn, Arg, Result*>, Result>::value, "evaluation function must have signature `Result eval(Arg term, Result* evaluatedArgs)`");

  
  /* recursion state. Contains a stack of items that are being recursed on. */
  Stack<BottomUpChildIter<Arg>> recState;
  Stack<Result> recResults;

  recState.push(BottomUpChildIter<Arg>(term));

  while (!recState.isEmpty()) {

    if (recState.top().hasNext()) {
      Arg t = recState.top().next();

      Option<Result> cached = memo.get(t);
      if (cached.isSome()) {
        recResults.push(std::move(cached).unwrap()); 
      } else {
        recState.push(BottomUpChildIter<Arg>(t));
      }

    } else { 

      BottomUpChildIter<Arg> orig = recState.pop();
      Result eval = memo.getOrInit(orig.self(), [&](){ 
            CALL("evaluateBottomUp(..)::closure@1")
            Result* argLst = NULL;
            if (orig.nChildren() != 0) {
              ASS_GE(recResults.size(), orig.nChildren());
              argLst = static_cast<Result*>(&recResults[recResults.size() - orig.nChildren()]);
            }
            return evaluateStep(orig.self(), argLst);
          });

      DEBUG("evaluated: ", orig.self(), " -> ", eval);

      recResults.pop(orig.nChildren());
      recResults.push(std::move(eval));
    }
  }
  ASS(recState.isEmpty())
    

  ASS(recResults.size() == 1);
  auto result = recResults.pop();
  DEBUG("eval result: ", term, " -> ", result);
  return result;
}

/** convenience wrapper for using evaluateBottomUp without a memo. */
template<class EvalFn>
typename EvalFn::Result evaluateBottomUp(typename EvalFn::Arg const& term, EvalFn evaluateStep) 
{
  using namespace Memo;
  auto memo = None<typename EvalFn::Arg, typename EvalFn::Result>();
  return evaluateBottomUp(term, evaluateStep, memo);
}



} // namespace Lib

#undef DEBUG
#endif // __LIB__BOTTOM_UP_EVALUATION_HPP__


/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Option.hpp"

namespace Lib {

/** struct that takes a closure and runs it when it is dropped (deleted without being moved) 
 * This is for example useful for debugging when/if some iterator or closure is being dropped.
 * For an iterator you can for example do
 * ```
 *   iterTraits(iter)
 *     .store(RunOnDrop([]() { DBG("iterator is being dropped"); }))
 * ```
 * or for a closure you can do
 * ```
 * auto fun = [dropGuard = RunOnDrop([]() { DBG("closure is being dropped"); })](auto arg) {
 *   // closure body
 * };
 * ```
 * */
template<class F>
struct RunOnDrop {
  Option<F> fun;
  RunOnDrop() : fun() {}
  RunOnDrop(F fun) : fun(some(std::move(fun))) {}
  RunOnDrop(RunOnDrop&& other) : RunOnDrop() { fun = other.fun.take(); }
  RunOnDrop& operator=(RunOnDrop&& other) {
    fun = other.fun.take();
    return *this;
  }
  ~RunOnDrop() {
    if (fun) {
      (*fun)();
      fun = Option<F>();
    }
  }
};

template<class F>
RunOnDrop(F) -> RunOnDrop<F>;
 

} // namespace Lib

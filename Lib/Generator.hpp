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
 * @file Generator.hpp
 * Defines class Generator, a lazy sequence produced by a C++20 coroutine.
 */

#ifndef __Generator__
#define __Generator__

#include <coroutine>
#include <exception>
#include <utility>

#include "Lib/Allocator.hpp"
#include "Lib/Option.hpp"
#include "Lib/Reflection.hpp"

namespace Lib {

/**
 * A lazily evaluated sequence of @b T, written as an ordinary function with loops that
 * @b co_yield s its elements.
 *
 * A Generator satisfies Vampire's duck-typed iterator protocol (DECL_ELEMENT_TYPE plus
 * @b hasNext() / @b next()), so it can be handed to @b pvi(), @b iterTraits(),
 * @b TIME_TRACE_ITER etc. exactly like any other iterator:
 *
 *   Generator<Clause*> myRule(Clause* premise) {
 *     for (Literal* lit : premise->getSelectedLiteralIterator())
 *       if (Clause* c = doSomething(premise, lit))
 *         co_yield c;
 *   }
 *   ...
 *   ClauseIterator generateClauses(Clause* premise) { return pvi(myRule(premise)); }
 *
 * The object is move-only, and nothing at all runs until the first call to hasNext():
 * merely creating a Generator has no side effects. Destroying a partially consumed
 * Generator destroys the coroutine frame, which runs the destructors of everything the
 * suspended body still has in scope -- so iterators the body was walking are released
 * (and, for substitution trees, backtracked) just as they would be in a hand-written
 * iterator chain.
 *
 * @warning A value borrowed from an iterator the body itself is driving must be consumed
 * *before* the co_yield, never carried across one. The important case is a
 * QueryRes<AbstractingUnifier*, ...> coming out of an index query: its @b unifier aliases
 * state owned by the still-live substitution-tree iterator, and is undone as soon as that
 * iterator is advanced -- which is precisely what happens when the Generator is resumed.
 *
 * @warning For the same reason do not open a TIME_TRACE scope that spans a co_yield:
 * Shell::TimeTrace keeps a stack of open scopes, so a scope left open across a suspension
 * would be charged for the consumer's work as well, would adopt the consumer's scopes as
 * its children, and would break the LIFO discipline when the frame is destroyed. Wrap the
 * whole Generator in TIME_TRACE_ITER at the call site instead, which measures exactly the
 * intervals during which the body is actually running.
 */
template<class T>
class Generator {
public:
  DECL_ELEMENT_TYPE(T);

  class promise_type {
    friend class Generator;

    Option<T> _value;
    std::exception_ptr _exception;

  public:
    // route the coroutine frame through Vampire's allocator; the compiler prefers the
    // sized deallocation function, which is the one Lib::free needs
    void *operator new(size_t size) { return Lib::alloc(size); }
    void operator delete(void *ptr, size_t size) { Lib::free(ptr, size); }

    Generator get_return_object()
    { return Generator(std::coroutine_handle<promise_type>::from_promise(*this)); }

    /* suspend_always: creating the Generator runs none of the body */
    std::suspend_always initial_suspend() noexcept { return {}; }
    /* suspend_always: the frame outlives the body, so that done() can be observed */
    std::suspend_always final_suspend() noexcept { return {}; }

    std::suspend_always yield_value(T value)
    {
      _value = some(std::move(value));
      return {};
    }

    void return_void() {}

    /* stash rather than rethrow: an exception must not escape while the frame is only
     * half unwound. Generator::hasNext() rethrows it on the consumer's stack instead. */
    void unhandled_exception() { _exception = std::current_exception(); }

    /* this is a generator, not a task: co_await makes no sense here */
    template<class U> std::suspend_never await_transform(U &&) = delete;
  };

  Generator() = default;

  Generator(Generator const&) = delete;
  Generator &operator=(Generator const&) = delete;

  Generator(Generator &&other) noexcept
    : _handle(std::exchange(other._handle, {})) {}

  Generator &operator=(Generator &&other) noexcept
  {
    if(this != &other) {
      if(_handle)
        _handle.destroy();
      _handle = std::exchange(other._handle, {});
    }
    return *this;
  }

  ~Generator()
  {
    if(_handle)
      _handle.destroy();
  }

  bool hasNext()
  {
    if(!_handle)
      return false;
    // an element produced by an earlier hasNext() is still waiting to be taken:
    // hasNext() must be idempotent
    if(_handle.promise()._value.isSome())
      return true;
    if(_handle.done())
      return false;

    _handle.resume();

    if(_handle.promise()._exception) {
      // clear it first: the frame is destroyed by ~Generator, which must not see it again
      auto exception = std::exchange(_handle.promise()._exception, {});
      std::rethrow_exception(exception);
    }

    return _handle.promise()._value.isSome();
  }

  /**
   * Return the next element.
   *
   * @warning as everywhere in Vampire, hasNext() must be called (and return true) before
   * each call to this function.
   */
  T next()
  {
    ASS(_handle)
    ASS(_handle.promise()._value.isSome())

    return _handle.promise()._value.take().unwrap();
  }

private:
  explicit Generator(std::coroutine_handle<promise_type> handle) : _handle(handle) {}

  std::coroutine_handle<promise_type> _handle = nullptr;
};

} // namespace Lib

#endif // __Generator__

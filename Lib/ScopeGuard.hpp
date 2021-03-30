/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef SCOPEGUARD_HPP
#define SCOPEGUARD_HPP

#include "Lib/STL.hpp"
#include <exception>
#include <utility>

namespace Lib
{


/// Calls the given function when the ScopeGuard goes out of scope (i.e., is destructed).
/// The given function is called exactly once.
template <typename Callable>
class ScopeGuard final
{
  public:
    explicit ScopeGuard(Callable&& f)
      : active{true}
      , f(std::forward<Callable>(f))
    { }

    ScopeGuard() = delete;

    // Disallow copy
    ScopeGuard(ScopeGuard const&) = delete;
    ScopeGuard& operator=(ScopeGuard const&) = delete;

    ScopeGuard(ScopeGuard&& other)
      : active{std::exchange(other.active, false)}
      , f(std::move(other.f))
    { }

    // Disallow moving into a ScopeGuard.
    // The reason is that if the LHS is still active, we should call execute() before moving
    // (to uphold the guarantee that f() is called exactly once).
    // However, this behaviour is somewhat unexpected for the user since it is not the point
    // where the guard goes out of scope.
    ScopeGuard& operator=(ScopeGuard&& other) = delete;

    ~ScopeGuard()
    {
      if (active) {
        execute();
      }
    }

  private:
    void execute()
    {
      active = false;
      if (!stackUnwindingInProgress()) {
        // ~ScopeGuard called normally
        f();
      } else {
        // ~ScopeGuard called during stack unwinding (this means we must not throw an exception)
        try {
          f();
        }
        catch(...) {
          /* do nothing */
          // TODO
          // It's bad to just swallow exceptions silently, but if it's just some not-so-important cleanup function we might not care.
          // For more important cases, maybe we should add a parameter that controls what to do in this case: terminate, ignore, something else???
          // std::terminate();

#if VDEBUG
          // In debug mode, just terminate so we notice there's a problem.
          std::cerr << "Exception in ~ScopeGuard during stack unwinding!" << std::endl;
          ASSERTION_VIOLATION;
#endif
        }
      }
    }

  private:
    bool active;
    Callable f;

    bool stackUnwindingInProgress() const {
      return std::uncaught_exception();
    }

    /*  C++17 only
    int exception_count = std::uncaught_exceptions();

    bool stackUnwindingInProgress() const {
      return exception_count != std::uncaught_exceptions();
    }
    */
};

template <typename Callable>
ScopeGuard<Callable> make_scope_guard(Callable&& f)
{
  return ScopeGuard<Callable>(std::forward<Callable>(f));
}


#define ON_SCOPE_EXIT_CONCAT_HELPER(X,Y) X ## Y
#define ON_SCOPE_EXIT_CONCAT(X,Y) ON_SCOPE_EXIT_CONCAT_HELPER(X,Y)

#define ON_SCOPE_EXIT(stmt) \
  auto ON_SCOPE_EXIT_CONCAT(on_scope_exit_guard_on_line_,__LINE__) = make_scope_guard([&]() { stmt; });

// We don't need make_scope_guard in C++17 or later:
// feature is called "class template argument deduction"
/*
#define ON_SCOPE_EXIT(stmt) \
  ScopeGuard ON_SCOPE_EXIT_CONCAT(on_scope_exit_guard_on_line_,__LINE__){[&]() { stmt; }};
*/

}

#endif /* !SCOPEGUARD_HPP */

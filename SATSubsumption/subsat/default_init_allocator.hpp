/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef DEFAULT_INIT_ALLOCATOR_HPP
#define DEFAULT_INIT_ALLOCATOR_HPP

#include <memory>


/// Allocator adaptor that interposes construct() calls to
/// convert value initialization into default initialization.
/// See https://stackoverflow.com/a/21028912
template <typename T, typename A = std::allocator<T>>
class default_init_allocator : public A
{
  using a_t = std::allocator_traits<A>;

public:
  template <typename U>
  struct rebind
  {
    using other = default_init_allocator<U, typename a_t::template rebind_alloc<U>>;
  };

  // inherit constructors from A
  using A::A;

  template <typename U>
  void construct(U* ptr) noexcept(std::is_nothrow_default_constructible<U>::value)
  {
    ::new(static_cast<void*>(ptr)) U;
  }

  template <typename U, typename... Args>
  void construct(U* ptr, Args&&... args)
  {
    a_t::construct(static_cast<A&>(*this), ptr, std::forward<Args>(args)...);
  }
};


#endif /* !DEFAULT_INIT_ALLOCATOR_HPP */

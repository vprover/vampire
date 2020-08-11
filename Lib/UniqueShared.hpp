#ifndef __UNIQUE_SHARED_HPP__
#define __UNIQUE_SHARED_HPP__

#include <functional>
#include "Lib/Map.hpp"

namespace Lib {

/** 
 * Smart pointer for aggressively sharing objects.
 *
 * This means that all objects of type T that are structurally equal, will be represented by the same pointer UniqueShared<T>.
 * This makes equality comparisons, hashing, and copying constant time operations.
 *
 * T is required to be comparable with `bool operator(const T&, const T&)`, and hashable with `std::hash<T>`.
 *
 * Further T must be copy constructible. // TODO get rid of this restriction
 */
template<class T>
class UniqueShared 
{
  using Cache = Map<T, T*, StlHash<T>>;

  T* _elem;
  static Cache _cached;

  /** 
   * If an equal object to elem exists, a pointer to that object is returned.
   * Otherwise elem is moved to the heap, and a pointer to that heap location is returned.
   */
  explicit UniqueShared(T&& elem) 
    : _elem(_cached.getOrInit(T(elem), [elem]() { 
          return new T(std::move(elem)); 
      })) 
    { }
public:

  /** copy constructor. Constant time. */
  UniqueShared(UniqueShared const& t) : _elem(t._elem) {  }

  /** copy constructor. Constant time. */
  UniqueShared(UniqueShared      & t) : _elem(t._elem) {  }

  /** default constructor. for this T must be default-constructible itself. */
  UniqueShared() : _elem(unique(T())) {}

  template<class U> friend bool operator==(UniqueShared<U> const& l, UniqueShared<U> const& r)
  { return l._elem == r._elem; }

  template<class U> friend bool operator!=(UniqueShared<U> const& l, UniqueShared<U> const& r)
  { return l != r; }

  /** dereferencing the smart pointer */
  T const* operator->() const& { return _elem; }
  T      * operator->()      & { return _elem; }

  T const& operator*() const& { return *_elem; }
  T      & operator*()      & { return *_elem; }
  T     && operator*()     && { return *_elem; }

  /** implicit conversions */
  operator T const&() const& { return *_elem; }
  operator T      &()      & { return *_elem; }
  operator T     &&()     && { return *_elem; }

  friend std::ostream& operator<<(std::ostream& out, UniqueShared& self) 
  { return out << *self._elem; }

  template<class U> 
  friend UniqueShared<U> unique(U&& t);
  friend struct std::hash<UniqueShared<T>>;
};

/** instantiating the cache */
template<class T> typename UniqueShared<T>::Cache UniqueShared<T>::_cached;

/** function to create a UniqueShared<T> ergonomically (with the help of type deduction) */
template<class T> UniqueShared<T> unique(T&& t) 
{ return UniqueShared<T>(std::move(t)); }

} // namespace Lib

template<class T> struct std::hash<Lib::UniqueShared<T>> 
{
  size_t operator()(Lib::UniqueShared<T> const& self) const 
  { return std::hash<size_t>{}((size_t) self._elem); }
};

#endif // __UNIQUE_SHARED_HPP__

#ifndef __UNIQUE_SHARED_HPP__
#define __UNIQUE_SHARED_HPP__

#include <functional>
#include "Lib/Map.hpp"
#include "Debug/Tracer.hpp"

namespace Lib {


template<class T>
struct UniqueSharedPtrComparison ;

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
template<class T, class DfltComparison = UniqueSharedPtrComparison<T> >
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

  /** implicit conversions */
  operator T const&() const& { return *_elem; }
  operator T      &()      & { return           *_elem ; }

  friend std::ostream& operator<<(std::ostream& out, const UniqueShared& self) 
  { return out << *self._elem; }

  template<class U, class Cmp> friend UniqueShared<U, Cmp> unique(U&& t);
  friend struct std::hash<UniqueShared<T, DfltComparison>>;

  template<class U> friend struct UniqueSharedPtrComparison;
}; // class UniqueShared

/** instantiating the cache */
template<class T, class Cmp> typename UniqueShared<T, Cmp>::Cache UniqueShared<T, Cmp>::_cached;

template<class T>
struct UniqueSharedPtrComparison 
{
  template<class Cmp>
  bool operator()(const UniqueShared<T, Cmp>& lhs, const UniqueShared<T, Cmp>& rhs) const
  { return lhs._elem < rhs._elem; }
};


/** function to create a UniqueShared<T> ergonomically (with the help of type deduction) */
template<class T, class Cmp = UniqueSharedPtrComparison<T>> 
UniqueShared<T, Cmp> unique(T&& t) 
{ return UniqueShared<T, Cmp>(std::move(t)); }

} // namespace Lib

template<class T, class Cmp> struct std::hash<Lib::UniqueShared<T, Cmp>> 
{
  size_t operator()(Lib::UniqueShared<T, Cmp> const& self) const 
  { return std::hash<size_t>{}((size_t) self._elem); }
};


template<class T, class Cmp> struct std::less<Lib::UniqueShared<T, Cmp>> 
{
  bool operator()(Lib::UniqueShared<T, Cmp> const& lhs, Lib::UniqueShared<T, Cmp> const& rhs) const 
  { return Cmp{}(lhs, rhs); }
};

#endif // __UNIQUE_SHARED_HPP__

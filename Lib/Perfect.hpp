#ifndef __UNIQUE_SHARED_HPP__
#define __UNIQUE_SHARED_HPP__

#include <functional>
#include "Lib/Map.hpp"
#include "Debug/Tracer.hpp"

namespace Lib {


template<class T>
struct PerfectPtrComparison ;

/** 
 * Smart pointer for perfectly sharing objects.
 *
 * This means that all objects of type T that are structurally equal, will be represented by the same pointer Perfect<T>.
 * This makes equality comparisons, hashing, and copying constant time operations.
 *
 * T is required to be comparable with `bool operator(const T&, const T&)`, and hashable with `std::hash<T>`.
 *
 * Further T must be copy constructible. // TODO get rid of this restriction (using a HashSet instead of a HashMap (?))
 */
template<class T, class DfltComparison = PerfectPtrComparison<T> >
class Perfect 
{
  using Cache = Map<T, T*, StlHash<T>>;

  T* _elem;
  static Cache _cached;

public:
  /** 
   * If an equal object to elem exists, a pointer to that object is returned.
   * Otherwise elem is moved to the heap, and a pointer to that heap location is returned.
   */
  explicit Perfect(T&& elem) 
    : _elem(_cached.getOrInit(T(elem), [elem]() { 
          auto mem = ALLOC_KNOWN(sizeof(T), typeid(Perfect).name());
          ::new(mem) T(std::move(elem)); 
          return (T*) mem;
      })) 
    { }

  /** copy constructor. Constant time. */
  Perfect(Perfect      & t) : _elem(t._elem) {  }

  /** copy constructor. Constant time. */
  Perfect(Perfect const& t) : _elem(t._elem) {  }

  /** default constructor. for this T must be default-constructible itself. */
  Perfect() : _elem(perfect(T())) {}

  template<class U, class C> friend bool operator==(Perfect<U, C> const& l, Perfect<U, C> const& r);

  /** dereferencing the smart pointer */
  T const* operator->() const& { return _elem; }
  T      * operator->()      & { return _elem; }

  T const& operator*() const& { return *_elem; }
  T      & operator*()      & { return *_elem; }

  friend std::ostream& operator<<(std::ostream& out, const Perfect& self) 
  { return out << *self._elem; }

  friend struct std::hash<Perfect<T, DfltComparison>>;

  template<class U> friend struct PerfectPtrComparison;

  template<class U, class C> 
  friend bool operator<(const Lib::Perfect<U, C> & lhs, const Lib::Perfect<U, C>& rhs);

}; // class Perfect


template<class U, class C> 
bool operator<(const Lib::Perfect<U, C> & lhs, const Lib::Perfect<U, C>& rhs) 
{ return std::less<Lib::Perfect<U, C>>{}(lhs,rhs); }

template<class U, class C> bool operator==(Perfect<U, C> const& l, Perfect<U, C> const& r)
{ return l._elem == r._elem; }

template<class U, class C> bool operator!=(Perfect<U, C> const& l, Perfect<U, C> const& r)
{ return !(l == r); }

/** instantiating the cache */
template<class T, class Cmp> typename Perfect<T, Cmp>::Cache Perfect<T, Cmp>::_cached;

template<class T>
struct PerfectPtrComparison 
{
  template<class Cmp>
  bool operator()(const Perfect<T, Cmp>& lhs, const Perfect<T, Cmp>& rhs) const
  { return lhs._elem < rhs._elem; }
};


/** function to create a Perfect<T> ergonomically (with the help of type deduction) */
template<class T, class Cmp = PerfectPtrComparison<T>> 
Perfect<T, Cmp> perfect(T&& t) 
{ return Perfect<T, Cmp>(std::move(t)); }

} // namespace Lib

template<class T, class Cmp> struct std::hash<Lib::Perfect<T, Cmp>> 
{
  size_t operator()(Lib::Perfect<T, Cmp> const& self) const 
  { return std::hash<size_t>{}((size_t) self._elem); }
};


template<class T, class Cmp> struct std::less<Lib::Perfect<T, Cmp>> 
{
  bool operator()(Lib::Perfect<T, Cmp> const& lhs, Lib::Perfect<T, Cmp> const& rhs) const 
  { return Cmp{}(lhs, rhs); }
};

#endif // __UNIQUE_SHARED_HPP__

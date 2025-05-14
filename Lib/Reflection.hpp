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
 * @file Reflection.hpp
 * Defines class Reflection.
 */


#ifndef __Reflection__
#define __Reflection__

#include "Lib/Comparison.hpp"
#include <type_traits>
#include <initializer_list>


///@addtogroup Reflection
///@{


#define DEFAULT_CONSTRUCTORS(Class)                                                       \
  Class(Class const&) = default;                                                          \
  Class(Class     &&) = default;                                                          \
  Class& operator=(Class const&) = default;                                               \
  Class& operator=(Class     &&) = default;                                               \

#define IMPL_COMPARISONS_FROM_TUPLE(Class)                                                \
  friend bool operator==(Class const& l, Class const& r)                                  \
  { return l.asTuple() == r.asTuple(); }                                                  \
                                                                                          \
  friend bool operator<(Class const& l, Class const& r)                                   \
  { return l.asTuple() < r.asTuple(); }                                                   \
                                                                                          \
  IMPL_COMPARISONS_FROM_LESS_AND_EQUALS(Class)                                            \

#define __IMPL_COMPARISONS_FROM_COMPARE(Class, op, ...)                                   \
  friend bool operator op(Class const& l, Class const& r) {                               \
    switch (DefaultComparator::compare(l,r)) {                                            \
      __VA_ARGS__ return true;                                                            \
      default:    return false;                                                           \
    }                                                                                     \
  }                                                                                       \

#define IMPL_EQ_FROM_COMPARE(Class)                                                       \
  friend bool operator==(Class const& l, Class const& r)                                  \
  { return DefaultComparator::compare(l,r) == Comparison::EQUAL; }                        \
                                                                                          \
  friend bool operator!=(Class const& l, Class const& r)                                  \
  { return !(l == r); }                                                                   \

#define IMPL_COMPARISONS_FROM_COMPARE(Class)                                              \
    __IMPL_COMPARISONS_FROM_COMPARE(Class, > , case GREATER:             )                \
    __IMPL_COMPARISONS_FROM_COMPARE(Class, < , case LESS   :             )                \
    __IMPL_COMPARISONS_FROM_COMPARE(Class, >=, case GREATER: case EQUAL: )                \
    __IMPL_COMPARISONS_FROM_COMPARE(Class, <=, case LESS   : case EQUAL: )                \


#define IMPL_COMPARISONS_FROM_LESS_AND_EQUALS(Class)                                      \
  friend bool operator> (Class const& l, Class const& r) { return r < l; }                \
  friend bool operator<=(Class const& l, Class const& r) { return l == r || l < r; }      \
  friend bool operator>=(Class const& l, Class const& r) { return l == r || l > r; }      \
  friend bool operator!=(Class const& l, Class const& r) { return !(l == r); }            \

#define IMPL_HASH_FROM_TUPLE(Class)                                                       \
  unsigned defaultHash() const { return DefaultHash::hash(asTuple()); }                   \
  unsigned defaultHash2() const { return DefaultHash2::hash(asTuple()); }                 \

//The obvious way to define this macro would be
//#define DECL_ELEMENT_TYPE(T) typedef T _ElementType
//but the preprocessor understands for example
//M(std::pair<A,B>)
//as an instantiation of  macro M with two arguments --
//pair<A is first and B> second.

/**
 * Declare type returned by an iterator
 *
 * To be used inside a public block of a class declaration
 *
 * There is no need to use this macro in a descendant of the
 * @b IteratorCore class, as this class already contains this
 * declaration.
 *
 * Although the macro formally takes variable number of arguments, it
 * should be used only with a single argument. The variable number
 * of formal arguments is to allow for the use of template types,
 * such as std::pair<int,int>, since the preprocessor considers every
 * comma as an argument separator.
 */
#define DECL_ELEMENT_TYPE(...) typedef __VA_ARGS__ _ElementType

/**
 * Type of elements in the iterator/collection @b __VA_ARGS__
 * This functions is variadic as the argument might be generic, hence contain commas
 *
 * The class @b __VA_ARGS__ must have its element type declared by the
 * @b DECL_ELEMENT_TYPE macro in order for this macro to be applicable
 * (Except for cases that are handled by a partial specialization
 * of the @b Lib::ElementTypeInfo template class.)
 *
 * @see DECL_ELEMENT_TYPE, Lib::ElementTypeInfo
 */
#define ELEMENT_TYPE(...) typename Lib::ElementTypeInfo<__VA_ARGS__>::Type

/**
 * Type of elements of the current class
 *
 * The current class must have its element type declared by the
 * @b DECL_ELEMENT_TYPE macro in order for this macro to be applicable
 *
 * @see DECL_ELEMENT_TYPE
 */
#define OWN_ELEMENT_TYPE _ElementType

/**
 * Declare the iterator type for a container class
 *
 * To be used inside a public block of declaration of a container class.
 *
 * An iterator type is a class with a constructor that takes (a reference
 * to) an instance of the container class, and then provides functions
 * @b hasNext() and @b next() to iterate through elements of the
 * container.
 *
 * Although the macro formally takes variable number of arguments, it
 * should be used only with a single argument. The variable number
 * of formal arguments is to allow for the use of template types,
 * such as std::pair<int,int>, since the preprocessor considers every
 * comma as an argument separator.
 */
#define DECL_ITERATOR_TYPE(...) typedef __VA_ARGS__ _IteratorType

/**
 * Return iterator type of the container class @b Cl
 *
 * An iterator type is a class with a constructor that takes (a reference
 * to) an instance of the container class, and then provides functions
 * @b hasNext() and @b next() to iterate through elements of the
 * container.
 *
 * The class @b Cl must have its iterator type declared by the
 * @b DECL_ITERATOR_TYPE macro in order for this macro to be applicable.
 * (Except for cases that are handled by a partial specialization
 * of the @b Lib::IteratorTypeInfo template class.)
 *
 * @see DECL_ITERATOR_TYPE, Lib::IteratorTypeInfo
 */
#define ITERATOR_TYPE(Cl) typename Lib::IteratorTypeInfo<Cl>::Type

/**
 * Iterator type of the current container class
 *
 * An iterator type is a class with a constructor that takes (a reference
 * to) an instance of the container class, and then provides functions
 * @b hasNext() and @b next() to iterate through elements of the
 * container.
 *
 * The current class must have its iterator type declared by the
 * @b DECL_ITERATOR_TYPE macro in order for this macro to be applicable
 *
 * @see DECL_ITERATOR_TYPE
 */
#define OWN_ITERATOR_TYPE _IteratorType

namespace Lib {

/**
 * A helper class that is used by the @b ELEMENT_TYPE macro to obtain
 * element types in iterator and container types
 *
 * The default implementation uses the @b _ElementType typedef which
 * is being declared by the @b DECL_ELEMENT_TYPE macro inside a class.
 *
 * If the use of the @b DECL_ELEMENT_TYPE macro is not suitable for some
 * type, the same effect can be achieved by a partial specialization of
 * this class that contains a typedef of the appropriate element type
 * to a new type @b Type. An example of this can be @b ElementTypeInfo<T[]>
 * which is this kin of specialisation for arrays.
 *
 * @see ELEMENT_TYPE, DECL_ELEMENT_TYPE
 */
template<typename T>
struct ElementTypeInfo
{
  typedef typename T::_ElementType Type;
};

/**
 * ElementTypeInfo for arrays.
 *
 * @see ElementTypeInfo
 */
template<typename T>
struct ElementTypeInfo<T[]>
{
  typedef T Type;
};

/**
 * ElementTypeInfo for pointers
 *
 * @see ElementTypeInfo
 */
template<typename T>
struct ElementTypeInfo<T*>
{
  typedef T Type;
};

template<class C> 
struct ElementTypeInfo<std::initializer_list<C>> {
  using Type = C;
};

/**
 * A helper class that is used by the @b ITERATOR_TYPE macro to obtain
 * iterator types for container classes
 *
 * The default implementation uses the @b _IteratorType typedef which
 * is being declared by the @b DECL_ITERATOR_TYPE macro inside a class.
 *
 * If the use of the @b DECL_ITERATOR_TYPE macro is not suitable for some
 * type, the same effect can be achieved by a partial specialization of
 * this class that contains a typedef of the appropriate element type
 * to a new type @b Type. An example of this can be @b IteratorTypeInfo<List<T>*>
 * in the List.hpp file which is this kind of specialisation for lists.
 *
 * @see ITERATOR_TYPE, DECL_ITERATOR_TYPE
 */
template<typename T>
struct IteratorTypeInfo
{
  typedef typename T::_IteratorType Type;
};

/**
 * IteratorTypeInfo for const types
 *
 * @see IteratorTypeInfo
 */
template<typename T>
struct IteratorTypeInfo<T const>
{
  typedef typename IteratorTypeInfo<T>::Type Type;
};


};

///@}�

#endif /* __Reflection__ */

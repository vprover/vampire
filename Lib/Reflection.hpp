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

///@}

#endif /* __Reflection__ */

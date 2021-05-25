/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LIB_TYPELIST__H__
#define __LIB_TYPELIST__H__

#include <functional>

namespace Lib {

  template<class F, class... As> using ResultOf = typename std::result_of<F(As...)>::type;

namespace TypeList {


  /* Meta level type constructor.
   *
   * List : [class] -> class 
   */
  template<class... As> struct List;

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////// FUNTIONS RETURNING TYPES 
  ////////////////////////////////////////

  /* Meta level type function. 
   * into : ([class] -> class) -> List [class] -> class 
   *
   * Transforms a List<As...> into another type with the same variadic type arguments. 
   * E.g. Into< Coproduct, List<As...>> ==>  Coproduct<As...>
   *      Into<std::tuple, List<As...>> ==> std::tuple<As...>
   */
  template<template<class...> class HKT, class A> 
  struct IntoImpl;

  template<template<class...> class HKT, class... As> 
  struct IntoImpl<HKT, List<As...> >
  { using type = HKT<As...>; };

  template<template<class...> class HKT, class A> 
  using Into = typename IntoImpl<HKT, A>::type;

  /* Meta level type function. 
   * concat : List [class] -> List [class] -> List [class] 
   *
   * Concatenates two List<...>s. 
   *
   * E.g. Concat<List<A, B>, List<A, B>> ==>  List<A,B,A,B>
   */  
  template<class A, class B> struct ConcatImpl;

  template<class... As, class... Bs> 
  struct ConcatImpl<List<As...>, List<Bs...>>
  { using type = List<As..., Bs...>; };

  template<class A, class B> 
  using Concat = typename ConcatImpl<A,B>::type;


  /* Meta level type function. 
   * get : List [class] -> unsigned -> class
   *
   * returns the nth element of the type list
   *
   * E.g. Get<2, List<A,B,C,D>> ==> C
   */  
  template<unsigned i, class A> struct GetImpl;
  template<unsigned i, class A> using Get = typename GetImpl<i,A>::type;

  template<class A, class... As> struct GetImpl<0, List<A, As...>>
  { using type = A; };

  template<unsigned i, class A, class... As> struct GetImpl<i, List<A, As...>>
  { using type = Get<i - 1, List<As...>>; };


  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////// FUNTIONS RETURNING VALUES 
  ////////////////////////////////////////

  /* Meta level function. 
   * size : List [class] -> unsigned
   *
   * returns the number of elements in the list
   *
   * E.g. Cnt<B, List<A,B,C,B>>::val ==> 4
   */  
  template<class As> struct Size;

  template<> struct Size<List<>> 
  { static unsigned constexpr val = 0; };

  template<class A, class... As> struct Size<List<A, As...>> 
  { static unsigned constexpr val = 1 + Size<List<As...>>::val; };


  /* Meta level function. 
   * cnt : class -> List [class] -> unsigned
   *
   * returns the number of occurences of an element in a list
   *
   * E.g. Cnt<B, List<A,B,C,B>>::val ==> 2
   */  
  template<class A, class As> struct Cnt;

  template<class A> struct Cnt<A, List<>> 
  { static unsigned constexpr val = 0; };

  template<class A,          class... Bs> struct Cnt<A, List<A, Bs...>> 
  { static unsigned constexpr val = 1 + Cnt<A, List<Bs...>>::val; };

  template<class A, class B, class... Bs> struct Cnt<A, List<B, Bs...>> 
  { static unsigned constexpr val =     Cnt<A, List<Bs...>>::val; };


  /* Meta level function. 
   * contains : class -> List [class] -> bool
   *
   * returns whether some type is in the list or not.
   *
   * E.g. Contains<B, List<A,B,C,D>>::val ==> true
   */  
  template<class A, class As> struct Contains;

  template<class A, class... As> struct Contains<A, List<As...>> 
  { static bool constexpr val = Cnt<A,List<As...>>::val > 0; };
  
  /* Meta level function. 
   * fistIdxOf : class -> List [class] -> unsigned
   *
   * returns the index of the first occurrence of a type
   *
   * E.g. FirstIdxOf<B, List<A,B,C,B>>::val ==> 1
   */  
  template<class A, class As> struct FirstIdxOf;

  template<class A, class... As> struct FirstIdxOf<A, List<A, As...>> 
  { static unsigned constexpr val = 0; };

  template<class A, class B, class... Bs> struct FirstIdxOf<A, List<B, Bs...>> 
  { static unsigned constexpr val = 1 + FirstIdxOf<A, List<Bs...>>::val; };


  /* Meta level function. 
   * idxOf : class -> List [class] -> unsigned
   *
   * returns the index of the unique occurrence of a type in a list
   *
   * E.g. IdxOf<B, List<A,B,C,B>>::val ==> compile fail
   *      IdxOf<C, List<A,B,C,B>>::val ==> 2
   */  
  template<class A, class As> struct IdxOf;

  template<class A, class... As> struct IdxOf<A, List<As...>> 
  { 
    static_assert(Cnt<A, List<As...>>::val == 1, "Type must have one unique occurence in the list.");
    static unsigned constexpr val = FirstIdxOf<A, List<As...>>::val; 
  };


  template<unsigned idx, class A>
  struct Indexed {};

  /* 
   * Zipps the list of types terms with indices.
   *
   * E.g. WithIndices<List<A, B, A>> ==> List<Indexed<0, A>, Indexed<1, B>, Indexed<2, A>>
   */  
  template<unsigned acc, class As> struct WithIndicesImpl;

  template<class As> using WithIndices = typename WithIndicesImpl<0, As>::type;


  template<unsigned acc> struct WithIndicesImpl<acc, List<>> 
  { 
    using type = List<>;
  };

  template<unsigned acc, class A, class... As> struct WithIndicesImpl<acc, List<A, As...>> 
  { 
    using type = Concat<List<Indexed<acc, A>>, typename WithIndicesImpl<acc + 1, List<As...>>::type>;
  };


  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////// COMPILE TIME TESTS
  ////////////////////////////////

  namespace StaticTest {
    struct A{};
    struct B{};
    struct C{};
    struct D{};

    template<class... As> 
    struct Tuple {
      Tuple(As...);
    };

    struct MkTuple {
      template<class A, class B> 
      Tuple<A, B> operator()(A,B) const;
    };


#   define STATIC_TEST_TYPE_EQ(...) \
       static_assert(std::is_same< __VA_ARGS__ >::value, "TEST FAIL: types don't match fail");

#   define STATIC_TEST_VAL_EQ(...) \
       static_assert(__VA_ARGS__, "TEST FAIL: values don't match fail");

    STATIC_TEST_TYPE_EQ(
        std::result_of<MkTuple(A,B)>::type,
        Tuple<A, B>)

    STATIC_TEST_TYPE_EQ(
        Into<Tuple, List<A, B, C> >,
        Tuple<A, B, C>)

    STATIC_TEST_TYPE_EQ(
       Concat<List<A, B>, List<A, B>>,
       List<A,B,A,B>)

    STATIC_TEST_TYPE_EQ(
       Get<2, List<A,B,C,D>>, 
       C)

    STATIC_TEST_VAL_EQ(
       Size<List<A, A, B, C, A>>::val == 5)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<>>::val == 0)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<B>>::val == 1)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<B, A>>::val == 1)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<A, B>>::val == 1)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<B, B>>::val == 2)

    STATIC_TEST_VAL_EQ(
       Cnt<B, List<A,B,C,B>>::val == 2)

    STATIC_TEST_VAL_EQ(
       Contains<B, List<A,B,C,D>>::val == true)

    STATIC_TEST_VAL_EQ(
       FirstIdxOf<B, List<A,B,C,B>>::val == 1)

    STATIC_TEST_VAL_EQ(
       IdxOf<C, List<A,B,C,B>>::val == 2)

    STATIC_TEST_TYPE_EQ(
       WithIndices<List<A, B, A>>,
       List<Indexed<0, A>, Indexed<1, B>, Indexed<2, A>>)
  }

} // namespace TypeList

} // namespace Lib


#endif // __LIB_TYPELIST__H__

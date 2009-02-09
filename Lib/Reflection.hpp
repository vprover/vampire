/**
 * @file Reflection.hpp
 * Defines class Reflection.
 */


#ifndef __Reflection__
#define __Reflection__

//The obvious way to define this macro would be
//#define DECL_ELEMENT_TYPE(T) typedef T _ElementType
//but the preprocessos understands for example
//M(pair<A,B>)
//as an instantiation of  macro M with two arguments --
//pair<A is first and B> second.
#define DECL_ELEMENT_TYPE(...) typedef __VA_ARGS__ _ElementType
#define ELEMENT_TYPE(Cl) typename ElementTypeInfo<Cl>::Type
#define OWN_ELEMENT_TYPE _ElementType

#define DECL_RETURN_TYPE(...) typedef __VA_ARGS__ _ReturnType
#define RETURN_TYPE(Cl) typename Cl::_ReturnType
#define OWN_RETURN_TYPE _ReturnType

#define DECL_ITERATOR_TYPE(...) typedef __VA_ARGS__ _IteratorType
#define ITERATOR_TYPE(Cl) typename IteratorTypeInfo<Cl>::Type
#define OWN_ITERATOR_TYPE _IteratorType

namespace Lib {

template<typename T>
struct ElementTypeInfo
{
  typedef typename T::_ElementType Type;
};

/**
 * ElementTypeInfo for arrays.
 */
template<typename T>
struct ElementTypeInfo<T[]>
{
  typedef T Type;
};

template<typename T>
struct ElementTypeInfo<T*>
{
  typedef T Type;
};

template<typename T>
struct IteratorTypeInfo
{
  typedef typename T::_IteratorType Type;
};

};

#endif /* __Reflection__ */

/**
 * @file Reflection.hpp
 * Defines class Reflection.
 */


#ifndef __Reflection__
#define __Reflection__

///@addtogroup Reflection
///@{


//The obvious way to define this macro would be
//#define DECL_ELEMENT_TYPE(T) typedef T _ElementType
//but the preprocessor understands for example
//M(pair<A,B>)
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
 * of formal arguments is to allow for use of template types,
 * such as pair<int,int>, since the preprocessor considers every
 * comma as an argument separator.
 */
#define DECL_ELEMENT_TYPE(...) typedef __VA_ARGS__ _ElementType

/**
 * Type of elements in the iterator/collection @b Cl
 *
 * The class @b Cl must have its element type declared by the
 * @b DECL_ELEMENT_TYPE macro in order for this macro to be applicable
 * (Except for cases that are handled by a partial specialization
 * of the @b ElementTypeInfo template class.)
 *
 * @see DECL_ELEMENT_TYPE, Lib::ElementTypeInfo
 */
#define ELEMENT_TYPE(Cl) typename Lib::ElementTypeInfo<Cl>::Type

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
 * Declare type returned by a functor class
 *
 * To be used inside a public block of declaration of a functor class.
 *
 * A functor class is a class with @b operator() defined, so that its
 * objects can be called as functions. The return type to be declared
 * by this macro is the return type of this operator.
 *
 * Although the macro formally takes variable number of arguments, it
 * should be used only with a single argument. The variable number
 * of formal arguments is to allow for use of template types,
 * such as pair<int,int>, since the preprocessor considers every
 * comma as an argument separator.
 */
#define DECL_RETURN_TYPE(...) typedef __VA_ARGS__ _ReturnType

/**
 * Return type of the functor class @b Cl
 *
 * The class @b Cl must have its return type declared by the
 * @b DECL_RETURN_TYPE macro in order for this macro to be applicable
 *
 * @see DECL_RETURN_TYPE
 */
#define RETURN_TYPE(Cl) typename Cl::_ReturnType

/**
 * Return type of the current functor class
 *
 * The current class must have its return type declared by the
 * @b DECL_RETURN_TYPE macro in order for this macro to be applicable
 *
 * @see DECL_RETURN_TYPE
 */
#define OWN_RETURN_TYPE _ReturnType

#define DECL_ITERATOR_TYPE(...) typedef __VA_ARGS__ _IteratorType
#define ITERATOR_TYPE(Cl) typename Lib::IteratorTypeInfo<Cl>::Type
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

template<typename T>
struct IteratorTypeInfo<T const>
{
  typedef typename IteratorTypeInfo<T>::Type Type;
};


};

///@}Á

#endif /* __Reflection__ */

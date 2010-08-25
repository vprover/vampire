/**
 * @file Type.hpp
 * Defines class Type
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramType__
#define __ProgramType__

#include "Debug/Assertion.hpp";

namespace Program {

/**
 * Types used in the program, currently just integers and arrays.
 * @since 20/08/2010, Torrevieja
 */
class Type
{
public:
	enum Kind {
		/** void type */
		VOID,
		/** integer, whatever it means */
		INT,
		/** boolean type */
		BOOL,
		/** all function types */
		FUNCTION,
		/** all kinds of arrays */
		ARRAY
	};
	/** the kind */
	Kind kind() const {return _kind; }

	/** the main constructor */
	explicit Type(Kind k) : _kind(k) {}

	static Type* voidType();
	static Type* integerType();
	static Type* booleanType();
	bool equals(const Type* tp) const;
protected:
	/** the kind */
	const Kind _kind;
	/** the void type, initialised upon demand */
	static Type* _voidType;
	/** the integer type, initialised upon demand */
	static Type* _integerType;
	/** the boolean type, initialised upon demand */
	static Type* _booleanType;
}; // class Type

/**
 * The type of arrays. Only one-dimentional arrays are
 * allowed.
 * @since 20/08/2010, Torrevieja
 */
class ArrayType
	: public Type
{
public:
	/** returns the value type of the array */
	const Type* valueType() const { return _valueType; }
	/** the constructor */
	ArrayType(const Type* vt)
		: Type(ARRAY),
			_valueType(vt)
	{}
protected:
	/** the value type of the array */
	const Type* _valueType;
}; // class ArrayType

/**
 * The type of functions.
 * @since 20/08/2010, Torrevieja
 */
class FunctionType
  : public Type
{
public:
  /** returns the value type of the array */
  const Type* valueType() const { return _valueType; }

  /** returns the n-th argument type */
  const Type* argumentType(unsigned n) const
  {
    ASS_L(n,_arity);
    return _argumentTypes[n];
  }

  unsigned arity() const { return _arity; }
  FunctionType(unsigned arity,const Type* valueType);

  /** set the argument type of an argument */
  inline void setArgumentType(unsigned argNumber,const Type* tp)
  {
    ASS_L(argNumber,_arity);
    ASS_EQ(_argumentTypes[argNumber],0);
    _argumentTypes[argNumber] = tp;
  }

protected:
  /** the number of arguments */
  unsigned _arity;
  /** the value type of the function */
  const Type* _valueType;
  /** the array of argument types */
  const Type** _argumentTypes;
}; // class FunctionType

}

#endif // __ProgramType__

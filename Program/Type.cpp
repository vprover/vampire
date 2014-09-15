/**
 *  @file Type.cpp
 *  Implements class Program::Type
 *
 * @since 20/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Type.hpp"

using namespace Program;

Type* Type::_integerType = 0;
Type* Type::_voidType = 0;
Type* Type::_booleanType = 0;

/** Return the unique void type */
Type* Type::voidType()
{
  if (! _voidType) {
    _voidType = new Type(VOID);
  }
  return _voidType;
}

/** Return the unique integer type */
Type* Type::integerType()
{
  if (! _integerType) {
    _integerType = new Type(INT);
  }
  return _integerType;
}

/** Return the unique boolean type */
Type* Type::booleanType()
{
  if (! _booleanType) {
    _booleanType = new Type(BOOL);
  }
  return _booleanType;
}

FunctionType::FunctionType(unsigned arity,const Type* valueType)
  : Type(FUNCTION),
    _arity(arity),
    _valueType(valueType)
{
  CALL("FunctionType::FunctionType");

  if (! arity) {
    _argumentTypes = 0;
    return;
  }
  _argumentTypes = static_cast<const Type**>(ALLOC_KNOWN(sizeof(const Type*)*arity,"FunctionType"));
#if VDEBUG
  for (int i = arity-1;i >= 0;i--) {
    _argumentTypes[i] = 0;
  }
#endif
}

/**
 * True if the types are equal.
 */
bool Type::equals(const Type* t) const
{
  CALL("Type::Equals");

  if (kind() != t->kind()) {
    return false;
  }
  switch (kind()) {
  case VOID:
  case INT:
  case BOOL:
    return true;
  case FUNCTION:
    {
      const FunctionType* t1 = static_cast<const FunctionType*>(this);
      const FunctionType* t2 = static_cast<const FunctionType*>(t);
      if (t1->arity() != t2->arity() ||
	  ! t1->valueType()->equals(t2->valueType())) {
	return false;
      }
      for (int i = t1->arity()-1;i >= 0;i--) {
	if (! t1->argumentType(i)->equals(t2->argumentType(i))) {
	  return false;
	}
      }
      return true;
    }

  default:
    ASS(false);
  }
}

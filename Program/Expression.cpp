/**
 *  @file Expression.cpp
 *  Implements class Program::Expression
 *
 * @since 20/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Lib/Int.hpp"
#include "Variable.hpp"
#include "Type.hpp"
#include "Expression.hpp"

using namespace Lib;
using namespace Program;

bool ConstantFunctionExpression::_initialized = false;
ConstantFunctionExpression* ConstantFunctionExpression::_integerEq = 0; 
ConstantFunctionExpression* ConstantFunctionExpression::_integerLess = 0; 
ConstantFunctionExpression* ConstantFunctionExpression::_integerLessEq = 0; 
ConstantFunctionExpression* ConstantFunctionExpression::_integerGreater = 0; 
ConstantFunctionExpression* ConstantFunctionExpression::_integerGreaterEq = 0; 
ConstantFunctionExpression* ConstantFunctionExpression::_integerPlus = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_integerMinus = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_integerNegation = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_integerMult = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_booleanAnd = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_booleanOr = 0;
ConstantFunctionExpression* ConstantFunctionExpression::_booleanNeg = 0;

/** Build a constant integer expression out of an integer */
ConstantIntegerExpression::ConstantIntegerExpression(int val)
  : Expression(CONSTANT_INTEGER),
    _value(val)
{
  _type = Type::integerType();
}

/** Build a variable expression out of a variable */
VariableExpression::VariableExpression(Variable* var)
  : Expression(VARIABLE),
    _variable(var)
{
  _type = var->vtype();
}

/** A variable expression is always an lvalue */
bool VariableExpression::lvalue() const
{
  return true;
}

/** A constant integer expression is not an lvalue */
bool ConstantIntegerExpression::lvalue() const
{
  return false;
}

/** constructor */
ConstantFunctionExpression::ConstantFunctionExpression(const char* name,Type* tp,unsigned priority)
  : Expression(CONSTANT_FUNCTION),
    _name(name),
    _priority(priority)
{
  _type = tp;
}

/** A constant function expression is not an lvalue */
bool ConstantFunctionExpression::lvalue() const
{
  return false;
}

/** initialize all built-ins */
void ConstantFunctionExpression::initialize()
{
  CALL("ConstantFunctionExpression::initialize");
  ASS(! _initialized);

  const Type* intType = Type::integerType();
  const Type* boolType = Type::booleanType();
  // int->int
  FunctionType* ii = new FunctionType(1,intType);
  ii->setArgumentType(0,intType);
  // int*int->bool
  FunctionType* iib = new FunctionType(2,boolType);
  iib->setArgumentType(0,intType);
  iib->setArgumentType(1,intType);
  // int*int->int
  FunctionType* iii = new FunctionType(2,intType);
  iii->setArgumentType(0,intType);
  iii->setArgumentType(1,intType);
  //bool*bool -> bool
  FunctionType* bbb = new FunctionType(2, boolType);
  bbb->setArgumentType(0, boolType);
  bbb->setArgumentType(1, boolType);
  //bool->bool
  FunctionType* bn = new FunctionType(1, boolType);
  bn->setArgumentType(0, boolType);

  _integerEq = new ConstantFunctionExpression("==",iib,2);
  _integerLess = new ConstantFunctionExpression("<",iib,2);
  _integerLessEq = new ConstantFunctionExpression("<=",iib,2);
  _integerGreater = new ConstantFunctionExpression(">",iib,2);
  _integerGreaterEq = new ConstantFunctionExpression(">=",iib,2);
  _integerPlus = new ConstantFunctionExpression("+",iii,4);
  _integerMinus = new ConstantFunctionExpression("-",iii,4);
  _integerNegation = new ConstantFunctionExpression("-",ii,1);
  _integerMult = new ConstantFunctionExpression("*",iii,3);
  _booleanAnd = new ConstantFunctionExpression("&&", bbb, 2);
  _booleanOr = new ConstantFunctionExpression("||",bbb,2);
  _booleanNeg = new ConstantFunctionExpression("!", bn, 1);
  _initialized = true;
}

/**Boolean negation*/

ConstantFunctionExpression* ConstantFunctionExpression::booleanNeg(){
  if (! _initialized) initialize();
  return _booleanNeg;
}

/** Boolean and*/
ConstantFunctionExpression* ConstantFunctionExpression::booleanAnd(){
  if (!_initialized) initialize();
  return _booleanAnd;
}

/** boolean or*/
ConstantFunctionExpression* ConstantFunctionExpression::booleanOr(){
  if (!_initialized) initialize();
  return _booleanOr;
}

/** integer equality */
ConstantFunctionExpression* ConstantFunctionExpression::integerEq()
{
  if (! _initialized) initialize();
  return _integerEq;
}

/** integer less than */
ConstantFunctionExpression* ConstantFunctionExpression::integerLess()
{
  if (! _initialized) initialize();
  return _integerLess;
}

/** integer less than or equal to */
ConstantFunctionExpression* ConstantFunctionExpression::integerLessEq() 
{
  if (! _initialized) initialize();
  return _integerLessEq;
}

/** integer greater than */
ConstantFunctionExpression* ConstantFunctionExpression::integerGreater() 
{
  if (! _initialized) initialize();
  return _integerGreater;
}

/** integer greater than or equal to */
ConstantFunctionExpression* ConstantFunctionExpression::integerGreaterEq() 
{
  if (! _initialized) initialize();
  return _integerGreaterEq;
}

/** integer plus */
ConstantFunctionExpression* ConstantFunctionExpression::integerPlus() 
{
  if (! _initialized) initialize();
  return _integerPlus;
}

/** integer minus */
ConstantFunctionExpression* ConstantFunctionExpression::integerMinus() 
{
  if (! _initialized) initialize();
  return _integerMinus;
}

/** integer unary minus */
ConstantFunctionExpression* ConstantFunctionExpression::integerNegation() 
{
  if (! _initialized) initialize();
  return _integerNegation;
}

/** integer product */
ConstantFunctionExpression* ConstantFunctionExpression::integerMult() 
{
  if (! _initialized) initialize();
  return _integerMult;
}

/** Constructor. The number of arguments will be computed from fun */
FunctionApplicationExpression::FunctionApplicationExpression(Expression* fun)
  : Expression(FUNCTION_APPLICATION),
    _function(fun)
{
  CALL("FunctionApplicationExpression::FunctionApplicationExpression");
  // currently only a variable expression or a constant function can be a function
  switch (fun->kind()) {
  case VARIABLE: 
    {
      // below, ve must be a variable expression and veType must be a variable type
      VariableExpression* ve = static_cast<VariableExpression*>(fun);
      const FunctionType* veType = static_cast<const FunctionType*>(ve->etype());
      ASS_EQ(veType->kind(),Type::FUNCTION);
      _type = veType->valueType();
      _numberOfArguments = veType->arity();
    }
    break;

  case CONSTANT_FUNCTION:
    {
      // below, ve must be a variable expression and veType must be a variable type
      ConstantFunctionExpression* cfe = static_cast<ConstantFunctionExpression*>(fun);
      const FunctionType* cfeType = static_cast<const FunctionType*>(cfe->etype());
      ASS_EQ(cfeType->kind(),Type::FUNCTION);
      _type = cfeType->valueType();
      _numberOfArguments = cfeType->arity();
    }
    break;

  case CONSTANT_INTEGER:
  case FUNCTION_APPLICATION:
  case ARRAY_APPLICATION:
    ASS(false);
  }

  if (_numberOfArguments == 0) {
    _arguments = 0;
    return;
  }
  _arguments = static_cast<Expression**>(ALLOC_KNOWN(sizeof(Expression*)*_numberOfArguments,"FunctionApplicationExpression"));  
#if VDEBUG
  for (int n = _numberOfArguments-1;n >= 0;n--) {
    _arguments[n] = 0;
  }
#endif
} // FunctionApplicationExpression::FunctionApplicationExpression

/** currently, function application expressions are not lvalues */
bool FunctionApplicationExpression::lvalue() const
{
  return false;
}

/**
 * Set an argument of a function application exptression.
 */
void FunctionApplicationExpression::setArgument(unsigned argNumber,Expression* e)
{
  CALL("FunctionApplicationExpression::setArgument");

  ASS_L(argNumber,_numberOfArguments);
  ASS(! _arguments[argNumber]);
  ASS(static_cast<const FunctionType*>(function()->etype())->argumentType(argNumber)->equals(e->etype()));
  _arguments[argNumber] = e;
}

/** array application expressions are lvalues */
bool ArrayApplicationExpression::lvalue() const
{
  return true;
}

/** Constructor */
ArrayApplicationExpression::ArrayApplicationExpression(Expression* arr,Expression* arg)
  : Expression(ARRAY_APPLICATION),
    _array(arr),
    _argument(arg)
{
  CALL("ArrayApplicationExpression::ArrayApplicationExpression");
  ASS_EQ(arg->etype()->kind(),Type::INT);
  ASS_EQ(arr->etype()->kind(),Type::ARRAY);

  const ArrayType* arrayType = static_cast<const ArrayType*>(arr->etype());
  _type = arrayType->valueType();
} // ArrayApplicationExpression::ArrayApplicationExpression

/** return the next subexpression */
Expression* Expression::SubexpressionIterator::next()
{
  CALL("Expression::SubexpressionIterator::next");
  Expression* expr = _stack.pop();

  switch (expr->kind()) {
  case VARIABLE: 
  case CONSTANT_FUNCTION:
  case CONSTANT_INTEGER:
    break;

  case FUNCTION_APPLICATION:
    {
      FunctionApplicationExpression* fun = static_cast<FunctionApplicationExpression*>(expr);
      _stack.push(fun->function());
      for (int i = fun->numberOfArguments()-1;i >= 0;i--) {
	_stack.push(fun->getArgument(i));
      }
    }
    break;

  case ARRAY_APPLICATION:
    {
      ArrayApplicationExpression* app = static_cast<ArrayApplicationExpression*>(expr);
      _stack.push(app->array());
      _stack.push(app->argument());
    }
    break;
  }

  return expr;
} // next

/** convert the expression to a string, can be used to output the expression */
vstring ConstantIntegerExpression::toString(unsigned priority) const
{
  return Int::toString(_value);
}

/** convert the expression to a string, can be used to output the expression */
vstring ConstantFunctionExpression::toString(unsigned priority) const
{
  return _name;
}

/** convert the expression to a string, can be used to output the expression */
vstring VariableExpression::toString(unsigned priority) const
{
  return _variable->name();
}

/** convert the expression to a string, can be used to output the expression */
vstring FunctionApplicationExpression::toString(unsigned priority) const
{
  CALL("FunctionApplicationExpression::toString");

  ASS(_function->kind() == CONSTANT_FUNCTION);
  ConstantFunctionExpression* fun = static_cast<ConstantFunctionExpression*>(_function);
  unsigned arity = fun->arity();
  unsigned pr = fun->priority();

  if (arity == 2 && pr > 0) {
    vstring result("");
    if (priority > 0 && pr >= priority) {
      result += '(';
    }
    result += _arguments[0]->toString(pr) + ' ' + _function->toString() + ' ' + _arguments[1]->toString(pr);
    if (priority > 0 && pr >= priority) {
      result += ')';
    }
    return result;
  }

  if (arity == 1 && pr > 0) {
    vstring result("");
    if (priority > 0 && pr >= priority) {
      result += '(';
    }
    result += _function->toString() + ' ' + _arguments[0]->toString(pr);
    if (priority > 0 && pr >= priority) {
      result += ')';
    }
    return result;
  }

  vstring result = _function->toString() + '(';
  if (_numberOfArguments > 0) {
    result += _arguments[0]->toString();
    for (unsigned n = 1;n < _numberOfArguments;n++) {
      result += vstring(",") + _arguments[n]->toString();
    }
  }
  return result + ")";
}

/** convert the expression to a string, can be used to output the expression */
vstring ArrayApplicationExpression::toString(unsigned priority) const
{
  CALL("ArrayApplicationExpression::toString");
  return _array->toString() + '[' + _argument->toString() + ']';
}

/** Return the arity of the function */
unsigned ConstantFunctionExpression::arity() const
{
  return static_cast<const FunctionType*>(etype())->arity();
}

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
ConstantFunctionExpression::ConstantFunctionExpression(const char* name,Type* tp)
	: Expression(CONSTANT_FUNCTION),
		_name(name)
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

	_integerEq = new ConstantFunctionExpression("=",iib);
	_integerLess = new ConstantFunctionExpression("<",iib);
	_integerLessEq = new ConstantFunctionExpression("<=",iib);
	_integerGreater = new ConstantFunctionExpression(">",iib);
	_integerGreaterEq = new ConstantFunctionExpression(">=",iib);
	_integerPlus = new ConstantFunctionExpression("+",iii);
	_integerMinus = new ConstantFunctionExpression("-",iii);
	_integerNegation = new ConstantFunctionExpression("-",ii);
	_integerMult = new ConstantFunctionExpression("*",iii);

	_initialized = true;
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
	_arguments = new Expression*[_numberOfArguments];
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
string ConstantIntegerExpression::toString() const
{
	return Int::toString(_value);
}

/** convert the expression to a string, can be used to output the expression */
string ConstantFunctionExpression::toString() const
{
	return _name;
}

/** convert the expression to a string, can be used to output the expression */
string VariableExpression::toString() const
{
	return _variable->name();
}

/** convert the expression to a string, can be used to output the expression */
string FunctionApplicationExpression::toString() const
{
	CALL("FunctionApplicationExpression::toString");

	string result = _function->toString() + '(';
	if (_numberOfArguments > 0) {
		result += _arguments[0]->toString();
		for (int n = 1;n < _numberOfArguments;n++) {
			result += string(",") + _arguments[0]->toString();
		}
	}
	return result + ")";
}

/** convert the expression to a string, can be used to output the expression */
string ArrayApplicationExpression::toString() const
{
	CALL("ArrayApplicationExpression::toString");
	return _array->toString() + '[' + _argument->toString() + ']';
}


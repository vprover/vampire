/**
 * @file Variable.hpp
 * Defines class Program::Variable
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramVariable__
#define __ProgramVariable__

#include "Type.hpp"

#include "Lib/VString.hpp"
#include "Lib/Allocator.hpp"

namespace Program {

/**
 * Variables used in programs
 * @since 20/08/2010, Torrevieja
 */
class Variable
{
public:
  CLASS_NAME(Variable);
  USE_ALLOCATOR(Variable);
  
	/** the main constructor */
	explicit Variable(const Lib::vstring& name,const Type* tp) : _name(name),_type(tp) {}
	/** the name of this variable */
	const Lib::vstring& name() { return _name; }
	/** the type */
	const Type* vtype() { return _type; }
protected:
	/** the name */
	const Lib::vstring _name;
	/** the type */
	const Type* _type;
}; // class Variable

}

#endif // __ProgramVariable__

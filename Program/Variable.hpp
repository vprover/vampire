/**
 * @file Variable.hpp
 * Defines class Program::Variable
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramVariable__
#define __ProgramVariable__

#include <string>
#include "Type.hpp"

using namespace std;

namespace Program {

/**
 * Variables used in programs
 * @since 20/08/2010, Torrevieja
 */
class Variable
{
public:
	/** the main constructor */
	explicit Variable(const string& name,const Type* tp) : _name(name),_type(tp) {}
	/** the name of this variable */
	const string& name() { return _name; }
	/** the type */
	const Type* vtype() { return _type; }
protected:
	/** the name */
	const string _name;
	/** the type */
	const Type* _type;
}; // class Variable

}

#endif // __ProgramVariable__

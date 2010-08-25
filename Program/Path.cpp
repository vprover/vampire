/**
 *  @file Path.cpp
 *  Implements class Program::Path
 *
 * @since 24/08/2010, Torrevieja
 */

#include "Path.hpp"
#include "Expression.hpp"
#include "Statement.hpp"

using namespace Program;

/**
 * Output the path to a stream
 */
void Path::prettyPrint(ostream& str)
{
  cout << "Path:\n";
  Iterator it(this);
  while (it.hasNext()) {
    Statement* stat = it.next();
    switch (stat->kind()) {
    case Statement::ASSIGNMENT:
      stat->prettyPrint(str,2);
      break;
    case Statement::ITE:
      {
	IfThenElse* ite = static_cast<IfThenElse*>(stat);
	str << "  "
	    << (it.next() == ite->elsePart() ? "false" : "true")
	    << ": " 
	    << ite->condition()->toString() << "\n";
      }
      break;
    case Statement::BLOCK:
    case Statement::WHILE_DO:
      break;
    case Statement::EXPRESSION:
      ASS(false); // cannot yet work with procedure calls
    }
  }
}

/** constructor */
Path::Iterator::Iterator(Path* path)
{
  List<Statement*>::Iterator stats(path);
  while (stats.hasNext()) {
    _stack.push(stats.next());
  }
}


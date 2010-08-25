/**
 * @file Path.hpp
 * Defines class Program::Path
 *
 * @since 24/08/2010, Torrevieja
 */

#ifndef __ProgramPath__
#define __ProgramPath__

#include <ostream>
#include "Debug/Assertion.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

using namespace std;
using namespace Lib;

namespace Program {

class Statement;

/**
 * Paths in programs. A path is a sequence of statements. Paths can share
 * common prefixes. For this reason, they are implemented as smart pointers
 * to lists.
 * @since 24/08/2010 Torrevieja
 */
class Path
  : public List<Statement*>
{
public:
  /** return a path obtaining by adding a statement to the end of the path */
  Path* add(Statement* st) { return static_cast<Path*>(new List<Statement*>(st,this)); }
  /** return the empty path */
  static Path* empty() { return 0; }
  void prettyPrint(ostream& str);

  /** An iterator that iterates elements from the beginning of the path */
  class Iterator {
  public:
    explicit Iterator(Path* path);
    /** Return true if there is a next element */
    bool hasNext() const { return ! _stack.isEmpty(); }
    /** return the next element */
    Statement* next() { return _stack.pop(); }
    /** return the next element without changing the state (the next call to next() will return it again) */
    Statement* showNext() { return _stack.top(); }
  protected:
    /** stack containing all elements */
    Stack<Statement*> _stack;
  };
}; // class Path


}

#endif // __ProgramExpression__

/**
 * @file Analyze.hpp
 * Defines class Program::Analyze
 *
 * @since 21/08/2010, Torrevieja
 */

#ifndef __ProgramAnalyze__
#define __ProgramAnalyze__

#include "Lib/Set.hpp"

using namespace Lib;

namespace Program {

class Variable;
class Expression;
class Statement;
class Assignment;
class WhileDo;

/**
 * Defines utilities for program analysis
 * @since 21/08/2010, Torrevieja
 */
class Analyze
{
public:
  Analyze(Statement* program);
  void analyze();
private:
  void analyzeSubstatements(Statement* statement);
  static void addExpressionVariables(Expression* exp,Statement* st);
  
  /** the program being analyzed */
  Statement* _program;
  /** the set of all loops */
  Set<WhileDo*> _loops;
}; // class Analyze

}

#endif // __ProgramVariable__

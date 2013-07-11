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
namespace Kernel{
  class Unit;
}

using namespace Kernel;
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
  List<Kernel::Unit*>* getUnits();
private:
  void analyzeSubstatements(Statement* statement);
  void preprocessStatement(Statement* statement);
  bool checkForIf(Statement* statement);
  Statement* concatenateStatements(Statement* block, List<Statement* >* list);
  Expression* treatCondition(Expression* condition, List<Statement* >* list);
  static void addExpressionVariables(Expression* exp,Statement* st);
  
  /** the program being analyzed */
  Statement* _program;
  /** the set of all loops */
  Set<WhileDo*> _loops;
}; // class Analyze

}

#endif // __ProgramVariable__

/**
 * @file LoopAnalyzer.hpp
 * Defines class Program::LoopAnalyzer for loop analysis
 *
 * @since 23/08/2010, Torrevieja
 */

#ifndef __ProgramLoopAnalyzer__
#define __ProgramLoopAnalyzer__

#include <string>
#include "Lib/Set.hpp"
#include "Lib/List.hpp"

namespace Kernel {
  class Unit;
};

using namespace std;
using namespace Lib;
using namespace Kernel;

namespace Program {

class Variable;
class WhileDo;
class Path;

/**
 * Class for loop analysis
 * @since 23/08/2010, Torrevieja
 */
class LoopAnalyzer
{
public:
  LoopAnalyzer(WhileDo* loop);
  void analyze();
private:
  Variable* isScalarAssignment(const Statement* st);
  static int isScalarIncrement(const Assignment* ass);
  void analyzeVariables();
  void collectPaths();
  void generateAxiomsForCounters();
  void generateCounterAxiom(const string& name,int min,int max,int gcd);

  /** the loop being analyzed */
  WhileDo* _loop;
  /** all variables updated by this loop */
  Set<Variable*> _updatedVariables;
  /** all variables that are counters. That is, they are updated and
   * either only decremented or incremented by a constant value */
  Set<Variable*> _counters;
  /** All paths in the loop */
  Stack<Path*> _paths;
  /** all generated units */
  List<Unit*>* _units;
}; // class Analyze

}

#endif // __ProgramVariable__

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
  class Term;
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
  Term* relativize(Expression* expr);

  /** the loop being analyzed */
  WhileDo* _loop;
  /** all variables updated by this loop */
  Set<Variable*> _updatedVariables;
  /** All paths in the loop */
  Stack<Path*> _paths;
  /** all generated units */
  List<Unit*>* _units;

  /** For every variable, this structure stores information used to
   * write down formulas containing the variable */
  struct VariableInfo {
    /** true if the variable is updated */
    bool updated;
    /** true if the variable is a counter. Counters are updated and
     * either only decremented or incremented by a constant value */
    bool counter;
    /** true if scalar (non-array) variable */
    bool scalar;
    /** signature number */
    unsigned signatureNumber;
    /** signature number for this symbol with an extra argument, only for updated variables */
    unsigned extraSignatureNumber;
    /** constant representing this variable, for scalar variables only */
    Term* constant;
  };

  typedef Map<Variable*,VariableInfo*> VariableMap;
  /** map from constant scalar variables to the corresponding terms */
  VariableMap _variableInfo;
}; // class Analyze

}

#endif // __ProgramVariable__

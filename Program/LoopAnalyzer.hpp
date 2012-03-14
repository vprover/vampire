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

#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Path.hpp"



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

  Variable* isScalarAssignment(const Statement* st);
  static int isScalarIncrement(const Assignment* ass);
  void analyzeVariables();
  void collectPaths();
  void generateAxiomsForCounters();
  void generateCounterAxiom(const string& name,int min,int max,int gcd);
  Term* relativize(Expression* expr);
  void generateLetExpressions();
  TermList expressionToTerm(Expression* exp);
  Formula*  expressionToPred(Expression* exp);
  TermList letTranslationOfPath(Path::Iterator& sit, TermList variable);
  Formula* letTranslationOfVar(VariableMap::Iterator& vit, Formula* letFormula); // VariableMap::Iterator&
  Formula* letTranslationOfArray(Map<Variable*,bool>::Iterator &sit, Formula* exp);
  Formula* letCondition(Path::Iterator &sit, Formula* condition, int condPos, int currPos);
  Formula* letTranslationOfGuards(Path* path, Path::Iterator &sit, Formula* letFormula);
  void generateUpdatePredicates();
  static int arrayIsUpdatedOnPath(Path* path,Variable *v);
  TermList arrayUpdatePosition(Path::Iterator &sit, TermList updPosExp, int posCnt, int currentCnt);
  Formula* updatePredicateOfArray2(Path* path, Path::Iterator &sit, Variable* v);
  Formula* updatePredicateOfArray3(Path* path, Path::Iterator &sit, Variable* v);
  Formula* arrayUpdateCondition(Path* path, Path::Iterator &sit, int posCnt);
  Formula* updPredicateStack(Stack<Formula*> &updStack);
  TermList arrayUpdateValue(Path::Iterator &sit, TermList exp, int posCnt, int currentCnt);
  Formula* lastUpdateProperty(Literal* updPred, string array, TermList position, TermList updValue);
  Formula* stabilityProperty(Literal* updPred, string array, TermList position, TermList iteration);
  void generateValueFunctionRelationsOfVariables();
  void generateLoopConditionProperty();
  void generateIterationDefinition();

  unsigned getIntFunction(string name, unsigned arity);
  unsigned getIntConstant(string name) { return getIntFunction(name, 0); }
  Literal* createIntEquality(bool polarity, TermList arg1, TermList arg2)
  { return Literal::createEquality(polarity, arg1, arg2, Sorts::SRT_INTEGER); }

  /** the loop being analyzed */
  WhileDo* _loop;
  /** all variables updated by this loop */
  Set<Variable*> _updatedVariables;
  /** All paths in the loop */
  Stack<Path*> _paths;
  /** all generated units */
  List<Unit*>* _units;

  
}; // class Analyze

}

#endif // __ProgramVariable__

/**
 * @file LoopAnalyzer.hpp
 * Defines class Program::LoopAnalyzer for loop analysis
 *
 * @since 23/08/2010, Torrevieja
 */

#ifndef __ProgramLoopAnalyzer__
#define __ProgramLoopAnalyzer__

#include "Lib/Set.hpp"
#include "Lib/List.hpp"
#include "Lib/VString.hpp"

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
  void runSEI();
  List<Unit* >* getUnits() {return _units;}
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
  Formula* getBranchCondition(Variable* v);
  Formula* getGeneralUpdateCondition(Path* path, Path::Iterator& pite, int conditionNumber);
  void generateCounterAxiom(const vstring& name,int min,int max,int gcd, Formula* branch);
  void generateLetExpressions();
  TermList expressionToTerm(Expression* exp, bool magic=false);
  Formula*  expressionToPred(Expression* exp,bool magic=false);
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
  Formula* lastUpdateProperty(Literal* updPred, vstring array, TermList position, TermList updValue);
  Formula* stabilityProperty(Literal* updPred, vstring array, TermList position, TermList iteration);
  void generateValueFunctionRelationsOfVariables();//TermList n);
  void generateLoopConditionProperty();
  void generateIterationDefinition();//TermList n);
  Formula* relativePathCondition(Formula* condition);

  unsigned getIntFunction(vstring name, unsigned arity, bool setColor=false);
  unsigned getIntConstant(vstring name);
  unsigned getIntPredicate(vstring name, unsigned arity, bool setColor);
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
  Term* _n;

  
}; // class Analyze

}

#endif // __ProgramVariable__

/**
 * @file LambdaElimination.hpp
 * Defines class LambdaElimination.
 */

#ifndef __LambdaElimination__
#define __LambdaElimination__

#include "Lib/Deque.hpp"
#include "Forwards.hpp"
#include "Kernel/HOSortHelper.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * A class with function @b elimLambda() that eliminates a lambda expressions
 * It does this by applying the well known rewrite rules for SKIBC combinators.
 *
 * These can be found:
 * https://en.wikipedia.org/wiki/Combinatory_logic
 */
class LambdaElimination {
public:


  LambdaElimination() : {};
  LambdaElimination(DHMap<unsigned,unsigned> varSorts) : _varSorts(varSorts){};
  TermList elimLambda(Term* lambdaTerm);
  TermList processBeyondLambda(Term* term);

  /** Iterates through sorts in problem and heuristically adds
    * a set of relevant combinators to the problem along with their defining
    * equations.
    */    
  //void addFunctionExtensionalityAxioms(UnitList*& units);
  //void addBooleanExtensionalityAxiom(UnitList*& units);
  
  static TermList createAppTerm(TermList sort, TermList arg1, TermList arg2);
  static TermList createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2);


  static FormulaUnit* addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned qvarSort);
  static FormulaUnit* addNotConnAxiom(TermList constant, unsigned notsort);
  static FormulaUnit* addBinaryConnAxiom(TermList constant, unsigned connSort, Connective conn, unsigned appedOnce);
  static FormulaUnit* addEqualityAxiom(TermList equals, unsigned argsSort, unsigned eqaulsSorts);
  static Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  static Formula* toEquality(TermList booleanTerm);
  static TermList addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant constant);
  
private:
 
  typedef HOSortHelper HSH;

  //keeps track of number of combinators added
  unsigned _combinatorsAdded;
  //maximum number of combinators that can be added
  unsigned _maxCombinatorsToBeAdded;
  
  unsigned countBasicSorts(Sorts::FunctionSort* fsort);
  bool eligible(unsigned sort);
  
  /*********************************************
  * Lambda and application elimination functions
  *********************************************/
    
  unsigned sortOf(TermList t);

  
  void addToProcessed(TermList ts, 	Stack<unsigned> &_argNums);
  /** Add a new definitions to _defs */
  void addAxiom(FormulaUnit* axiom, bool extensionalityAxiom = false);
  void addCombinatorAxiom(TermList combinator, unsigned combinatorSort, unsigned argSort,
                          Signature::Symbol::HOLConstant comb, int arg1Sort = -1, int arg2Sort = -1);
  // Introduces a fresh predicate or function (depending on the context) symbol
  // with given arguments and result sort

  void dealWithApp(TermList lhs, TermList rhs, unsigned sort, int lambdaVar, Stack<TermList> &_toBeProcessed, Stack<unsigned> &_argNums);
  
  TermList addKComb(unsigned appliedToArg, TermList arg);
  TermList addComb(unsigned appliedToArgs, TermList arg1, TermList arg2, Signature::Symbol::HOLConstant comb);
  
  void process(Stack<int> &vars, TermStack &sorts, TermStack &toBeProcessed);
  
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;
  //Stack<int> _vars;
  //Stack<unsigned> _sorts;
  //Stack<unsigned> _argNums;
  //Stack<TermList> _toBeProcessed;
  Stack<TermList> _processed;
  Stack<Signature::Symbol::HOLConstant> _combinators;
  Stack<unsigned> _combSorts;
  
  TermList _processing; 

};

#endif // __LambdaElimination__
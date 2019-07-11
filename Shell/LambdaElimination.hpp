/**
 * @file LambdaElimination.hpp
 * Defines class LambdaElimination.
 */

#ifndef __LambdaElimination__
#define __LambdaElimination__

#include "Lib/Deque.hpp"
#include "Forwards.hpp"

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


  LambdaElimination() {};
  LambdaElimination(DHMap<unsigned,TermList> varSorts) : _varSorts(varSorts){};
  TermList elimLambda(Term* lambdaTerm);
  TermList processBeyondLambda(Term*);
  TermList processBeyondLambda(Formula*);
  TermList processBeyondLambda(TermList);


  /** Iterates through sorts in problem and heuristically adds
    * a set of relevant combinators to the problem along with their defining
    * equations.
    */    
  //void addFunctionExtensionalityAxioms(UnitList*& units);
  //void addBooleanExtensionalityAxiom(UnitList*& units);
  
  static TermList createAppTerm(TermList sort, TermList arg1, TermList arg2);
  static TermList createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2);
  static TermList createAppTerm3(TermList sort, TermList arg1, TermList arg2, TermList arg3);
  static TermList createAppTerm(TermList sort, TermList arg1, TermList arg2, TermList arg3, TermList arg4); 
  static TermList getNthArg(TermList arrowSort, unsigned argNum);
  static TermList getResultApplieadToNArgs(TermList arrowSort, unsigned argNum);
  static void addCombinatorAxioms(Problem& prb);

  /*static FormulaUnit* addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned qvarSort);
  static FormulaUnit* addNotConnAxiom(TermList constant, unsigned notsort);
  static FormulaUnit* addBinaryConnAxiom(TermList constant, unsigned connSort, Connective conn, unsigned appedOnce);
  static FormulaUnit* addEqualityAxiom(TermList equals, unsigned argsSort, unsigned eqaulsSorts);
  static Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  static Formula* toEquality(TermList booleanTerm);
  static TermList addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant constant);*/
  
private:
  
  /*********************************************
  * Lambda and application elimination functions
  *********************************************/
    
  TermList sortOf(TermList t);

  void addToProcessed(TermList ts, Stack<unsigned> &_argNums);
  void dealWithApp(TermList lhs, TermList rhs, int lambdaVar, TermStack &toBeProcessed, Stack<unsigned> &argNums);

  TermList createKTerm(TermList s1, TermList s2, TermList arg1);
  TermList createSCorBTerm(TermList arg1, TermList arg2, Signature::Combinator comb);
  
  void process(Stack<int> &vars, TermStack &sorts, TermStack &toBeProcessed);
  
  /** Lexical scope of the current unit */
  DHMap<unsigned,TermList> _varSorts;
  TermStack _processed;
  Stack<Signature::Combinator> _combinators;
};

#endif // __LambdaElimination__
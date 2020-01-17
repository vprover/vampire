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
  
  //void addFunctionExtensionalityAxioms(UnitList*& units);
  //void addBooleanExtensionalityAxiom(UnitList*& units);
  
  static void addCombinatorAxioms(Problem& prb);
  static void addProxyAxioms(Problem& prb);
  static void addFunctionExtensionalityAxiom(Problem& prb);
  static void addChoiceAxiom(Problem& prb);
  static Literal* toEquality(TermList booleanTerm, bool polarity);
  
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
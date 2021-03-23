/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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
//  LambdaElimination(DHMap<unsigned,TermList> varSorts) : _varSorts(varSorts){};

  /** Set of recursive functions that rconvert lambda terms to 
   *  combinatory terms and replace logical symbols by proxies.
   *  It can be used as an alternative to FOOLElimination
   */
  TermList elimLambda(Term* lambdaTerm);
  TermList elimLambda(TermList term);
  TermList elimLambda(Stack<int>& vars, TermStack& sorts, TermList body, TermList sort);
  TermList elimLambda(int var, TermList varSort, TermList body, TermList sort);
  TermList elimLambda(Formula*);
  
  //void addFunctionExtensionalityAxioms(UnitList*& units);
  //void addBooleanExtensionalityAxiom(UnitList*& units);
  
  static void addCombinatorAxioms(Problem& prb);
  static void addProxyAxioms(Problem& prb);
  static void addFunctionExtensionalityAxiom(Problem& prb);
  static void addChoiceAxiom(Problem& prb);
  static Literal* toEquality(TermList booleanTerm, bool polarity);
  
  class TermListComparator {
  public:
    bool lessThan(TermList t1, TermList t2);
  };

private:

  /*********************************************
  * Lambda and application elimination functions
  *********************************************/
    
  TermList sortOf(TermList t);

  void addToProcessed(TermList ts, TermList sort, Stack<unsigned> &_argNums);
  void dealWithApp(Term* app, const unsigned lambdaVar, 
    TermStack &toBeProcessed, TermStack &sorts, Stack<unsigned> &argNums);

  TermList createKTerm(TermList s1, TermList s2, TermList arg1);
  TermList createSCorBTerm(TermList arg1, TermList arg1sort, 
        TermList arg2, TermList arg2sort, Signature::Combinator comb);
  
  void process(Stack<int> &vars, TermStack &varSorts, 
               TermStack &toBeProcessed, TermStack &sorts);
  
  /** Lexical scope of the current unit */
  TermStack _processed;
  TermStack _processedSorts;
  Stack<Signature::Combinator> _combinators;
};

#endif // __LambdaElimination__


/*
 * File TheoryInstAndSimp.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TheoryInstAndSimp.hpp
 * Defines class TheoryInstAndSimp
 *
 */

#ifndef __TheoryInstAndSimp__
#define __TheoryInstAndSimp__

#if VZ3

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Substitution.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

struct Solution{
  Solution(bool s) : status(s) {}
  const bool status;
  Substitution subst;
};


class TheoryInstAndSimp
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(TheoryInstAndSimp);
  USE_ALLOCATOR(TheoryInstAndSimp);

  TheoryInstAndSimp() : _splitter(0) {}
  void attach(SaturationAlgorithm* salg);

  ClauseIterator generateClauses(Clause* premise, bool& premiseRedundant);
  ClauseIterator generateClauses(Clause* premise){
    bool r;
    return generateClauses(premise,r);
  }

  /** Find a set of instantiations that make theoryLiterals unsatisfiable. maxVar is the highest variable
      occuring in the clause that contains theoryLiterals. If guarded is set, add constraints that exclude
      division by zero. If minimize is set, try to remove unneccesary components of the substitution.
   */
  VirtualIterator<Solution> getSolutions(Stack<Literal*>& theoryLiterals, unsigned maxVar, bool minimize, bool guarded);

private:

  void selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits);

  void originalSelectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3);

  void applyFilters(Stack<Literal*>& theoryLits, bool forZ3);
  void filterDivisionByZero(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits);
  void filterDivisionByZeroDeep(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits);

  /* Take a theory (sub)clause, the skolemization grounding and a solution that makes the clause unsat.
     Return a new solution that is at least as general as the input solution which still makes theoryLiterals unsat.
  */
  VirtualIterator<Solution>  minimizeSolution(Stack<Literal*>& theoryLiterals, bool guarded,
                                              Solution sol,
                                              Stack<Literal*>& triangleSubst,
                                              unsigned maxVar
                                              );
  
  /** Fills trivialLits with all clauses trivial in cl
   */
  void selectTrivialLiterals(Clause* cl, Stack<Literal*>& trivialLits);
  bool isPure(Literal* lit);

  /**
   Checks if left = right is of the form X = t where X does not occur in t.
   */
  static inline bool isXeqTerm(const TermList* left,const TermList* right);

  unsigned varOfXeqTerm(const Literal* lit,bool flip=false);

  /**
     Checks if models for sort can be mapped back to terms.
  */
  bool isSupportedSort(const unsigned sort);

  /**
     Checks if literal can be mapped back to terms. Works around
     Theory::interpretPredicate not reporting interpreted equality.
   */
  bool isSupportedLiteral(Literal* lit);


  /** Checks if literal lit contains the variable v
   */
  bool literalContainsVar(const Literal* lit, unsigned v);

  Splitter* _splitter;
  //SAT2F0 _naming;
  //Z3Interfacing* _solver;

};

};

#endif

#endif /*__TheoryInstAndSimp__*/

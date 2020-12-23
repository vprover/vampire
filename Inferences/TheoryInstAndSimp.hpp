
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
#include "Shell/Options.hpp"
#include "SAT/Z3Interfacing.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

struct Solution{
  explicit Solution(bool s) : status(s) {}
  const bool status;
  Substitution subst;
  friend std::ostream& operator<<(std::ostream& out, Solution const&);
};


class TheoryInstAndSimp
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(TheoryInstAndSimp);
  USE_ALLOCATOR(TheoryInstAndSimp);

  ~TheoryInstAndSimp();
  TheoryInstAndSimp() : TheoryInstAndSimp(*env.options) {}
  TheoryInstAndSimp(Options& opts) : TheoryInstAndSimp(opts.theoryInstAndSimp(), opts.showZ3(), opts.z3UnsatCores()) {}
  TheoryInstAndSimp(Options::TheoryInstSimp mode, bool showZ3, bool unsatCoreForRefutations) 
    : _splitter(0)
    , _mode(mode)
    , _naming()
    , _solver([&](){ 
        BYPASSING_ALLOCATOR; 
        return new Z3Interfacing(_naming, showZ3, unsatCoreForRefutations,  /* unsatCoresForAssumptions = */ false); 
      }())
  {}

  void attach(SaturationAlgorithm* salg);

  ClauseGenerationResult generateSimplify(Clause* premise);
  VirtualIterator<Solution> getSolutions(Stack<Literal*>& theoryLiterals, bool guarded, bool& addedGuards);

  VirtualIterator<Solution> getSolutionsWithGuards(Stack<Literal*>& theoryLiterals, bool& addedGuards) 
  { return getSolutions(theoryLiterals, true, addedGuards); }

  VirtualIterator<Solution> getSolutionsWithoutGuards(Stack<Literal*>& theoryLiterals)
  { bool _; return getSolutions(theoryLiterals, false, _); }

private:

  void selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits);

  void originalSelectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3);

  void applyFilters(Stack<Literal*>& theoryLits, bool forZ3);
  void filterUninterpretedPartialFunctionDeep(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits);
  
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
  Options::TheoryInstSimp _mode;
  SAT2FO _naming;
  Z3Interfacing* _solver;

};

};

#endif

#endif /*__TheoryInstAndSimp__*/

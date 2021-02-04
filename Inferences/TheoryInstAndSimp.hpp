
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
  explicit Solution(Substitution subst) : sat(true), subst(std::move(subst)) {}
  static Solution unsat() { return Solution(); }
  const bool sat;
  Substitution subst;
  friend std::ostream& operator<<(std::ostream& out, Solution const&);
private:
  Solution() : sat(false) {}
};


class TheoryInstAndSimp
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(TheoryInstAndSimp);
  USE_ALLOCATOR(TheoryInstAndSimp);

  ~TheoryInstAndSimp();
  TheoryInstAndSimp() : TheoryInstAndSimp(*env.options) {}

  TheoryInstAndSimp(Options& opts);
  TheoryInstAndSimp(Options::TheoryInstSimp mode, bool thiTautologyDeletion, bool showZ3, bool generalisation);

  void attach(SaturationAlgorithm* salg);

  ClauseGenerationResult generateSimplify(Clause* premise);

  VirtualIterator<Solution> getSolutions(Stack<Literal*> const& theoryLiterals, Stack<Literal*> const& guards);
private:
  Option<Substitution> instantiateWithModel(Stack<unsigned> const& vars, Substitution skolemSubst);
  Option<Substitution> instantiateGeneralisied(Stack<unsigned> const& vars, 
    Substitution skolemSubst, 
    Stack<SATLiteral> theoryLits);

  Stack<Literal*> selectTheoryLiterals(Clause* cl);

  void originalSelectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3);

  Stack<Literal*> applyFilters(Stack<Literal*> theoryLits);
  void filterUninterpretedPartialFunctionDeep(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits);
  
  /** returns the set of literals trivial in cl */
  Stack<Literal*> selectTrivialLiterals(Clause* cl );
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
  bool calcIsSupportedSort(const unsigned sort);
  bool isSupportedFunction(Term* trm);
  bool isSupportedFunction(Theory::Interpretation trm);

  /**
     Checks if literal can be mapped back to terms. Works around
     Theory::interpretPredicate not reporting interpreted equality.
   */
  bool isSupportedLiteral(Literal* lit);


  /** Checks if literal lit contains the variable v
   */
  bool literalContainsVar(const Literal* lit, unsigned v);

  class GeneralisationTree;
  class ConstantCache 
  {
    class SortedConstantCache {
      unsigned _used;
      Stack<Term*> _constants;
    public:
      SortedConstantCache() : _used(0), _constants() {}
      void reset();
      Term* freshConstant(const char* prefix, unsigned sort);
    };

    const char* _prefix;
    Stack<SortedConstantCache> _inner;

  public:
    ConstantCache(const char* prefix) : _prefix(prefix), _inner() {}

    void reset();

    Term* freshConstant(unsigned sort) ;
  };

  Splitter* _splitter;
  Options::TheoryInstSimp const _mode;
  bool const _thiTautologyDeletion;
  SAT2FO _naming;
  Z3Interfacing* _solver;
  Map<unsigned, bool> _supportedSorts;
  bool _generalisation;
  ConstantCache _instantiationConstants;
  ConstantCache _generalizationConstants;
};

};

#endif

#endif /*__TheoryInstAndSimp__*/

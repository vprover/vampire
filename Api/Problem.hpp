/**
 * @file Problem.hpp
 * Defines class Problem.
 */

#ifndef __Problem__
#define __Problem__

#include "FormulaBuilder.hpp"

namespace Api {

class Problem;

class AnnotatedFormulaIterator
{
public:
  bool hasNext();
  /**
   * Return the next @b AnnotatedFormula object
   *
   * Each call to the @b next function must be preceded by a call to
   * the @b hasNext function (which has returned @b true).
   */
  AnnotatedFormula next();

  /** delete the last returned formula from the problem */
  void del();
private:
  bool ready;
  void* idata;

  friend class Problem;
};

/**
 * Container of a list of annotated formulas
 *
 * The object acts as a reference counted pointer to a mutable list of formulas.
 * To obtain a true copy of the object, one should call the @b clone function.
 */
class Problem
{
public:
  Problem();
  Problem(const Problem& p);
  Problem& operator=(const Problem&);
  ~Problem();

  enum InliningMode {
    INL_OFF = 0,
    INL_ON = 1,
    INL_AXIOMS_ONLY = 2
  };

  /**
   * Return a copy of the problem
   *
   * The copy constructor and operator= do not create a copy of the
   * problem, they give a pointer pointing to the same memory location.
   * To obtain a copy, this function must be used.
   */
  Problem clone();

  void addFormula(AnnotatedFormula f);

  /**
   * Add formulas parsed from a stream
   *
   * @param s the tsream
   * @param includeDirectory where the parser will look for included files
   * @param simplifySyntax Simplify syntax will be used instead of the TPTP syntax.
   */
  void addFromStream(istream& s, string includeDirectory="./", bool simplifySyntax=false);

  /**
   * Return the current problem clausified
   *
   * @param namingThreshold When the number of clauses generated from one formula
   *   exceeds this number, we attempt to introduce names to lower the amount of
   *   generated clauses. If the value is 0, naming is disabled.
   * @param preserveEpr If true, names will not be introduced if it would
   *   lead to introduction of non-constant Skolem functions.
   */
  Problem clausify(int namingThreshold=8, bool preserveEpr=false, InliningMode predicateDefinitionInlining=INL_OFF,
      bool unusedPredicateDefinitionRemoval=true);

  /**
   * Return the current problem skolemized
   *
   * @param namingThreshold When the number of NNF formulas generated from one formula
   *   exceeds this number, we attempt to introduce names to lower the amount of
   *   generated formulas. If the value is 0, naming is disabled.
   * @param preserveEpr If true, names will not be introduced if it would
   *   lead to introduction of non-constant Skolem functions.
   */
  Problem skolemize(int namingThreshold=8, bool preserveEpr=false, InliningMode predicateDefinitionInlining=INL_OFF,
      bool unusedPredicateDefinitionRemoval=true);

  /**
   * Perform predicate definition inlining and return the resulting problem.
   *
   * @c mode cannot be @c INL_OFF.
   */
  Problem inlinePredicateDefinitions(InliningMode mode=INL_ON);

  /**
   * Perform removal of pure predicates and unused predicate definitions.
   */
  Problem removeUnusedPredicateDefinitions();

  /**
   * Return iterator of formulas in the problem
   *
   * When the problem is modified, behavior of all existing iterators
   * (except for the one that caused the modification) is undefined.
   */
  AnnotatedFormulaIterator formulas();

  /**
   * Return number of formulas in this problem
   */
  size_t size();
private:
  class PData;
  class ProblemTransformer;

  class Preprocessor1;
  class PredicateDefinitionInliner;
  class UnusedPredicateDefinitionRemover;
  class Clausifier;

  PData* _data;
};

}

#endif // __Problem__

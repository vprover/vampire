/**
 * @file Problem.hpp
 * Defines class Problem.
 */

#ifndef __API_Problem__
#define __API_Problem__

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
    /** Inline all predicate defnitions */
    INL_ON = 1,
    INL_AXIOMS_ONLY = 2,
    /**
     * Performs only the inlining that is necessary to avoid introducing non-constant
     * skolem functions (if possible).
     * This inlining needs to be followed by the unused predicate definition removal
     * to achieve the desired effect.
     */
    INL_EPR_RESTORING = 3,
    /**
     * Inline only symetric equivalences between two predicates.
     */
    INL_PREDICATE_EQUIVALENCES_ONLY = 4,
    /**
     * This options disables scanning of the problem for definitions.
     * The definitions need to be supplied by other means. This mode
     * makes sense only for certaing APIs that perform definition inlining.
     */
    INL_NO_DISCOVERED_DEFS = 5,
    /**
     * Inlines only definitions that do not increase the size of the problem
     */
    INL_NON_GROWING = 6
  };

  enum PreprocessingMode {
    /**
     * This mode performs only Sine axiom selection (if it is enabled)
     */
    PM_SELECTION_ONLY,
    /**
     * This mode performs only axiom selection and predicate definition elimination rules (if they are enabled)
     */
    PM_EARLY_PREPROCESSING,
    PM_SKOLEMIZE,
    PM_CLAUSIFY
  };

  /**
   * Options for the @c preprocess() function.
   */
  struct PreprocessingOptions
  {
    PreprocessingOptions(
	PreprocessingMode mode=PM_CLAUSIFY,
	int namingThreshold=8,
	bool preserveEpr=false,
	InliningMode predicateDefinitionInlining=INL_OFF,
	bool unusedPredicateDefinitionRemoval=true,
	bool showNonConstantSkolemFunctionTrace=false,
	bool traceInlining=false,
	bool sineSelection=false,
	float sineTolerance=1.0f,
	unsigned sineDepthLimit=0,
	bool variableEqualityPropagation=false,
	bool traceVariableEqualityPropagation=false,
	bool eprSkolemization=false,
	bool traceEPRSkolemization=false,
	bool predicateDefinitionMerging=false,
	bool tracePredicateDefinitionMerging=false,
	bool traceClausification=false,
	bool traceUnusedPredicateDefinitionRemoval=false);

    PreprocessingMode mode;
    /**
     * When the number of clauses generated from one formula
     * exceeds this number, we attempt to introduce names to lower the amount of
     * generated clauses. If the value is 0, naming is disabled.
     */
    int namingThreshold;
    /**
     * If true, names will not be introduced if it would
     * lead to introduction of non-constant Skolem functions.
     */
    bool preserveEpr;
    InliningMode predicateDefinitionInlining;
    bool unusedPredicateDefinitionRemoval;
    bool showNonConstantSkolemFunctionTrace;
    /**
     * If true, details on every definition inlining step will be output
     * to the standard error output.
     */
    bool traceInlining;
    bool sineSelection;
    /**
     * Sine tolerance parameter.
     *
     * Must be greater than or equal to 1. More axioms are selected for
     * greater numbers.
     *
     * Value has effect only when @c sineSelection is true.
     */
    float sineTolerance;
    /**
     * Maximal number of iterations of the Sine axiom selection algorithm.
     *
     * Zero means unlimited. The more iterations can be performed, the more
     * axioms are selected.
     *
     * Value has effect only when @c sineSelection is true.
     */
    unsigned sineDepthLimit;
    /**
     * Propagate variable equalities in formulas, for example
     * X=Y => X=f(Y) ---> X=f(X)
     *
     * Only equalities with a variable on one side and variable or constant
     * on the other side are propagated. This is to avoid possible exponential
     * growth in the size of terms.
     *
     * We propagate positive equalities in conjunctions (e.g. X=Y & p(X,Y) ---> p(X,X))
     * and negative in disjunctions (e.g. X!=Y | p(X,Y) ---> p(X,X)).
     * Implication F=>G is treated as disjunction ~F | G.
     *
     * In certain cases we propagate the equality, but do not remove it.
     * For example ![X]: ?[Y]: (X!=Y | p(X,Y)) ---> ![X]: ?[Y]: (X!=Y | p(X,X))
     * This formula is true in any model of size at least two, while ![X]: p(X,X) is not.
     */
    bool variableEqualityPropagation;
    bool traceVariableEqualityPropagation;

    /**
     * Where possible, perform EPR preserving skolemization of predicate
     * definitions whose clausification would otherwise violate the EPR
     * property.
     */
    bool eprSkolemization;
    bool traceEPRSkolemization;

    /**
     * Merge predicate definitions that have equivalent body
     * (the equivalency check is incomplete)
     */
    bool predicateDefinitionMerging;
    bool tracePredicateDefinitionMerging;

    /**
     * Output information on what formulas are being clausified, and what
     * clauses were generated.
     *
     * The output is directed to standard error output.
     */
    bool traceClausification;

    /**
     * Output information on th progress of unused predicate definition
     * removal and pure predicate removal.
     *
     * The output is directed to standard error output.
     */
    bool traceUnusedPredicateDefinitionRemoval;

    /**
     * Add asymmetric rewriting rule to be used during preprocessing.
     *
     * For details on the requirements see documentation to the
     * @c Problem::performAsymetricRewriting() function.
     */
    void addAsymmetricRewritingRule(Formula lhs, Formula posRhs, Formula negRhs, Formula dblRhs=Formula());

    /**
     * Mark a predicate as built-in.
     *
     * This means that the predicate will not be emilinated by the unused
     * predicate definition removal rule (which, among other, removes predicates
     * occurring with only one polarity).
     */
    void addBuiltInPredicate(Predicate pred);
  private:
    friend class Problem;
    void validate() const;

    struct OptDataStore {
      OptDataStore();
      OptDataStore(const OptDataStore& o);
      OptDataStore& operator=(const OptDataStore& o);
      ~OptDataStore();

      //pointers in order to avoid dependency on the Stack class definition here
      Stack<Formula>* lhs;
      Stack<Formula>* posRhs;
      Stack<Formula>* negRhs;
      Stack<Formula>* dblRhs;

      Stack<unsigned>* builtInPreds;
    };

    OptDataStore _ods;
  };

  /**
   * Return a copy of the problem
   *
   * The copy constructor and operator= do not create a copy of the
   * problem, they give a pointer pointing to the same memory location.
   * To obtain a copy, this function must be used.
   */
  Problem clone();

  /**
   * Add formula into the problem
   *
   * @warning Problem can contain only formulas coming from one FormulaBuilder object.
   */
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
   * Preprocess the problem according to @c options.
   */
  Problem preprocess(const PreprocessingOptions& options);

  /**
   * Rewrite occurrences of @c lhs in the problem by posRhs, negRhs or dblRhs,
   * based on the polarity. dblRhs is used inside equivalences or XOR expressions.
   * If null formula is passed for some case, rewriting is not performed in
   * that case.
   * lhs must be a literal or a negation of a literal.
   */
  Problem performAsymetricRewriting(Formula lhs, Formula posRhs, Formula negRhs, Formula dblRhs=Formula());

  /**
   * For all @c lhs, @c posRhs, @c negRhs and @c dblRhs in the correspondingly
   * named array arguments, rewrite occurrences of @c lhs in the problem by posRhs,
   * negRhs or dblRhs, based on the polarity. dblRhs is used inside equivalences or
   * XOR expressions.
   * If null formula is passed for some case, rewriting is not performed in
   * that case.
   *
   * All the *Array arguments must be arrays of length @c cnt.
   * Formulas in the lhsArray must be literals or negations of literals that
   * contain distinct variables as top level arguments.
   * Predicates in the lhsArray must not appear in any formula in any *RhsArray.
   * (These conditions might not be currently enforced by the Api, but the behavior
   * is undefined in those cases.)
   */
  Problem performAsymetricRewriting(size_t cnt, Formula* lhsArray, Formula* posRhsArray, Formula* negRhsArray,
      Formula* dblRhsArray);

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

  /**
   * Output tff type definitions for non-standard types and for all
   * functions and predicates, whose type contains some non-default sort.
   */
  void outputTypeDefinitions(ostream& out, bool outputAllTypeDefs=false);

  /**
   * Output the problem in TPTP format.
   * If @c outputTypeDefs is true, type definitions will be output
   * using he @c outputTypeDefinitions() function.
   */
  void output(ostream& out, bool outputTypeDefs=false, bool outputAllTypeDefs=false);

  /**
   * Output various statistics
   *
   * Currently the statictics are gobal and cummulative. If two preprocessing runs
   * are performed, the numbers in the statistics will be sums of the numbers
   * generated by the two runs.
   */
  void outputStatistics(ostream& out);
private:
  class PData;
  class ProblemTransformer;

  class Preprocessor1;
  class VariableEqualityPropagator;
  class PredicateDefinitionMerger;
  class PredicateDefinitionInliner;
  class EPRRestoringInliner;
  class ConstantSkolemizer;
  class EPRSkolemizer;
  class UnusedPredicateDefinitionRemover;
  class Clausifier;
  class SineSelector;

  PData* _data;
};

}

#endif // __API_Problem__

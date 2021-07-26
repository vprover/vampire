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
 * @file Api/Problem.hpp
 * Defines class Problem.
 */

#ifndef __API_Problem__
#define __API_Problem__

#include "FormulaBuilder.hpp"
#include "Lib/VString.hpp"
#include "Lib/Allocator.hpp"

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

  enum EquivalenceDiscovery {
    ED_NONE,
    /**
     * Attempts to discover equivalences in the shape
     * p(X1,...,XN) <=> q(Y1,...,YN)
     * where X1,...,XN are distinct variables and a permutation of Y1,...,YN.
     *
     * This is the fastest option as it restricts the set of candidates the most.
     */
    ED_PREDICATE_EQUIVALENCES,
    /**
     * Attempts to discover equivalences in the shape
     * p(X1,...,XN) <=> q(t1,...,tM)
     * where X1,...,XN are distinct variables and t1,...,tM terms which contain
     * only variables X1,...,XN.
     *
     * All results of this discovery can be inlined (unless several definitions
     * of one predicate are discovered).
     */
    ED_PREDICATE_DEFINITIONS,
    /**
     * Attempts to discover equivalences between any two atoms.
     */
    ED_ATOM_EQUIVALENCES,
    /**
     * Attempts to discover equivalences between any two formulas.
     */
    ED_FORMULA_EQUIVALENCES
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
   * If there are multiple runs for the preprocessing segment, the runs may
   * be made to terminate early by setting one of these checks.
   */
  enum FixpointCheck {
    FC_NONE,
    /**
     * Will terminate if the formula count does not decrease
     */
    FC_FORMULA_COUNT
  };

  /**
   * Options for the @c preprocess() function.
   */
  struct PreprocessingOptions
  {
    CLASS_NAME(Problem::PreprocessingOptions);
    USE_ALLOCATOR_ARRAY;    
    
    PreprocessingOptions();
    /**
     * Read options from a string.
     */
    explicit PreprocessingOptions(Lib::vstring spec);

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
    bool sineSelection;
    /**
     * Sine tolerance parameter.
     *
     * Must be greater than or equal to 1 or equal to -1. More axioms are selected for
     * greater numbers. -1 means unlimited tolerance.
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

    /**
     * Where possible, perform EPR preserving skolemization of predicate
     * definitions whose clausification would otherwise violate the EPR
     * property.
     */
    bool eprSkolemization;

    /**
     * Merge predicate definitions that have equivalent body
     * (the equivalency check is incomplete)
     */
    bool predicateDefinitionMerging;

    /**
     * If all atoms of a certain predicate contain distinct constants as
     * a particular argument, atoms of the predicate are replaces by set
     * of fresh predicates, one for each of the distinct constants.
     *
     * E.g. a problem
     * p(a,b,X,1)
     * p(a,c,a,2)
     * will be transformed into
     * p_a_1(b,X)
     * p_a_2(c,a)
     * (second argument is not removed because constants b and c are not
     * necessarily distinct, and third argment is not replaced because it
     * occurs as a variable)
     *
     * Default value is false.
     */
    bool predicateIndexIntroduction;

    /**
     * split formulas with top-level (up to universal quantification)
     * conjunctions into several formulas
     *
     * Default value is false.
     */
    bool flatteningTopLevelConjunctions;

    /**
     * Use SAT solver to attempt to discover equivalences, see documentation of
     * @c EquivalenceDiscovery for description of possible values.
     *
     * Default value is ED_NONE which does not do any discovery.
     */
    EquivalenceDiscovery equivalenceDiscovery;
    /**
     * If true, premises will be retrieved for discovered equivalences. This may take
     * some time for big problems.
     *
     * Default value is true.
     */
    bool equivalenceDiscoveryRetrievePremises;
    /**
     * Limit on the number of SAT conflicts in each equivalence check.
     * Default is UINT_MAX which stands for unlimited, 0 will restrict equivalence
     * discovery to unit propagation.
     *
     * Implementation:
     * The implicative sat sweeping has an internal conflict count limit which always
     * starts with zero and is increased geometrically until it reaches the limit set
     * by this value.
     */
    unsigned equivalenceDiscoverySatConflictLimit;

    /**
     * If true, the predicate equivalence will add also implications.
     *
     * Default value is false.
     */
    bool equivalenceDiscoveryAddImplications;

    /**
     * If true, the predicate equivalence will first do several loops of random
     * simulation to restrict the space of candidate equivalences.
     *
     * Default value is true.
     */
    bool equivalenceDiscoveryRandomSimulation;

    /**
     * Full inlining using AIG with BDD-sweeping simplifications
     */
    bool aigInlining;

    /**
     * BDD-sweeping simplification of AIG representation of the problem
     */
    bool aigBddSweeping;

    /**
     * Maximal number of atoms for which BDDs are built during the sweeping process
     *
     * Default value is 16, which gives upper bound on the BDD size in the order of 2^16.
     */
    unsigned aigBddSweepingMaximumBddAtomCount;

    /**
     * BDD-sweeping simplification of AIG representation of the problem
     */
    bool aigDefinitionIntroduction;

    /**
     * Conditional rewriting on the AIG of the problem
     */
    bool aigConditionalRewriting;

    /**
     * How many times we will iterate this preprocessing strategy
     *
     * Default value is 1, 0 means unlimited.
     */
    unsigned repetitionCount;
    /**
     * Check that can gove early termination of the repetitions
     *
     * Default value is FC_NONE, if repetitionCount==1, the option has no effect.
     */
    FixpointCheck repetitionEarlyTermination;


    /**
     * Add asymmetric rewriting rule to be used during preprocessing.
     *
     * For details on the requirements see documentation to the
     * @c Problem::performAsymetricRewriting() function.
     */
    void addAsymmetricRewritingRule(Formula lhs, Formula posRhs, Formula negRhs, Formula dblRhs=Formula());

    /**
     * Takes assymmetric rules from @c src.
     */
    void importAssymmetricRulesFrom(const PreprocessingOptions& src);
    /**
     * Restrict equivalence discovery to equivalences between atoms from
     * set1 and set2
     *
     * Formulas in arrays set1 and set2 must be atoms.
     */
    void restrictPredicateEquivalenceDiscovery(size_t set1Sz, Formula* set1, size_t set2Sz, Formula* set2);

    /**
     * Print values of current option settings, marking options that have their default value
     */
    void printOptionValues(ostream& out);
  private:
    friend class Problem;
    void validate() const;

    // void prepareOptionsReader(OptionsReader& rdr);
    void setDefaults();

    struct Atom2LitFn;

    struct OptDataStore {
      OptDataStore();
      OptDataStore(const OptDataStore& o);
      OptDataStore& operator=(const OptDataStore& o);
      ~OptDataStore();

      void setDefaults();


      //pointers in order to avoid dependency on the Stack class definition here
      Stack<Formula>* lhs;
      Stack<Formula>* posRhs;
      Stack<Formula>* negRhs;
      Stack<Formula>* dblRhs;
      Stack<Kernel::Literal*>* pedSet1;
      Stack<Kernel::Literal*>* pedSet2;
    };

    bool _predicateEquivalenceDiscoveryRestricted;
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
  void addFromStream(istream& s, vstring includeDirectory="./", bool simplifySyntax=false);

  /**
   * Return the current problem clausified
   *
   * @param namingThreshold When the number of clauses generated from one formula
   *   exceeds this number, we attempt to introduce names to lower the amount of
   *   generated clauses. If the value is 0, naming is disabled.
   * @param preserveEpr If true, names will not be introduced if it would
   *   lead to introduction of non-constant Skolem functions.
   * @param predicateDefinitionInlining - use of predicate definition inlining
   * @param unusedPredicateDefinitionRemoval - use of unused predicate definition removal
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
   * @param predicateDefinitionInlining - use of predicate definition inlining
   * @param unusedPredicateDefinitionRemoval - use of unused predicate definition removal
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
   * Creates array of PreprocessingOptions specifying the stages to be performed.
   * It is caller's responsibility to call delete[] stageSpecs.
   *
   * Format of the string should be
   * &lt;stage1 spec&gt;[;&lt;stage2 spec&gt;[;&lt;stage3 spec&gt;[;...]]]
   * where &lt;stageX spec&gt; is
   * &lt;option1&gt;=&lt;value1&gt;[:&lt;option2&gt;=&lt;value2&gt;[:...]]
   */
  void readStageSpecs(Lib::vstring stagesStr, size_t& stageCnt, PreprocessingOptions*& stageSpecs);

  /**
   * Perform sequence of preprocessing according to array of options @c stageSpecs with
   * length stageCount. Preprocessing specified by stageSpecs[0] is performed as the first.
   *
   */
  Problem preprocessInStages(size_t stageCount, const PreprocessingOptions* stageSpecs);
  Problem preprocessInStages(Lib::vstring stagesStr);

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
   * Return true if problem contains no formulas
   */
  bool empty();

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

  Problem singlePreprocessingIteration(const PreprocessingOptions& options);
  bool fixpointReached(FixpointCheck fc, Problem& oldPrb, Problem& newPrb);

  class PData;
  class ProblemTransformer;

  class Preprocessor1;
  class TopLevelFlattener;
  class VariableEqualityPropagator;
  class BDDSweeper;
  class AIGInliner;
  class AIGDefinitionIntroducer;
  class AIGConditionalRewriter;
  class PredicateIndexIntroducer;
  class PredicateEquivalenceDiscoverer;
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

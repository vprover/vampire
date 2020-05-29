
/*
 * File Inference.hpp.
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
 * @file Inference.hpp
 * Defines class Inference for various kinds of inference
 *
 * @since 10/05/2007 Manchester
 */

#ifndef __Inference__
#define __Inference__

#include <cstdlib>

#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"
#include "Forwards.hpp"

#include <type_traits>

using namespace std;
using namespace Lib;

namespace Kernel {

/** Kind of input. The integers should not be changed, they are used in
 *  Compare. */
enum class UnitInputType : unsigned char {
  /** Axiom or derives from axioms */
  AXIOM = 0,
  /** Assumption or derives from axioms and assumptions */
  ASSUMPTION = 1,
  /** derives from the goal */
  CONJECTURE = 2,
  /** negated conjecture */
  NEGATED_CONJECTURE = 3,
  /** Vampire-only, for the consequence-finding mode */
  CLAIM = 4,
  /** Used in parsing and preprocessing for extensionality clause tagging, should not appear in proof search */
  EXTENSIONALITY_AXIOM = 5,
  /** Used to seperate model definitions in model_check mode, should not appear in proof search */
  MODEL_DEFINITION = 6
};

inline std::underlying_type<UnitInputType>::type toNumber(UnitInputType t) { return static_cast<std::underlying_type<UnitInputType>::type>(t); }

UnitInputType getInputType(UnitList* units);
UnitInputType getInputType(UnitInputType t1, UnitInputType t2);

/**
 * Tag to denote various kinds of inference rules.
 */
enum class InferenceRule : unsigned char {
  /** input formula or clause */
  INPUT,

  /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL
   * (preprocessing/normalisation) FORMULA TRANSFORMATION SHOULD BELONG
   * (see also INTERNAL_FORMULA_TRANSFORMATION_LAST and isFormulaTransformation below). */
  GENERIC_FORMULA_TRANSFORMATION,
  /** negated conjecture from the input */
  NEGATED_CONJECTURE,
  /** introduction of answer literal into the conjecture,
   * or the unit negation of answer literal used to obtain refutation */
  ANSWER_LITERAL,
  /** claim definition, definition introduced by a claim in the input */
  CLAIM_DEFINITION,
//     /** choice_axiom (Ax)((Ey)F(x,y) -> F(x,f(x))) */
//     CHOICE_AXIOM,
//     /** (Ax)(F(x)->F'(x)), G[F(t)] / G[F'(t)] */
//     MONOTONE_REPLACEMENT,
//     /** G[(Ax)F(x)] => G[F(t)] */
//     FORALL_ELIMINATION,
  /** rectify a formula */
  RECTIFY,
//     /** ~(F1 & ... & Fn) => ~F1 \/ ... \/ ~Fn */
//     NOT_AND,
//     /** ~(F1 \/ ... \/ Fn) => ~F1 & ... & ~Fn */
//     NOT_OR,
//     /** ~(F1 -> F2) => F1 & ~F2 */
//     NOT_IMP,
//     /** ~(F1 <-> F2) => F1 <~> F2 */
//     NOT_IFF,
//     /** ~(F1 <~> F2) => F1 <-> F2 */
//     NOT_XOR = 1,
//     /** ~~F => F */
//     NOT_NOT = 1,
//     /** ~(Ax)F => (Ex)~F */
//     NOT_FORALL,
//     /** ~(Ex)F => (Ax)~F */
//     NOT_EXISTS,
//     /** F1 -> F2 => ~F1 \/ F2 */
//     IMP_TO_OR,
//     /** F1 <-> F2 => (F1 -> F2) & (F2 -> F1) */
//     IFF_TO_AND,
//     /** F1 <~> F2 => (F1 \/ F2) & (~F1 \/ ~F2) */
//     XOR_TO_AND,
  /** replace formula F by (A x1...xn)F, where x1 ... xn are all
   *  free variables of F */
  CLOSURE,
  /** obtained by flattening (quantifiers, junctions) */
  FLATTEN,
  /** obtained by transformation into ENNF */
  ENNF,
  /** obtained by transformation into NNF */
  NNF,
  /** reduce a formula containing false or true, for example
   *  false & A ---> false */
  REDUCE_FALSE_TRUE,

  /** any kind of definition folding */
  DEFINITION_FOLDING,
//     /** Replace formula (Q x1 ... xk ... x_n)A by
//      * (Q x1 ... xk-1 xk+1 ... x_n)A, where xk does not occur in A */
//     DUMMY_QUANTIFIER_REMOVAL,
//     /** Transformation (A x1 ... xn)(F1 & ... & Fm) ->
//      * (A x1 ... xn)F1 & ... & (A x1 ... xn)Fm) */
//     FORALL_AND,
//     /** Transformation (E x1 ... xn)(F1 \/ ... \/ Fm) ->
//      * (E x1 ... xn)F1 \/ ... \/ (E x1 ... xn)Fm) */
//     EXISTS_OR,
//     /** (Q x)(Q y)F -> (Q y)(Q x)F */
//     QUANTIFIER_SWAP,
//     /** Transformation (A x1 x2)(F1 \/ F2) ->
//      * (A x1)F1 \/ ... \/ (A x2)F2), where x2 does not occur in F1.
//      * Can be applied to many variables and disjunctions of arbitrary length */
//     FORALL_OR,
//     /** Transformation (E x1 x2)(F1 & F2) ->
//      * (E x1)F1 & ... & (E x2)F2), where x2 does not occur in F1.
//      * Can be applied to many variables and disjunctions of arbitrary length */
//     EXISTS_AND,
//     /** obtained by permutations, e.g. f <=> g replaced by g <=> f */
//     PERMUT,
//     /** obtained by reordering equalities */
//     REORDER_EQ,
//     /** obtained by rewriting a positive equivalence
//      * f <=> ginto an implication f => g or g => f
//      */
//     HALF_EQUIV,
//     /** miniscoping */
//     MINISCOPE,
    /** skolemization */
    SKOLEMIZE,
    /** obtain clause from a formula */
    CLAUSIFY,
    /** obtain a formula from a clause */
    FORMULIFY,
    /** obtain a clause from a clause by removing duplicate literals */
    REMOVE_DUPLICATE_LITERALS,
//     /** shell clause transformed to a resolution clause */
//     SHELL_TO_RESOLUTION,
    /** resolution inference */
    RESOLUTION,
    /** constrained resolution inference */
    CONSTRAINED_RESOLUTION,
    /** equality proxy replacement */
    EQUALITY_PROXY_REPLACEMENT,
    /** definition of the equality proxy predicate in the form E(x,y) <=> x=y */
    EQUALITY_PROXY_AXIOM1,
    /** equality proxy axioms such as E(x,x) or ~E(x,y) \/ x=y */
    EQUALITY_PROXY_AXIOM2,
    /** unfolding by definitions f(x1,...,xn)=t */
    DEFINITION_UNFOLDING,
    /** any kind of definition folding */
    DEFINITION_FOLDING,
    /** introduction of auxiliady predicate for EPR-preserving skolemization */
    SKOLEM_PREDICATE_INTRODUCTION,
    /** EPR-preserving skolemization */
    PREDICATE_SKOLEMIZE,
//     /** expansion of row variable, KIF-specific */
//     ROW_VARIABLE_EXPANSION,
    /** introduction of new name p, p <=> C */
    PREDICATE_DEFINITION,
    /** unfolding predicate definitions */
    PREDICATE_DEFINITION_UNFOLDING,
    /** merging predicate definitions */
    PREDICATE_DEFINITION_MERGING,
    /** discovery of equivalences between atoms */
    EQUIVALENCE_DISCOVERY,
    /** sharing common subformulas across the problem */
    FORMULA_SHARING,
    /** reduce a formula containing false or true, for example
     *  false & A ---> false */
    REDUCE_FALSE_TRUE,
    /** Local simplification of formula, for example A | (B & A) ---> A*/
    LOCAL_SIMPLIFICATION,
    /** Normalization of formulas */
    NORMALIZATION,
    /** propagate equalities in formulas, for example
     * X=Y => X=f(Y) ---> X=f(X) */
    EQUALITY_PROPAGATION,
    /** remove from clause one or more inequalities <i>s != s</i> */
    TRIVIAL_INEQUALITY_REMOVAL,
    /** factoring inference */
    FACTORING,
    /** factoring with constraints */
    CONSTRAINED_FACTORING,
    /** subsumption resolution simplification rule */
    SUBSUMPTION_RESOLUTION,
    /** superposition inference */
    SUPERPOSITION,
    /** superposition with constraints */
    CONSTRAINED_SUPERPOSITION,
    /** equality factoring inference */
    EQUALITY_FACTORING,
    /** equality resolution inference */
    EQUALITY_RESOLUTION,
    /** redundant inference with extensionality-like clause */
    EXTENSIONALITY_RESOLUTION,
    /** forward demodulation inference */
    FORWARD_DEMODULATION,
    /** backward demodulation inference */
    BACKWARD_DEMODULATION,
    /** forward literal rewriting inference */
    FORWARD_LITERAL_REWRITING,
    /** inner rewriting */
    INNER_REWRITING,
    /** condensation inference */
    CONDENSATION,
    /** evaluation inference */
    EVALUATION,
    /** evaluation inference */
    INTERPRETED_SIMPLIFICATION,
    /** unused predicate definition removal */
    UNUSED_PREDICATE_DEFINITION_REMOVAL,
    /** pure predicate removal */
    PURE_PREDICATE_REMOVAL,
    /** inequality splitting */
    INEQUALITY_SPLITTING,
    /** inequality splitting name introduction */
    INEQUALITY_SPLITTING_NAME_INTRODUCTION,
    /** grounding */
    GROUNDING,
    /** equality axiom */
    EQUALITY_AXIOM,
    /** choice axiom */
    CHOICE_AXIOM,
    /** conflict clause generated by sat solver */
    SAT_CONFLICT_CLAUSE,
    /** distinctness axiom for numbers, generated by SimplifyProver */
    SIMPLIFY_PROVER_DISTINCT_NUMBERS_AXIOM,
    /** a not further specified theory axiom internally added by the class TheoryAxioms. */
    THEORY_AXIOM,
    /** acyclicity axiom for term algebras */
    TERM_ALGEBRA_ACYCLICITY_AXIOM,
    /** discrimation axiom for term algebras */
    TERM_ALGEBRA_DISCRIMINATION_AXIOM,
    /** distinctness axiom for term algebras */
    TERM_ALGEBRA_DISTINCTNESS_AXIOM,
    /** exhaustiveness axiom (or domain closure axiom) for term algebras */
    TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM,
    /** exhaustiveness axiom (or domain closure axiom) for term algebras */
    TERM_ALGEBRA_INJECTIVITY_AXIOM,
    /** one of two axioms of FOOL (distinct constants or finite domain) */
    FOOL_AXIOM,
    /** a theory axiom which is not generated internally in Vampire */
    EXTERNAL_THEORY_AXIOM,
    /** inference rule for term algebras (no cyclic terms)*/
    TERM_ALGEBRA_ACYCLICITY,
    /** inference rule for term algebras (no equality between terms of different constructors)*/
    TERM_ALGEBRA_DISTINCTNESS,
    /** inference rule for term algebras (injectivity of constructors)*/
    TERM_ALGEBRA_INJECTIVITY,
    //** Flatten a clause to separate theory literals */
    THEORY_FLATTENING,
    /** Introduction of formula to convert formulas used as argument positions.
     *  Such formulas have the form F->f(x)=1 or ~F->f(x)=0 */
    BOOLEAN_TERM_ENCODING,
    /** Elimination of FOOL expressions that makes a formula not syntactically first-order */
    FOOL_ELIMINATION,
    /** Elimination of $ite expressions */
    FOOL_ITE_ELIMINATION,
    /** Elimination of $let expressions */
    FOOL_LET_ELIMINATION,
    /** Replaces a literal of the form C[s] with C[true] \/ s = false, where s is a boolean non-variable term */
    FOOL_PARAMODULATION,
    /** definition introduced by AVATAR */
    AVATAR_DEFINITION,
    /** component introduced by AVATAR */
    AVATAR_COMPONENT,
    /** refutation of a AVATAR splitting branch */
    AVATAR_REFUTATION,
    /** sat clause representing FO clause for AVATAR */
    AVATAR_SPLIT_CLAUSE,
    /** sat clause representing FO clause for AVATAR */
    AVATAR_CONTRADICTION_CLAUSE,
    /** sat color elimination */
    SAT_COLOR_ELIMINATION,
    /** result of general splitting */
    GENERAL_SPLITTING,
    /** component introduced by general splitting */
    GENERAL_SPLITTING_COMPONENT,
    /** merge of clauses with common non-prop. parts */
    COMMON_NONPROP_MERGE,
    /** reducing the propositional part (due to simplification) */
    PROP_REDUCE,
    /** clause naming */
    CLAUSE_NAMING,
    /** bddzation */
    BDDZATION,
    /** tautology introduction */
    TAUTOLOGY_INTRODUCTION,
    /** replacing colored constants by skolem functions */
    COLOR_UNBLOCKING,
    /** generated as instance of its parent */
    INSTANCE_GENERATION,
    /** unit resulting resolution */
    UNIT_RESULTING_RESOLUTION,
    /** hyper-superposition */
    HYPER_SUPERPOSITION,
    /** global subsumption */
    GLOBAL_SUBSUMPTION,
    /** refutation in the SAT solver for InstGen */
    SAT_INSTGEN_REFUTATION,
    /** distinct equality removal */
    DISTINCT_EQUALITY_REMOVAL,
    /** inference coming from outside of Vampire */
    EXTERNAL,
    /** claim definition, definition introduced by a claim in the input */
    CLAIM_DEFINITION,
    /** BNFT flattening */
    BFNT_FLATTENING,
    /** BNFT axioms m != n */
    BFNT_DISTINCT,
    /** BNFT totality axioms R(x,1) \/ ... \/ R(x,n) */
    BFNT_TOTALITY,
    /* FMB flattening */
    FMB_FLATTENING,
    /* Functional definition for FMB */
    FMB_FUNC_DEF,
    /* Definition Introduction for FMB */
    FMB_DEF_INTRO, 
    /* Adding sort predicate */
    ADD_SORT_PREDICATES,
    /* Adding sort functions */
    ADD_SORT_FUNCTIONS,
    /* Instantiation */
    INSTANTIATION,
    /* Finite model not found */
    MODEL_NOT_FOUND,
    /* Induction hypothesis*/
    INDUCTION,
    /* Inductive strengthening*/
    INDUCTIVE_STRENGTH,
    /* rewriting by theory equalties 3x != 6 \/ C[x] ==> C[2] */
    GAUSSIAN_VARIABLE_ELIMINIATION,
  }; // class Inference::Rule

  explicit Inference(Rule r);

  /**
   * Decrease reference counters in referred units.
   *
   * Also does what destroyDirectlyOwned (see above).
   */
  void destroy();

  /**
   * Since we treat Inferences as PODs, this is intentionally left empty.
   *
   * Using this can lead to memory leaks unless reference counters in
   * referred clauses are decreased extra. (Such as in Clause::destroy()
   * which does not use Inference::destroy() to avoid deep recursion.)
   */
  ~Inference() {}

  /*
   * Inference objects are not meant to generally live outside Units
   * (who take care of calling destroy on Inference as appropriate).
   * In the rare cases in which an Inference has not been passed to a Unit yet,
   * a Destroyer can help calling destroy when coming out of scope prematurely
   * (e.g. on Unit construction abort or exception occurring).
   */
  class Destroyer {
    Inference* _destroyee;
  public:
    Destroyer(Inference& i) : _destroyee(&i) {}
    ~Destroyer() { if(_destroyee) _destroyee->destroy(); }
    void disable() { _destroyee = nullptr; }
  };

  /**
   * After minimizePremises has been called, some inferences may have fewer parents,
   * so statistics could change and this function recomputes them.
   * The function is only responsible for the update between this inference and its parents (if any).
   * The caller is responsible to ensure that parents are updated before children.
   **/
  void updateStatistics();

   vstring toString() const;

  /**
   * To implement lazy minimization of proofs coming from a SAT solver
   * without explicit proof recording.
   *
   * We want to postpone the potentially expensive
   * minimizing call to after
   * a complete refutation has been found.
   *
   * This is meant to be a no-op for all inferences except those related to SAT.
   */
  void minimizePremises();

  vstring name() const { return ruleName(_rule); }

  /** return the input type of the unit */
  UnitInputType inputType() const { return (UnitInputType)_inputType; }
  /** set the input type of the unit */
  void setInputType(UnitInputType it) { _inputType=it; }
  /** return true if inputType relates to a goal **/
  bool derivedFromGoal() const { return toNumber(_inputType) > toNumber(UnitInputType::ASSUMPTION); }

  /** Return the inference rule */
  InferenceRule rule() const { return _rule; }

  unsigned char getSineLevel() const { return _sineLevel; }
  /* should be only used to initialize the "whole chain" by SineUtils */
  void setSineLevel(unsigned char l) { _sineLevel = l; }

  /*
   * returns true if clause is a theory axiom
   *
   * Definition: A unit is a theory axiom iff both
   * 1) it is added internally in the TheoryAxiom-class or is an externally added theory axiom
   * 2) it is a clause.
   * In particular:
   * - integer/rational/real theory axioms are internal theory axioms
   * - term algebra axioms are internal theory axioms
   * - FOOL axioms are internal theory axioms
   * - equality-proxy-axioms, SimplifyProver’s-distinct-number-axioms, and BFNT-axioms
   *   are not treated as internal theory axioms, since they are not generated in TheoryAxioms
   *   (these axioms should probably be refactored into TheoryAxioms at some point)
   * - consequences of theory axioms are not theory axioms
   * - each theory axiom is a theory-tautology, but not every theory-tautology
   *   is a theory axiom (e.g. a consequence of two theory axioms or a conflict
   *   clause generated by a call to Z3)
   * We are interested in whether a clause is an internal theory axiom, because of several reasons:
   * - Internal theory axioms are already assumed to be clausal and simplified as much as possible
   * - Internal theory axioms often blow up the search space
   * - We don't need to pass internal theory axioms to another prover, if
   *   that prover natively handles the corresponding theory.
   *
   * TODO: handle the exhaustiveness axiom, which should be added as clause
   */
  bool isTheoryAxiom() const {
    return isExternalTheoryAxiomRule(_rule) || // maybe we don't want these?
        isTheoryAxiomRule(_rule);
  }

  /*
   * returns true if clause is an external theory axiom
   *
   * Definition: A unit is an external theory axiom iff it is added by parsing
   * an external theory axioms (currently only happens in some LTB mode)
   *
   * We are interested in whether a clause is an external theory axiom, because of several reasons:
   * - External theory axioms should already be simplified as much as possible
   * - External theory axioms often blow up the search space
   *
   * TODO: If an unit u with inference EXTERNAL_THEORY_AXIOM is a formula (and therefore not a clause),
   *  the results c_i of clausifying u will not be labeled EXTERNAL_THEORY_AXIOM, and therefore this function
   * will return false for c_i. In particular, adding the same formula as a clause or as formula could cause
   * different behavior by Vampire, which is probably a bad thing.
   */
  bool isExternalTheoryAxiom() const {
    return isExternalTheoryAxiomRule(_rule);
  }

  /** Mark the corresponding unit as read from a TPTP included file  */
  void markIncluded() { _included = 1; }
  /** true if the unit is read from a TPTP included file  */
  bool included() const { return _included; }

  /*
   * Returns true if the unit belonging to this inference is a pure theory descendant.
   *
   * Definition: A pure theory descendant is a unit that
   * has a derivation where each leaf is a theory axiom.
   * (This propagates in AVATAR from the clause being split to the corresponding components,
   * because some people thought it should be that way.)
   *
   * Note that a theory axiom itself is also a pure theory descendant.
   */
  bool isPureTheoryDescendant() const { return _isPureTheoryDescendant; }
  /** This is how AVATAR sets it... */
  void setPureTheoryDescendant(bool val) { _isPureTheoryDescendant = val; }

  unsigned inductionDepth() const { return _inductionDepth; }
  void setInductionDepth(unsigned d) { _inductionDepth = d; }

  void computeTheoryRunningSums();

  SplitSet* splits() const { return _splits; }
  void setSplits(SplitSet* splits) {
    ASS(splits != nullptr);
    ASS(!_splits);
    _splits=splits;
  }

  /** Return the age */
  unsigned age() const { return _age; }
  /** Set the age to @b a */
  void setAge(unsigned a) { _age = a; }

private:
  Kind _kind : 2;

  UnitInputType _inputType : 3;

  /** The rule used */
  InferenceRule _rule : 8;

  /** true if the unit is read from a TPTP included file  */
  bool _included : 1;

  /** track whether all leafs were theory axioms only */
  bool _isPureTheoryDescendant : 1;

  /** Induction depth **/
  unsigned _inductionDepth : 5;

  /** Sine level computed in SineUtils and used in various heuristics.
   * May stay uninitialized (i.e. always MAX), if not needed
   **/
  unsigned char _sineLevel : 8; // updated as the minimum from parents to children

  /** age */
  unsigned _age;

  SplitSet* _splits;

  /**
   * General storage for all Kinds of Inference:
   * INFERENCE_012 - use ptr1 and ptr2 in sequence storing its up to two premises "left to right"
   * - the unused are set to nullptr
   * INFERENCE_MANY - uses ptr1 to point to a list of units, its premises
   * INFERENCE_FROM_SAT_REFUTATION
   * - uses ptr1 to point to a list of units, its premises;
   * - uses ptr2 to point to a heap allocated struct for the sat premises and assumption
   *  which waits to be used during minimisation call; ptr2 can be empty (this means minimisation will be a noop)
   **/
  void* _ptr1;
  void* _ptr2;

public:
  // counting the leafs (in the tree rather than dag sense)
  // which are theory axioms and the total across all leafs
  float th_ancestors, all_ancestors; // we use floats, because this can grow large (because of the tree understanding of the dag);
  // CAREFUL: could this lead to platform differences?
}; // class Inference

} // namespace Kernel

#endif

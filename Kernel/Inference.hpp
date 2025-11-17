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
 * @file Inference.hpp
 * Defines class Inference for various kinds of inference
 *
 * @since 10/05/2007 Manchester
 */

#ifndef __Inference__
#define __Inference__

#include <iosfwd>
#include <limits>
#include <string>
#include <type_traits>

#include "Forwards.hpp"
#include "Debug/Assertion.hpp"

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
  /** Used to separate model definitions in model_check mode, should not appear in proof search */
  MODEL_DEFINITION = 6
};

inline constexpr std::underlying_type_t<UnitInputType> toNumber(UnitInputType t) { return static_cast<std::underlying_type_t<UnitInputType>>(t); }

UnitInputType getInputType(UnitList* units);
UnitInputType getInputType(UnitInputType t1, UnitInputType t2);

/** Step-by-step guide to adding an inference to Vampire:
 *  1) Update the enum below with an entry for the new inference.
 *     The enum is sorted into simplifying, generating etc. inferences.
 *     The new inference must be placed in the appropriate section.
 *  2) Update the ruleName(..) function in Inference.cpp to return
 *     the name of the new inference. This name will be used in proof
 *     printing.
 *  3) In the /Inferences directory, create a *.cpp and *.hpp files to 
 *     contain the code which defines the functionality of the new inference.
 *  4) Vampire supports five types of inferences. Immediate simplifications,
 *     simplifications (like immediate simplifications, but occur later in the
 *     given clause loop), forward simplification, backward simplifications
 *     and generating inferences. The core functionality of each of these
 *     is specified via five abstract classes in InferenceEngine.hpp. The new 
 *     inference should inherit from one of these.
 *  5) In SaturationAlgorithm.hpp update the createFromOptions() function
 *     to attach the new inference to the relevant (generating, simplifying, ...)
 *     front. This ensures that the inference is actually carried out during
 *     the saturation loop.
 *  6) If the new inference involves an index of some sort then the following
 *     needs to be done:
 *     6.1) Update TermIndex.* / LiteralIndex.* (whichever is appropriate) to
 *          create a new index for this inference. Specify how the index will
 *          handle new clauses (will it index subterms of the clause, literals or
 *          something else? How will it handle these?).
 *     6.2) Update IndexManager.cpp create(...) function to return an 
 *          instance of the new index on request.
 *     6.3) Update inference code to override the attach(...) and detach(...) 
 *          methods of the InferenceEngine class. Request the index in the 
 *          attach(...) function and release in the detach(...) function.
 *
 *  Further notes on creating inferences:
 *  - Immediate simplification inferences cannot be linked to an index
 *  - For an inference that works at subterms, please consider carefully
 *    which iterator to use to return these subterms. In Vampire, terms are
 *    of the form f(type_args, term_args). In most cases, inferences should NOT
 *    be working on type arguments. Please view TermIterators.hpp for a list of
 *    iterators available.
 *  - TermSubstitutionTrees, do NOT carry out any type checking. Thus, in the case
 *    where either the search or query term is a variable, a type check needs to
 *    be carried out by the inference code. This check may be a unification check or 
 *    a matching check depending on whether the inference is using unification or
 *    matching. Please view Superposition.cpp for an example of a unification check
 *    and ForwardDemodulation for an example of a matching check.
 */

/**
 * Tag to denote various kinds of inference rules.
 */
enum class InferenceRule : unsigned char {
  /** input formula or clause */
  INPUT,

  /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL
   * (preprocessing/normalisation) FORMULA TRANSFORMATION SHOULD BELONG
   * (see also INTERNAL_FORMULA_CLAUSE_TRANSFORMATION_LAST and isFormulaClauseTransformation below). */
  GENERIC_FORMULA_CLAUSE_TRANSFORMATION,
  /** negated conjecture from the input */
  NEGATED_CONJECTURE,
  /** introduction of answer literal into the conjecture */
  ANSWER_LITERAL_INJECTION,
  /** introduction of answer literal into the conjecture,
   * and skolemisation of input variables */
  ANSWER_LITERAL_INPUT_SKOLEMISATION,
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
  /** normalizing inference */
  THEORY_NORMALIZATION,
  ALASCA_INTEGER_TRANSFORMATION,
  /** skolemization */
  SKOLEMIZE,
  /** skolem symbol introduction (there can be more than one introduction during one SKOLEMIZE step) */
  SKOLEM_SYMBOL_INTRODUCTION,
  /** obtain clause from a formula */
  CLAUSIFY,
  /** change the orientations of some equations in a formula */
  REORIENT_EQUATIONS,
  /** the (preprocessing/normalisation) formula transformation marker --
    inferences between GENERIC_FORMULA_CLAUSE_TRANSFORMATION and INTERNAL_FORMULA_CLAUSE_TRANSFORMATION_LAST
    will be automatically understood as formula transformations (see also isFormulaClauseTransformation) */
  GENERIC_FORMULA_CLAUSE_TRANSFORMATION_LAST,

  /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL SIMPLIFYING INFERENCES SHOULD BELONG
   * (see also GENERIC_SIMPLIFYING_INFERENCE_LAST and isSimplifyingInferenceRule below). */
  GENERIC_SIMPLIFYING_INFERENCE,
  /** obtained by reordering literals */
  REORDER_LITERALS,
  /** obtain a clause from a clause by removing duplicate literals */
  REMOVE_DUPLICATE_LITERALS,
  /** remove from clause one or more inequalities <i>s != s</i> */
  TRIVIAL_INEQUALITY_REMOVAL,
  /** equality resolution as a simplification */
  EQUALITY_RESOLUTION_WITH_DELETION,
  /** forward subsumption resolution simplification rule */
  FORWARD_SUBSUMPTION_RESOLUTION,
  /** backward subsumption resolution simplification rule */
  BACKWARD_SUBSUMPTION_RESOLUTION,
  /** forward demodulation inference */
  FORWARD_DEMODULATION,
  /** backward demodulation inference */
  BACKWARD_DEMODULATION,
  ALASCA_FWD_DEMODULATION,
  ALASCA_BWD_DEMODULATION,
  /** forward subsumption demodulation inference */
  FORWARD_SUBSUMPTION_DEMODULATION,
  /** backward subsumption demodulation inference */
  BACKWARD_SUBSUMPTION_DEMODULATION,
  /** forward literal rewriting inference */
  FORWARD_LITERAL_REWRITING,
  /** inner rewriting */
  INNER_REWRITING,
  /** condensation inference */
  CONDENSATION,
  /** evaluation inference */
  EVALUATION,
  ALASCA_NORMALIZATION,
  ALASCA_ABSTRACTION,
  ALASCA_FLOOR_ELIMINATION,
  CANCELLATION,
  /** interpreted simplification inference */
  INTERPRETED_SIMPLIFICATION,
  //** Flatten a clause to separate theory literals */
  THEORY_FLATTENING,
  /** inference rule for term algebras (no equality between terms of different constructors)*/
  TERM_ALGEBRA_DISTINCTNESS,
  /** inference rule for term algebras (injectivity of constructors)*/
  TERM_ALGEBRA_POSITIVE_INJECTIVITY_SIMPLIFYING,
  /** inference rule for term algebras (injectivity of constructors)*/
  TERM_ALGEBRA_NEGATIVE_INJECTIVITY_SIMPLIFYING,
  /** global subsumption */
  GLOBAL_SUBSUMPTION, // CEREFUL: the main premise is not necessarily the first one!
  /** distinct equality removal */
  DISTINCT_EQUALITY_REMOVAL,
  /** simplification eliminating variables by rewriting arithmetic equalities: e.g.: 6 = 3 x \/ L[x] => L[2] */
  GAUSSIAN_VARIABLE_ELIMINIATION,
  ARITHMETIC_SUBTERM_GENERALIZATION,
  /* clause added after removing answer literal and saving it as a witness */
  ANSWER_LITERAL_REMOVAL,
  /* clause after successfully unifying two answer literals from the parent */
  ANSWER_LITERAL_JOIN_WITH_CONSTRAINTS,
  /* clause after joining two answer literals from the parent into an if-then-else*/
  ANSWER_LITERAL_JOIN_AS_ITE,
  /* clause with literals added from AVATAR assertions of the parent */
  AVATAR_ASSERTION_REINTRODUCTION,

  /* negative extnsionality */
  CASES_SIMP,
  ALASCA_VIRAS_QE,

  BOOL_SIMP,

  FUNCTION_DEFINITION_DEMODULATION,

  /** the last simplifying inference marker --
    inferences between GENERIC_SIMPLIFYING_INFERENCE and GENERIC_SIMPLIFYING_INFERENCE_LAST will be automatically understood simplifying
    (see also isSimplifyingInferenceRule) */
  GENERIC_SIMPLIFYING_INFERENCE_LAST,

  /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL GENERATING INFERENCES SHOULD BELONG
    * (see also GENERIC_GENERATING_INFERENCE_LAST and isGeneratingInferenceRule below). */
  GENERIC_GENERATING_INFERENCE,
  /** resolution inference */
  RESOLUTION,
  /** constrained resolution inference */
  CONSTRAINED_RESOLUTION,
  /** factoring inference */
  FACTORING,
  /** factoring with constraints */
  CONSTRAINED_FACTORING,
  /** superposition inference */
  SUPERPOSITION,
  /** function definition rewriting inference */
  FUNCTION_DEFINITION_REWRITING,
  /** superposition with constraints */
  CONSTRAINED_SUPERPOSITION,
  /** equality factoring inference */
  EQUALITY_FACTORING,
  /** equality resolution inference */
  EQUALITY_RESOLUTION,
  /** redundant inference with extensionality-like clause */
  EXTENSIONALITY_RESOLUTION,
  /** inference rule for term algebras (injectivity of constructors)*/
  TERM_ALGEBRA_INJECTIVITY_GENERATING,
  /** inference rule for term algebras (no cyclic terms)*/
  TERM_ALGEBRA_ACYCLICITY,
  /** Replaces a literal of the form C[s] with C[true] \/ s = false, where s is a boolean non-variable term */
  FOOL_PARAMODULATION,
  /** unit resulting resolution */
  UNIT_RESULTING_RESOLUTION,
  /* Induction hyperresolution */
  INDUCTION_HYPERRESOLUTION,
  /* Instantiation */
  INSTANTIATION, // used for theory reasoning
  /* inequality factoring rule of the ALASCA Calculus */
  ALASCA_FOURIER_MOTZKIN,
  ALASCA_INTEGER_FOURIER_MOTZKIN,
  ALASCA_TERM_FACTORING,
  ALASCA_FLOOR_BOUNDS,
  ALASCA_EQ_FACTORING,
  ALASCA_LITERAL_FACTORING,
  ALASCA_SUPERPOSITION,
  ALASCA_COHERENCE,
  ALASCA_COHERENCE_NORMALIZATION,
  ALASCA_VARIABLE_ELIMINATION,
  /** the last generating inference marker --
        inferences between GENERIC_GENERATING_INFERENCE and GENERIC_GENERATING_INFERENCE_LAST will be automatically understood generating
        (see also isGeneratingInferenceRule) */
  /* argument congruence: t = t' => tx = t'x*/
  ARG_CONG,
  INJECTIVITY,
  PRIMITIVE_INSTANTIATION,
  LEIBNIZ_ELIMINATION,
  HILBERTS_CHOICE_INSTANCE, // not considered a theory axiom at the moment (it's a HOL creature)
  NEGATIVE_EXT,
  EQ_TO_DISEQ,
  /** The next five rules can be either simplifying or generating */
  HOL_NOT_ELIMINATION,
  BINARY_CONN_ELIMINATION,
  VSIGMA_ELIMINATION,
  VPI_ELIMINATION,
  HOL_EQUALITY_ELIMINATION,

  /** the last generating inference marker --
        inferences between GENERIC_GENERATING_INFERENCE and GENERIC_GENERATING_INFERENCE_LAST will be automatically understood generating
        (see also isGeneratingInferenceRule) */
  GENERIC_GENERATING_INFERENCE_LAST,

  /** equality proxy replacement */
  EQUALITY_PROXY_REPLACEMENT,
  /** definition of the equality proxy predicate in the form E(x,y) <=> x=y */
  EQUALITY_PROXY_AXIOM1,
  /** equality proxy axioms such as E(x,x) or ~E(x,y) \/ x=y */
  EQUALITY_PROXY_AXIOM2,
  /** unfolding by definitions f(x1,...,xn)=t */
  DEFINITION_UNFOLDING,

  /** introduction of a new symbol f, f = term */
  FUNCTION_DEFINITION,

  /** introduction of new name p, p <=> C */
  PREDICATE_DEFINITION,
  /** unfolding predicate definitions */
  PREDICATE_DEFINITION_UNFOLDING,
  /** merging predicate definitions */
  PREDICATE_DEFINITION_MERGING,

  /** (consistent) polarity flipping of (some selected) predicates **/
  POLARITY_FLIPPING,

  /** unused predicate definition removal */
  UNUSED_PREDICATE_DEFINITION_REMOVAL,
  /** pure predicate removal */
  PURE_PREDICATE_REMOVAL,
  /** inequality splitting */
  INEQUALITY_SPLITTING,
  /** inequality splitting name introduction */
  INEQUALITY_SPLITTING_NAME_INTRODUCTION,
  /** distinctness axiom */
  DISTINCTNESS_AXIOM,
  /** Introduction of formula to convert formulas used as argument positions.
   *  Such formulas have the form F->f(x)=1 or ~F->f(x)=0 */
  BOOLEAN_TERM_ENCODING,
  /** Elimination of FOOL expressions that makes a formula not syntactically first-order */
  FOOL_ELIMINATION,
  /** Definition of $ite expressions */
  FOOL_ITE_DEFINITION,
  /** Definition of $let expressions */
  FOOL_LET_DEFINITION,
  /** Definition of formulas used as terms */
  FOOL_FORMULA_DEFINITION,
  /** Definition for $match expressions */
  FOOL_MATCH_DEFINITION,
  /** result of general splitting */
  GENERAL_SPLITTING,
  /** component introduced by general splitting */
  GENERAL_SPLITTING_COMPONENT,
  /** replacing colored constants by skolem functions */
  COLOR_UNBLOCKING,

  /** sat color elimination */
  SAT_COLOR_ELIMINATION,
  /** obtain a formula from a clause */
  FORMULIFY,

  /* FMB flattening */
  FMB_FLATTENING,
  /* Functional definition for FMB */
  FMB_FUNC_DEF,
  /* Definition Introduction for FMB */
  FMB_DEF_INTRO,
  /* Finite model not found */
  MODEL_NOT_FOUND,

  /* Adding sort predicate */
  ADD_SORT_PREDICATES,
  /* Adding sort functions */
  ADD_SORT_FUNCTIONS,

  /* the unit clause against which the Answer is extracted in the last step */
  ANSWER_LITERAL_RESOLVER,

  /** A (first-order) tautology generated on behalf of a decision procedure,
   * whose propositional counterpart becomes a conflict clause in a sat solver */
  THEORY_TAUTOLOGY_SAT_CONFLICT,

  GENERIC_AVATAR_INFERENCE,
  /** definition introduced by AVATAR */
  AVATAR_DEFINITION,
  /** component introduced by AVATAR */
  AVATAR_COMPONENT,
  /** inconsistency from AVATAR SAT solver */
  AVATAR_REFUTATION,
  /** inconsistency from AVATAR SMT solver (not necessarily propositionally unsat) */
  AVATAR_REFUTATION_SMT,
  /** sat clause representing FO clause for AVATAR */
  AVATAR_SPLIT_CLAUSE,
  /** sat clause representing FO clause for AVATAR */
  AVATAR_CONTRADICTION_CLAUSE,
  GENERIC_AVATAR_INFERENCE_LAST,

  /** a not further specified theory axiom internally added by the class TheoryAxioms. */
  GENERIC_THEORY_AXIOM, // CAREFUL: adding rules here influences the theory_split_queue heuristic
  /** Some specific groups of axioms coming from TheoryAxioms.cpp" */
  THA_COMMUTATIVITY,
  THA_ASSOCIATIVITY,
  THA_RIGHT_IDENTITY,
  THA_LEFT_IDENTITY,
  THA_INVERSE_OP_OP_INVERSES,
  THA_INVERSE_OP_UNIT,
  THA_INVERSE_ASSOC,
  THA_NONREFLEX,
  THA_TRANSITIVITY,
  THA_ORDER_TOTALITY,
  THA_ORDER_MONOTONICITY,
  THA_ALASCA,
  THA_PLUS_ONE_GREATER,
  THA_ORDER_PLUS_ONE_DICHOTOMY,
  THA_MINUS_MINUS_X,
  THA_TIMES_ZERO,
  THA_DISTRIBUTIVITY,
  THA_DIVISIBILITY,
  THA_MODULO_MULTIPLY,
  THA_MODULO_POSITIVE,
  THA_MODULO_SMALL,
  THA_DIVIDES_MULTIPLY,
  THA_NONDIVIDES_SKOLEM,
  THA_ABS_EQUALS,
  THA_ABS_MINUS_EQUALS,
  THA_QUOTIENT_NON_ZERO,
  THA_QUOTIENT_MULTIPLY,
  THA_EXTRA_INTEGER_ORDERING,
  THA_FLOOR_SMALL,
  THA_FLOOR_BIG,
  THA_CEILING_BIG,
  THA_CEILING_SMALL,
  THA_TRUNC1,
  THA_TRUNC2,
  THA_TRUNC3,
  THA_TRUNC4,
  THA_ARRAY_EXTENSIONALITY,
  THA_BOOLEAN_ARRAY_EXTENSIONALITY, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
  THA_BOOLEAN_ARRAY_WRITE1, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
  THA_BOOLEAN_ARRAY_WRITE2, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
  THA_ARRAY_WRITE1,
  THA_ARRAY_WRITE2,
  /** acyclicity axiom for term algebras */
  TERM_ALGEBRA_ACYCLICITY_AXIOM,
  TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM,
  TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM,
  /** discrimination axiom for term algebras */
  TERM_ALGEBRA_DISCRIMINATION_AXIOM,
  /** distinctness axiom for term algebras */
  TERM_ALGEBRA_DISTINCTNESS_AXIOM,
  /** exhaustiveness axiom (or domain closure axiom) for term algebras */
  TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM, // currently (sometimes) applied to a formula, so won't propagate to clause->isTheoryAxiom()
  /** injectivity axiom for term algebras */
  TERM_ALGEBRA_INJECTIVITY_AXIOM,
  /** distinctness axiom for FOOL */
  FOOL_AXIOM_TRUE_NEQ_FALSE,
  /** exhaustiveness (finite domain) axiom for FOOL */
  FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE,

  /* Structural induction axioms */
  STRUCT_INDUCTION_AXIOM_ONE,
  STRUCT_INDUCTION_AXIOM_TWO,
  STRUCT_INDUCTION_AXIOM_THREE,
  STRUCT_INDUCTION_AXIOM_RECURSION,
  /* Integer induction axioms for infinite intervals */
  INT_INF_UP_INDUCTION_AXIOM,
  INT_INF_DOWN_INDUCTION_AXIOM,
  /* Integer induction axioms for finite intervals */
  INT_FIN_UP_INDUCTION_AXIOM,
  INT_FIN_DOWN_INDUCTION_AXIOM,
  /* Integer induction axioms for infinite interval and the default bound */
  INT_DB_UP_INDUCTION_AXIOM,
  INT_DB_DOWN_INDUCTION_AXIOM,

  /** the last theory axiom marker --
    axioms between THEORY_AXIOM and GENERIC_THEORY_AXIOM_LAST will be automatically making their respective clauses isTheoryAxiom() true */
  GENERIC_THEORY_AXIOM_LAST
}; // class InferenceRule

inline constexpr std::underlying_type_t<InferenceRule> toNumber(InferenceRule r) { return static_cast<std::underlying_type_t<InferenceRule>>(r); }

inline bool isFormulaClauseTransformation(InferenceRule r) {
  return (toNumber(r) > toNumber(InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION) &&
      toNumber(r) < toNumber(InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION_LAST));
}

/** Currently not enforced but (almost) assumed:
 * - these are simplifying inferences used during proof search
 * - therefore they operate on Clauses
 * - there is always a main premise, which is going to be the first one returned by Iterator
 * (CAREFUL: this is currently a problem for GLOBAL_SUBSUMPTION)
 * - the age of the corresponding Clause is the same as that of this main premise
 **/
inline bool isSimplifyingInferenceRule(InferenceRule r) {
  return (toNumber(r) > toNumber(InferenceRule::GENERIC_SIMPLIFYING_INFERENCE) &&
      toNumber(r) < toNumber(InferenceRule::GENERIC_SIMPLIFYING_INFERENCE_LAST));
}

/**
 * Currently not enforced but (almost) assumed:
 * - these are generating inferences used during proof search
 * - therefore they operate on Clauses
 * - the age of the corresponding Clause is computed as the max over parent's ages +1
 */
inline bool isGeneratingInferenceRule(InferenceRule r) {
  return (toNumber(r) > toNumber(InferenceRule::GENERIC_GENERATING_INFERENCE) &&
      toNumber(r) < toNumber(InferenceRule::GENERIC_GENERATING_INFERENCE_LAST));
}

inline bool isTheoryAxiomRule(InferenceRule r) {
  return (toNumber(r) > toNumber(InferenceRule::GENERIC_THEORY_AXIOM) &&
      toNumber(r) < toNumber(InferenceRule::GENERIC_THEORY_AXIOM_LAST));
}

std::string inputTypeName(UnitInputType type);
std::string ruleName(InferenceRule rule);

/*
* The following structs are here just that we can have specialized overloads for the Inference constructor (see below)
* There should be not computational overhead under modern compilers.
*/

struct FromInput {
  FromInput(UnitInputType it) : inputType(it) {}
  UnitInputType inputType;
};

struct TheoryAxiom {
  TheoryAxiom(InferenceRule r) : rule(r) {}
  InferenceRule rule;
};

struct FormulaClauseTransformation {
  FormulaClauseTransformation(InferenceRule r, Unit* p) : rule(r), premise(p) {}
  InferenceRule rule;
  Unit* premise;
};

struct FormulaClauseTransformationMany {
  FormulaClauseTransformationMany(InferenceRule r, UnitList* p) : rule(r), premises(p) {}
  InferenceRule rule;
  UnitList* premises;
};

struct SimplifyingInference1 {
  SimplifyingInference1(InferenceRule r, Clause* main_premise) : rule(r), premise(main_premise) {}
  InferenceRule rule;
  Clause* premise;
};

struct SimplifyingInference2 {
  SimplifyingInference2(InferenceRule r, Clause* main_premise, Clause* other_premise) :
    rule(r), premise1(main_premise), premise2(other_premise) {}
  InferenceRule rule;
  Clause* premise1;
  Clause* premise2;
};

struct SimplifyingInferenceMany {
  SimplifyingInferenceMany(InferenceRule r, UnitList* prems) : rule(r), premises(prems) {}
  InferenceRule rule;
  UnitList* premises;
};

struct GeneratingInference1 {
  GeneratingInference1(InferenceRule r, Clause* p) : rule(r), premise(p) {}
  InferenceRule rule;
  Clause* premise;
};

struct GeneratingInference2 {
  GeneratingInference2(InferenceRule r, Clause* p1, Clause* p2) : rule(r), premise1(p1), premise2(p2) {}
  InferenceRule rule;
  Clause* premise1;
  Clause* premise2;
};

struct GeneratingInferenceMany {
  GeneratingInferenceMany(InferenceRule r, UnitList* prems) : rule(r), premises(prems) {}
  InferenceRule rule;
  UnitList* premises;
};

struct NonspecificInference0 {
  NonspecificInference0(UnitInputType it, InferenceRule r) : inputType(it), rule(r) {}
  UnitInputType inputType;
  InferenceRule rule;
};

struct NonspecificInference1 {
  NonspecificInference1(InferenceRule r, Unit* p) : rule(r), premise(p) {}
  InferenceRule rule;
  Unit* premise;
};

struct NonspecificInference2 {
  NonspecificInference2(InferenceRule r, Unit* p1, Unit* p2) : rule(r), premise1(p1), premise2(p2) {}
  InferenceRule rule;
  Unit* premise1;
  Unit* premise2;
};

struct NonspecificInferenceMany {
  NonspecificInferenceMany(InferenceRule r, UnitList* prems) : rule(r), premises(prems) {}
  InferenceRule rule;
  UnitList* premises;
};

struct InferenceOfASatClause {
  InferenceOfASatClause(InferenceRule r, SAT::SATClause* cl, UnitList* prems) : rule(r), clause(cl), premises(prems) {}
  InferenceRule rule;
  SAT::SATClause* clause;
  UnitList* premises;
};

struct NeedsMinimization; // defined in SATInference.hpp

class Inference;
std::ostream& operator<<(std::ostream& out, Inference const& self);

/**
 * Class to represent inferences
 */
class Inference
{
private:
  void *operator new(size_t) = delete;

  enum class Kind : unsigned char {
    INFERENCE_012,
    INFERENCE_MANY,
    SAT,
    SAT_NEEDS_MINIMIZATION
  };

  void initDefault(UnitInputType inputType, InferenceRule r) {
    _inputType = inputType;
    _rule = r;
    _included = false;
    _inductionDepth = 0;
    _XXNarrows = 0;
    _reductions = 0;
    _sineLevel = std::numeric_limits<decltype(_sineLevel)>::max();
    _splits = nullptr;
    _age = 0;
  }

  void init0(UnitInputType inputType, InferenceRule r);
  void init1(InferenceRule r, Unit* premise);
  void init2(InferenceRule r, Unit* premise1, Unit* premise2);
  void initMany(InferenceRule r, UnitList* premises);

public:
  /* FromInput inferences are automatically InferenceRule::INPUT. */
  Inference(const FromInput& fi);

  /* Theory axioms are automatically of inputType AXIOM.
   * and the corresponding rule should satisfy isTheoryAxiomRule
   * CAREFUL: extending what TheoryAxiomRule is influences the theory_split_queue heuristic
   **/
  Inference(const TheoryAxiom& ta);

  /* A formula transformation inference automatically propagates the _included flag from the parent to the child
     (later during clausal proof search, currently, this is not done anymore)*/
  Inference(const FormulaClauseTransformation& ft);
  // _included propagated from the first premise here
  Inference(const FormulaClauseTransformationMany& ft);

  /* A generating inference automatically computes age as 1 + the maximum over the parents' age */
  Inference(const GeneratingInference1& gi);
  Inference(const GeneratingInference2& gi);
  Inference(const GeneratingInferenceMany& gi);

  /* A simplifying inference has a main premise and possibly also side premises.
   * The age is automatically computed as the age of the main premise */
  Inference(const SimplifyingInference1& si);
  Inference(const SimplifyingInference2& si);
  Inference(const SimplifyingInferenceMany& si);

  /** No special propagation, no extra checks. Use sparingly. */
  Inference(const NonspecificInference0& gi);
  Inference(const NonspecificInference1& gi);
  Inference(const NonspecificInference2& gi);
  Inference(const NonspecificInferenceMany& gi);

  Inference(const NeedsMinimization& fsr);
  Inference(const InferenceOfASatClause& isc);

  Inference(const Inference&) = default;

  /**
   * A class that iterates over parents.
   * @since 04/01/2008 Torrevieja
   */
  struct Iterator {
    /** The content, can be anything (interpretation depends on Kind) */
    union {
      void* pointer;
      int integer;
    };
  };

  Iterator iterator() const;
  bool hasNext(Iterator& it) const;
  Unit* next(Iterator& it) const;

  /*
  * The supporting heap allocated objects are deleted
  * (The unitList of INFERENCE_MANY and, additionally,
  * the FromSatRefutationInfo of INFERENCE_FROM_SAT_REFUTATION).
  */
  void destroyDirectlyOwned();
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

 friend std::ostream& operator<<(std::ostream& out, Inference const& self);

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

  // returns ruleName; with inputTypeName on top, in the case of ruleName == INPUT
  std::string name() const;

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
   * Definition: A unit is a theory axiom iff it is added internally in the TheoryAxiom-class
   * In particular:
   * - integer/rational/real theory axioms are theory axioms
   * - term algebra axioms are theory axioms
   * - FOOL axioms are theory axioms
   * - instances of induction axioms
   * - equality-proxy-axioms
   *   are not treated as theory axioms, since they are not generated in TheoryAxioms
   *   (these axioms should probably be refactored into TheoryAxioms at some point)
   * - consequences of theory axioms are not theory axioms
   * - each theory axiom is a theory-tautology, but not every theory-tautology
   *   is a theory axiom (e.g. a consequence of two theory axioms or a conflict
   *   clause generated by a call to Z3)
   * We are interested in whether a clause is a theory axiom, because of several reasons:
   * - Theory axioms are already assumed to be simplified as much as possible
   * - Theory axioms often blow up the search space
   * - We don't need to pass theory axioms to another prover, if
   *   that prover natively handles the corresponding theory.
   */
  bool isTheoryAxiom() const {
    return isTheoryAxiomRule(_rule);
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

  unsigned xxNarrows() const { return _XXNarrows; }
  /** used to propagate in AVATAR **/
  void setXXNarrows(unsigned n) { _XXNarrows = n; }
  void incXXNarrows(){ if(_XXNarrows < 8){ _XXNarrows++; } }

  unsigned reductions() const { return _reductions; }
  void setReductions(unsigned r) { _reductions = r; } 
  void increaseReductions(unsigned n){ _reductions += n; }

  void computeTheoryRunningSums();

  SplitSet* splits() const { return _splits; }
  void setSplits(SplitSet* splits) {
    ASS(splits != nullptr);
    ASS(!_splits);
    _splits=splits;
  }

  SAT::SATClause *satPremise() const
  { return _kind == Kind::SAT ? static_cast<SAT::SATClause *>(_ptr2) : nullptr; }

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

  /** number of XX' narrows carried out on clause */
  unsigned _XXNarrows : 3;
  /** number of weak reductions in the history of this clause */
  unsigned _reductions : 30;

  // aligned to 64 bits

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

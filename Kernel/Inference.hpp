
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

#include "Kernel/Unit.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"

using namespace std;
using namespace Lib;

namespace Kernel {

/**
 * Class to represent inferences
 */
class Inference
{
public:
  /**
   * Tag to denote various kinds of inference rules.
   */
  enum Rule {
    /** input formula or clause */
    INPUT,
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
    /** obtained by reordering literals */
    REORDER_LITERALS,
    /** obtained by transformation into ENNF */
    ENNF,
    /** obtained by transformation into NNF */
    NNF,
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
    /** choice axiom */
    CHOICE_AXIOM,
    /** skolemization */
    SKOLEMIZE,
    /** obtain clause from a formula */
    CLAUSIFY,

    /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL SIMPLIFYING INFERENCES SHOULD BELONG
     * (see also INTERNAL_SIMPLIFYING_INFERNCE_LAST and isSimplifyingInferenceRule below). */
    GENERIC_SIMPLIFYING_INFERNCE,
    /** obtain a clause from a clause by removing duplicate literals */
    REMOVE_DUPLICATE_LITERALS,
    /** remove from clause one or more inequalities <i>s != s</i> */
    TRIVIAL_INEQUALITY_REMOVAL,
    /** subsumption resolution simplification rule */
    SUBSUMPTION_RESOLUTION,
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
    /** interpreted simplification inference */
    INTERPRETED_SIMPLIFICATION,
    /** inference rule for term algebras (no equality between terms of different constructors)*/
    TERM_ALGEBRA_DISTINCTNESS,
    /** inference rule for term algebras (no cyclic terms)*/
    TERM_ALGEBRA_ACYCLICITY,
    /** inference rule for term algebras (injectivity of constructors)*/
    TERM_ALGEBRA_INJECTIVITY_SIMPLIFYING,
    /** hyper-superposition */
    HYPER_SUPERPOSITION_SIMPLIFYING, // not used at the moment
    /** global subsumption */
    GLOBAL_SUBSUMPTION, // CEREFUL: the main premise is not necessarily the first one!
    /** distinct equality removal */
    DISTINCT_EQUALITY_REMOVAL,
    /** the last simplifying inference marker --
      inferences between GENERIC_SIMPLIFYING_INFERNCE and INTERNAL_SIMPLIFYING_INFERNCE_LAST will be automatically understood simplifying
      (see also isSimplifyingInferenceRule) */
    INTERNAL_SIMPLIFYING_INFERNCE_LAST,


    /** THIS DEFINES AN INTERVAL IN THIS ENUM WHERE ALL SIMPLIFYING INFERENCES SHOULD BELONG
      * (see also INTERNAL_GENERATING_INFERNCE_LAST and isGeneratingInferenceRule below). */
    GENERIC_GENERATING_INFERNCE,
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
    /** Replaces a literal of the form C[s] with C[true] \/ s = false, where s is a boolean non-variable term */
    FOOL_PARAMODULATION,
    /** unit resulting resolution */
    UNIT_RESULTING_RESOLUTION,
    /** hyper-superposition */
    HYPER_SUPERPOSITION_GENERATING,

    /** generated as instance of its parent */
    INSTANCE_GENERATION, // used by InstGen. Fun fact: the inference has one parent (logically) but the age is set from two parents (and +1)!
    /* Instantiation */
    INSTANTIATION, // used for theory reasoning
    /** the last generating inference marker --
          inferences between GENERIC_GENERATING_INFERNCE and INTERNAL_GENERATING_INFERNCE_LAST will be automatically understood generating
          (see also isGeneratingInferenceRule) */
    INTERNAL_GENERATING_INFERNCE_LAST,


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
    /** introduction of new name p, p <=> C */
    PREDICATE_DEFINITION,
    /** unfolding predicate definitions */
    PREDICATE_DEFINITION_UNFOLDING,
    /** merging predicate definitions */
    PREDICATE_DEFINITION_MERGING,
    /** reduce a formula containing false or true, for example
     *  false & A ---> false */
    REDUCE_FALSE_TRUE,
    /** normalizing inference */
    THEORY_NORMALIZATION,
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
    /** conflict clause generated by sat solver */
    SAT_CONFLICT_CLAUSE,
    /** distinctness axiom for numbers, generated by SimplifyProver */
    SIMPLIFY_PROVER_DISTINCT_NUMBERS_AXIOM,
    /** Introduction of formula to convert formulas used as argument positions.
     *  Such formulas have the form F->f(x)=1 or ~F->f(x)=0 */
    BOOLEAN_TERM_ENCODING,
    //** Flatten a clause to separate theory literals */
    THEORY_FLATTENING,
    /** Elimination of FOOL expressions that makes a formula not syntactically first-order */
    FOOL_ELIMINATION,
    /** Elimination of $ite expressions */
    FOOL_ITE_ELIMINATION,
    /** Elimination of $let expressions */
    FOOL_LET_ELIMINATION,
    /** result of general splitting */
    GENERAL_SPLITTING,
    /** component introduced by general splitting */
    GENERAL_SPLITTING_COMPONENT,
    /** replacing colored constants by skolem functions */
    COLOR_UNBLOCKING,

    /** refutation in the SAT solver for InstGen */
    SAT_INSTGEN_REFUTATION,

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
    /** obtain a formula from a clause */
    FORMULIFY,

    /** inference coming from outside of Vampire */
    EXTERNAL,

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
    /* Finite model not found */
    MODEL_NOT_FOUND,

    /* Adding sort predicate */
    ADD_SORT_PREDICATES,
    /* Adding sort functions */
    ADD_SORT_FUNCTIONS,

    /* Induction hypothesis*/
    INDUCTION_AXIOM,

    /** a not further specified theory axiom internally added by the class TheoryAxioms. */
    GENERIC_THEORY_AXIOM,
    /** Some specific groups of axioms coming from TheoryAxioms.cpp" */
    THEORY_AXIOM_COMMUTATIVITY,
    THEORY_AXIOM_ASSOCIATIVITY,
    THEORY_AXIOM_RIGHT_IDENTINTY,
    THEORY_AXIOM_LEFT_IDENTINTY,
    THEORY_AXIOM_INVERSE_OP_OP_INVERSES,
    THEORY_AXIOM_INVERSE_OP_UNIT,
    THEORY_AXIOM_INVERSE_ASSOC,
    THEORY_AXIOM_NONREFLEX,
    THEORY_AXIOM_TRANSITIVITY,
    THEORY_AXIOM_ORDER_TOTALALITY,
    THEORY_AXIOM_ORDER_MONOTONICITY,
    THEORY_AXIOM_PLUS_ONE_GREATER,
    THEORY_AXIOM_ORDER_PLUS_ONE_DICHOTOMY,
    THEORY_AXIOM_MINUS_MINUS_X,
    THEORY_AXIOM_TIMES_ZERO,
    THEORY_AXIOM_DISTRIBUTIVITY,
    THEORY_AXIOM_DIVISIBILITY,
    THEORY_AXIOM_MODULO_MULTIPLY,
    THEORY_AXIOM_MODULO_POSITIVE,
    THEORY_AXIOM_MODULO_SMALL,
    THEORY_AXIOM_DIVIDES_MULTIPLY,
    THEORY_AXIOM_NONDIVIDES_SKOLEM,
    THEORY_AXIOM_ABS_EQUALS,
    THEORY_AXIOM_ABS_MINUS_EQUALS,
    THEORY_AXIOM_QUOTIENT_NON_ZERO,
    THEORY_AXIOM_QUOTIENT_MULTIPLY,
    THEORY_AXIOM_EXTRA_INTEGER_ORDERING,
    THEORY_AXIOM_FLOOR_SMALL,
    THEORY_AXIOM_FLOOR_BIG,
    THEORY_AXIOM_CEILING_BIG,
    THEORY_AXIOM_CEILING_SMALL,
    THEORY_AXIOM_TRUNC1,
    THEORY_AXIOM_TRUNC2,
    THEORY_AXIOM_TRUNC3,
    THEORY_AXIOM_TRUNC4,
    THEORY_AXIOM_ARRAY_EXTENSIONALITY,
    THEORY_AXIOM_BOOLEAN_ARRAY_EXTENSIONALITY, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
    THEORY_AXIOM_BOOLEAN_ARRAY_WRITE1, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
    THEORY_AXIOM_BOOLEAN_ARRAY_WRITE2, // currently applied to a formula, so won't propagate to clause->isTheoryAxiom()
    THEORY_AXIOM_ARRAY_WRITE1,
    THEORY_AXIOM_ARRAY_WRITE2,
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
    /** exhaustiveness axiom (or domain closure axiom) for term algebras */
    TERM_ALGEBRA_INJECTIVITY_AXIOM,
    /** one of two axioms of FOOL (distinct constants or finite domain) */
    FOOL_AXIOM_TRUE_NEQ_FALSE,
    FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE,
    /** the last internal theory axiom marker --
      axioms between THEORY_AXIOM and INTERNAL_THEORY_AXIOM_LAST will be automatically making their respective clauses isTheoryAxiom() true */
    INTERNAL_THEORY_AXIOM_LAST,
    /** a theory axiom which is not generated internally in Vampire */
    EXTERNAL_THEORY_AXIOM
  }; // class Inference::Rule

  /** Currently not enforced but (almost) assumed:
   * - these are simplifying inferences used during proof search
   * - therefore they operate on Clauses
   * - there is always a main premise, which is going to be the first one returned by Iterator
   * (CAREFUL: this is currently a problem for GLOBAL_SUBSUMPTION)
   * - the age of the corresponding Clause is the same as that of this main premise
   **/
  static bool isSimplifyingInferenceRule(Rule r) {
    return (static_cast<unsigned>(r) >= static_cast<unsigned>(Inference::GENERIC_SIMPLIFYING_INFERNCE) &&
        static_cast<unsigned>(r) < static_cast<unsigned>(Inference::INTERNAL_SIMPLIFYING_INFERNCE_LAST));
  }

  /**
   * Currently not enforced but (almost) assumed:
   * - these are generating inferences used during proof search
   * - therefore they operate on Clauses
   * - the age of the corresponding Clause is computed as the max over parent's ages +1
   */
  static bool isGeneratingInferenceRule(Rule r) {
    return (static_cast<unsigned>(r) >= static_cast<unsigned>(Inference::GENERIC_GENERATING_INFERNCE) &&
        static_cast<unsigned>(r) < static_cast<unsigned>(Inference::INTERNAL_GENERATING_INFERNCE_LAST));
  }

  /** Currently not enforced but assumed:
   * - theory axioms should not have any premises
   **/
  static bool isTheoryAxiomRule(Rule r) {
    return (static_cast<unsigned>(r) >= static_cast<unsigned>(Inference::GENERIC_THEORY_AXIOM) &&
        static_cast<unsigned>(r) < static_cast<unsigned>(Inference::INTERNAL_THEORY_AXIOM_LAST));
  }

  static bool isExternalTheoryAxiomRule(Rule r) {
    return r == Inference::EXTERNAL_THEORY_AXIOM;
  }

  explicit Inference(Rule r);

  /**
   * Destroy the Inference object and decrease reference
   * counters in refered clauses.
   */
  virtual void destroy() = 0;
  /**
   * Destroy the Inference object without decreasing reference
   * counters in refered units.
   *
   * Using this can lead to memory leaks unless reference counters in
   * refered clauses are decreased extra. (Such as in Clause::destroy()
   * which does not use Inference::destroy() to avoid deep recursion.)
   */
  virtual ~Inference() {}

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
  virtual void minimizePremises() {}

  /**
   * After minimizePremises has been called, some inferences may have fewer parents,
   * so statistics could change and this function recomputes them.
   * The function is only responsible for the update between this inference and its parents (if any).
   * The caller is responsible to ensure that parents are updated before children.
   **/
  virtual void updateStatistics() = 0;

  static vstring ruleName(Rule rule);
  vstring name() const { return ruleName(_rule); }

  // TODO used in some proofExtra output
  //      find a better place for this
  static bool positionIn(TermList& subterm,TermList* term, vstring& position);
  static bool positionIn(TermList& subterm,Term* term, vstring& position);

  CLASS_NAME(Inference);
  USE_ALLOCATOR(Inference);

  /**
   * A class that iterates over parents.
   * @since 04/01/2008 Torrevieja
   */
  struct Iterator {
    /** The content, can be anything */
    union {
      void* pointer;
      int integer;
    };
  };

  virtual Iterator iterator() const = 0;
  virtual bool hasNext(Iterator& it) const = 0;
  virtual Unit* next(Iterator& it) const = 0;

  /** Return the inference rule */
  Rule rule() const { return _rule; }

  /** Set extra string */
  void setExtra(vstring e){ _extra=e; }
  /** Return the extra string */
  vstring extra() { return _extra; }

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
   *  the results c_i of clausifying u will not be labelled EXTERNAL_THEORY_AXIOM, and therefore this function
   * will return false for c_i. In particular, adding the same formula as a clause or as formula could cause
   * different behaviour by Vampire, which is probably a bad thing.
   */
  bool isExternalTheoryAxiom() const {
    return isExternalTheoryAxiomRule(_rule);
  }

  // counting the leafs (in the tree rather than dag sense)
  // which are theory axioms and the total across all leafs
  float th_ancestors, all_ancestors; // we use floats, because this can grow large (because of the tree understanding of the dag); CAREFUL: could this lead to platform differences?

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

  void computeTheoryRunningSums() {
    CALL("Inference::computeTheoryRunningSums");

    Inference::Iterator parentIt = iterator();

    // inference without parents
    if (!hasNext(parentIt))
    {
      th_ancestors = isTheoryAxiom() ? 1.0 : 0.0;
      all_ancestors = 1.0;
    }
    else
    {
      // for simplifying inferences, propagate running sums of main premise
      if (isSimplifyingInferenceRule(_rule))
      {
        // all simplifying inferences save the main premise as first premise
        Unit* mainPremise = next(parentIt);
        th_ancestors = mainPremise->inference()->th_ancestors;
        all_ancestors = mainPremise->inference()->all_ancestors;
      }
      // for non-simplifying inferences, compute running sums as sum over all parents
      else
      {
        th_ancestors = 0.0;
        all_ancestors = 0.0; // there is going to be at least one, eventually
        while (hasNext(parentIt))
        {
          Unit *parent = next(parentIt);
          th_ancestors += parent->inference()->th_ancestors;
          all_ancestors += parent->inference()->all_ancestors;
        }
      }
    }
  }

protected:
  /** The rule used */
  Rule _rule;
  /** Extra information */
  vstring _extra;
  /** track whether all leafs were theory axioms only */
  bool _isPureTheoryDescendant;
  /** Induction depth **/
  unsigned _inductionDepth;
}; // class Inference

/**
 * Inferences with no premise
 */
class Inference0
  : public Inference
{
public:
  Inference0(Rule rule) : Inference(rule)
  {
    computeTheoryRunningSums();

    _isPureTheoryDescendant = isTheoryAxiom();

    //_inductionDepth = 0 from Inference::Inference (or set externally)
  }

  /* Inference0 does not update (it does not have parents anyway).
  * So if any of Inference0's statistics have been set externally during
  * proof search, update statistics won't reset these "hacky" values.
  * (C.f., inductionDepth assigned in AVATAR to AVATAR_DEFINITION
  * and thus later propagated to AVATAR_COMPONENT, AVATAR_SPLIT_CLAUSE, and transitively to AVATAR_REFUTATION,
  * and similarly inductionDepth assigned INDUCTION "hypothesis" formulas in Induction.)
  */
  void updateStatistics() {}

  virtual void destroy();
  virtual Iterator iterator() const;
  virtual bool hasNext(Iterator& it) const;
  virtual Unit* next(Iterator& it) const;

  CLASS_NAME(Inference0);
  USE_ALLOCATOR(Inference0);
};

/**
 * Inferences with a single premise
 * @since 07/04/2007 flight Manchester-Frankfurt
 */
class Inference1
  : public Inference
{
public:
  Inference1(Rule rule,Unit* premise)
    : Inference(rule),
      _premise1(premise)
  { 
    _premise1->incRefCnt(); 

    computeTheoryRunningSums();
    _isPureTheoryDescendant = _premise1->inference()->isPureTheoryDescendant();

    updateStatistics();
  }

  void updateStatistics()
  {
    CALL("Inference1::updateStatistics");

    _inductionDepth = _premise1->inference()->inductionDepth();
  }

  virtual void destroy();
  virtual Iterator iterator() const;
  virtual bool hasNext(Iterator& it) const;
  virtual Unit* next(Iterator& it) const;

  CLASS_NAME(Inference1);
  USE_ALLOCATOR(Inference1);

protected:
  /** The premise */
  Unit* _premise1;
};

/**
 * Inferences with two premises
 * @since 07/01/2008 Torrevieja
 */
class Inference2
  : public Inference
{
public:
  Inference2(Rule rule,Unit* premise1,Unit* premise2)
    : Inference(rule),
      _premise1(premise1),
      _premise2(premise2)
  {
    _premise1->incRefCnt();
    _premise2->incRefCnt();

    computeTheoryRunningSums();
    _isPureTheoryDescendant = _premise1->inference()->isPureTheoryDescendant() && _premise2->inference()->isPureTheoryDescendant();

    updateStatistics();
  }

  void updateStatistics()
  {
    CALL("Inference2::updateStatistics");

    _inductionDepth = max(_premise1->inference()->inductionDepth(),_premise2->inference()->inductionDepth());
  }

  virtual void destroy();
  virtual Iterator iterator() const;
  virtual bool hasNext(Iterator& it) const;
  virtual Unit* next(Iterator& it) const;

  CLASS_NAME(Inference2);
  USE_ALLOCATOR(Inference2);

protected:
  /** First premise */
  Unit* _premise1;
  /** Second premise */
  Unit* _premise2;
};

/**
 * Inferences with a list of premises
 * @since 07/07/2007 Manchester
 */
class InferenceMany
  : public Inference
{
public:
  InferenceMany(Rule rule,UnitList* premises);
  virtual ~InferenceMany() { UnitList::destroy(_premises); }

  virtual void destroy();
  virtual Iterator iterator() const;
  virtual bool hasNext(Iterator& it) const;
  virtual Unit* next(Iterator& it) const;

  CLASS_NAME(InferenceMany);
  USE_ALLOCATOR(InferenceMany);

  void updateStatistics();

protected:
  /** The premises */
  UnitList* _premises;
};

}
#endif

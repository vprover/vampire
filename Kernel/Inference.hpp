
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
   * Destroy the Inference object and decrease reference
   * counters in refered clauses.
   */
  virtual void destroy();
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

  virtual Iterator iterator();
  virtual bool hasNext(Iterator& it);
  virtual Unit* next(Iterator& it);

  /** Return the inference rule */
  Rule rule() const { return _rule; }

  /** Set extra string */
  void setExtra(vstring e){ _extra=e; }
  /** Return the extra string */
  vstring extra() { return _extra; }

  unsigned maxDepth(){ return _maxDepth; }

protected:
  /** The rule used */
  Rule _rule;
  /** Extra information */
  vstring _extra;
  /** The depth */
  unsigned _maxDepth;
}; // class Inference

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
    _maxDepth = premise->inference()->maxDepth()+1; 
    if(_rule == EVALUATION){ _maxDepth = premise->inference()->maxDepth(); }
  }

  virtual void destroy();
  virtual Iterator iterator();
  virtual bool hasNext(Iterator& it);
  virtual Unit* next(Iterator& it);

  CLASS_NAME(Inference1);
  USE_ALLOCATOR(Inference1);

protected:
  /** The premise */
  Unit* _premise1;
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
  virtual Iterator iterator();
  virtual bool hasNext(Iterator& it);
  virtual Unit* next(Iterator& it);

  CLASS_NAME(InferenceMany);
  USE_ALLOCATOR(InferenceMany);

protected:
  /** The premises */
  UnitList* _premises;
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
    _maxDepth = max(premise1->inference()->maxDepth(),premise2->inference()->maxDepth())+1;
  }

  virtual void destroy();
  virtual Iterator iterator();
  virtual bool hasNext(Iterator& it);
  virtual Unit* next(Iterator& it);

  CLASS_NAME(Inference2);
  USE_ALLOCATOR(Inference2);

protected:
  /** First premise */
  Unit* _premise1;
  /** Second premise */
  Unit* _premise2;
};


}
#endif

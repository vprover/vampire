/**
 * @file Inference.hpp
 * Defines class Inference for various kinds of inference
 *
 * @since 10/05/2007 Manchester
 */

#ifndef __Inference__
#define __Inference__

#include <cstdlib>
#include <string>

#include "Kernel/Unit.hpp"
#include "Lib/Allocator.hpp"

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
    /** obtained by expansion of the formula if-then-else connective */
    FORMULA_ITE_EXPANSION,
    /** a definition introduced for the term if-then-else operator */
    TERM_ITE_DEFINITION,
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
    /** obtain a clause from a clause by removing duplicate literals */
    REMOVE_DUPLICATE_LITERALS,
//     /** shell clause transformed to a resolution clause */
//     SHELL_TO_RESOLUTION,
    /** resolution inference */
    RESOLUTION,
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
    /** subsumption resolution simplification rule */
    SUBSUMPTION_RESOLUTION,
    /** superposition inference */
    SUPERPOSITION,
    /** equality factoring inference */
    EQUALITY_FACTORING,
    /** equality resolution inference */
    EQUALITY_RESOLUTION,
    /** forward demodulation inference */
    FORWARD_DEMODULATION,
    /** backward demodulation inference */
    BACKWARD_DEMODULATION,
    /** forward literal rewriting inference */
    FORWARD_LITERAL_REWRITING,
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
    /** any added theory axioms */
    THEORY,
    /** Introduction of formula to convert formulas used as argument positions.
     *  Such formulas have the form F->f(x)=1 or ~F->f(x)=0 */
    BOOLEAN_TERM_ENCODING,
    /** Introduction of definitions to handle the term <i>if F then s else t</i>
     *  Such formulas have the form F->f(x)=s or ~F->f(x)=t */
    TERM_IF_THEN_ELSE_DEFINITION,
    /** Elimination of if-then-else and let...in special terms and let...in
     * formula connectives */
    SPECIAL_TERM_ELIMINATION,
    /** splitting */
    SPLITTING,
    /** component introduced by splitting */
    SPLITTING_COMPONENT,
    /** component introduced by backtracking splitting */
    BACKTRACKING_SPLITTING_COMPONENT,
    /** refutation of a backtracking splitting branch */
    BACKTRACKING_SPLIT_REFUTATION,
    /** component introduced by backtracking splitting */
    SAT_SPLITTING_COMPONENT,
    /** refutation of a backtracking splitting branch */
    SAT_SPLITTING_REFUTATION,
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
    /** anything generated by program analysis */
    PROGRAM_ANALYSIS,
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

  static string ruleName(Rule rule);
  string name() const { return ruleName(_rule); }

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

protected:
  /** The rule used */
  Rule _rule;
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
  { _premise1->incRefCnt(); }

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
  virtual ~InferenceMany() { _premises->destroy(); }

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

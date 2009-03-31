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

#include "../Kernel/Unit.hpp"
#include "../Lib/Allocator.hpp"

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
   * Consecutive numbering is important since arrays are used
   * to store the names of the rules.
   */
  enum Rule {
    /** input formula or clause */
    INPUT = 0u,
    /** negated conjecture from the input */
    NEGATED_CONJECTURE = 1u,
//     /** choice_axiom (Ax)((Ey)F(x,y) -> F(x,f(x))) */
//     CHOICE_AXIOM = 2u,
//     /** (Ax)(F(x)->F'(x)), G[F(t)] / G[F'(t)] */
//     MONOTONE_REPLACEMENT = 3u,
//     /** G[(Ax)F(x)] => G[F(t)] */
//     FORALL_ELIMINATION = 4u,
    /** rectify a formula */
    RECTIFY = 5u,
//     /** ~(F1 & ... & Fn) => ~F1 \/ ... \/ ~Fn */
//     NOT_AND = 6u,
//     /** ~(F1 \/ ... \/ Fn) => ~F1 & ... & ~Fn */
//     NOT_OR = 7u,
//     /** ~(F1 -> F2) => F1 & ~F2 */
//     NOT_IMP = 8u,
//     /** ~(F1 <-> F2) => F1 <~> F2 */
//     NOT_IFF = 9u,
//     /** ~(F1 <~> F2) => F1 <-> F2 */
//     NOT_XOR = 10u,
//     /** ~~F => F */
//     NOT_NOT = 11u,
//     /** ~(Ax)F => (Ex)~F */
//     NOT_FORALL = 12u,
//     /** ~(Ex)F => (Ax)~F */
//     NOT_EXISTS = 13u,
//     /** F1 -> F2 => ~F1 \/ F2 */
//     IMP_TO_OR = 14u,
//     /** F1 <-> F2 => (F1 -> F2) & (F2 -> F1) */
//     IFF_TO_AND = 15u,
//     /** F1 <~> F2 => (F1 \/ F2) & (~F1 \/ ~F2) */
//     XOR_TO_AND = 16u,
    /** replace formula F by (A x1...xn)F, where x1 ... xn are all
     *  free variables of F */
    CLOSURE = 17u,
    /** obtained by flattening (quantifiers, junctions) */
    FLATTEN = 18u,
    /** obtained by reordering literals */
    REORDER_LITERALS = 19u,
    /** obtained by transformation into ENNF */
    ENNF = 20u,
    /** obtained by transformation into NNF */
    NNF = 21u,
//     /** Replace formula (Q x1 ... xk ... x_n)A by
//      * (Q x1 ... xk-1 xk+1 ... x_n)A, where xk does not occur in A */
//     DUMMY_QUANTIFIER_REMOVAL = 22u,
//     /** Transformation (A x1 ... xn)(F1 & ... & Fm) ->
//      * (A x1 ... xn)F1 & ... & (A x1 ... xn)Fm) */
//     FORALL_AND = 23u,
//     /** Transformation (E x1 ... xn)(F1 \/ ... \/ Fm) ->
//      * (E x1 ... xn)F1 \/ ... \/ (E x1 ... xn)Fm) */
//     EXISTS_OR = 24u,
//     /** (Q x)(Q y)F -> (Q y)(Q x)F */
//     QUANTIFIER_SWAP = 25,
//     /** Transformation (A x1 x2)(F1 \/ F2) ->
//      * (A x1)F1 \/ ... \/ (A x2)F2), where x2 does not occur in F1.
//      * Can be applied to many variables and disjunctions of arbitrary length */
//     FORALL_OR = 26u,
//     /** Transformation (E x1 x2)(F1 & F2) ->
//      * (E x1)F1 & ... & (E x2)F2), where x2 does not occur in F1.
//      * Can be applied to many variables and disjunctions of arbitrary length */
//     EXISTS_AND = 27u,
//     /** obtained by permutations, e.g. f <=> g replaced by g <=> f */
//     PERMUT = 28u,
//     /** obtained by reordering equalities */
//     REORDER_EQ = 29u,
//     /** obtained by rewriting a positive equivalence
//      * f <=> ginto an implication f => g or g => f
//      */
//     HALF_EQUIV = 30u,
//     /** miniscoping */
//     MINISCOPE = 31u,
    /** skolemization */
    SKOLEMIZE = 32u,
    /** obtain clause from a formula */
    CLAUSIFY = 33u,
    /** obtain a clause from a clause by removing duplicate literals */
    REMOVE_DUPLICATE_LITERALS = 34u,
//     /** shell clause transformed to a resolution clause */
//     SHELL_TO_RESOLUTION = 35u,
    /** resolution inference */
    RESOLUTION = 36u,
//     /** equality proxy replacement */
//     EQUALITY_PROXY_REPLACEMENT = 37u,
//     /** equality proxy axiom E(x,x) */
//     EQUALITY_PROXY_AXIOM1 = 38u,
//     /** equality proxy axiom ~E(x,y) \/ x=y */
//     EQUALITY_PROXY_AXIOM2 = 39u,
//     /** unfolding by definitions f(x1,...,xn)=t */
//     DEFINITION_UNFOLDING = 40u,
    /** any kind of definition folding */
    DEFINITION_FOLDING = 41u,
//     /** expansion of row variable, KIF-specific */
//     ROW_VARIABLE_EXPANSION = 42u,
    /** introduction of new name p, p <=> C */
    PREDICATE_DEFINITION = 43u,
    /** reduce a formula containing false or true, for example
     *  false & A ---> false */
    REDUCE_FALSE_TRUE = 44u,
    /** remove from clause one or more inequalities <i>s != s</i> */
    TRIVIAL_INEQUALITY_REMOVAL = 45u,
    /** factoring inference */
    FACTORING = 46u,
    /** subsumption resolution simplification rule */
    SUBSUMPTION_RESOLUTION = 47u,
    /** superposition inference */
    SUPERPOSITION = 48u,
    /** equality factoring inference */
    EQUALITY_FACTORING = 49u,
    /** equality resolution inference */
    EQUALITY_RESOLUTION = 50u,
    /** forward demodulation inference */
    FORWARD_DEMODULATION = 51u,
    /** backward demodulation inference */
    BACKWARD_DEMODULATION = 52u,
    /** condensation inference */
    CONDENSATION = 53u,
    /** evaluation inference */
    EVALUATION = 54u

  }; // class Inference::Rule

  explicit Inference(Rule r)
    : _rule(r)
  {
  }

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
  string name() const;

  CLASS_NAME("Inference");
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

  CLASS_NAME("Inference1");
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

  CLASS_NAME("InferenceMany");
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

  CLASS_NAME("Inference2");
  USE_ALLOCATOR(Inference2);

protected:
  /** First premise */
  Unit* _premise1;
  /** Second premise */
  Unit* _premise2;
};


}
#endif


/*
 * File Inference.cpp.
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
 * @file Inference.cpp
 * Implements class Inference for various kinds of inference.
 *
 * @since 19/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"
#include "Kernel/Term.hpp"

#include "Inference.hpp"

using namespace Kernel;


/**
 * Return InputType of which should be a formula that has
 * units of types @c t1 and @c t2 as premises.
 */
Inference::InputType Inference::getInputType(InputType t1, InputType t2)
{
  CALL("Unit::getInputType");

  return static_cast<Inference::InputType>(std::max(toNumber(t1), toNumber(t2)));
}

/**
 * Return InputType of which should be a formula that has
 * @c units as premises.
 *
 * @c units must be a non-empty list.
 */
Inference::InputType Inference::getInputType(UnitList* units)
{
  CALL("Unit::getInputType");
  ASS(units);

  UnitList::Iterator uit(units);
  ALWAYS(uit.hasNext());
  InputType res = uit.next()->inference()->inputType();

  while(uit.hasNext()) {
    res = getInputType(res, uit.next()->inference()->inputType());
  }
  return res;
}

Inference::Inference(InputType inputType, Rule r) :
    _inputType(inputType), _rule(r),
    _inductionDepth(0),
    _sineLevel(std::numeric_limits<decltype(_sineLevel)>::max()),
    _splits(nullptr) {}

/**
 * Create an inference object with multiple premises
 */
InferenceMany::InferenceMany(Rule rule,UnitList* premises)
  : Inference(InputType::AXIOM /* the minimal element; we later compute maximum over premises*/,rule),
    _premises(premises)
{
  CALL("InferenceMany::InferenceMany");

  UnitList* it=_premises;
  while(it) {
    it->head()->incRefCnt();
    it=it->tail();
  }

  computeTheoryRunningSums();

  if (_premises) {
    _isPureTheoryDescendant = true;
    it=_premises;
    while(it) {
      Inference* inf = it->head()->inference();
      _inputType = getInputType(_inputType,inf->inputType());
      _isPureTheoryDescendant &= inf->isPureTheoryDescendant();
      _sineLevel = min(_sineLevel,it->head()->inference()->getSineLevel());
      it=it->tail();
    }
  } else {
    _isPureTheoryDescendant = isTheoryAxiom();
  }

  updateStatistics();
}

void InferenceMany::updateStatistics()
{
  CALL("InferenceMany::updateRunningStatistics");

  _inductionDepth = 0;
  UnitList*  it=_premises;
  while(it) {
    Inference* inf = it->head()->inference();
    _inductionDepth = max(_inductionDepth,inf->inductionDepth());
    it=it->tail();
  }
}

/**
 * Destroy an inference with no premises.
 * @since 04/01/2008 Torrevieja
 */
void Inference0::destroy()
{
  CALL ("Inference::destroy");
  delete this;
}

/**
 * Destroy an inference with a single premise.
 * @since 04/01/2008 Torrevieja
 */
void Inference1::destroy()
{
  CALL ("Inference1::destroy");
  _premise1->decRefCnt();
  delete this;
}

/**
 * Destroy an inference with two premises.
 * @since 07/01/2008 Torrevieja
 */
void Inference2::destroy()
{
  CALL ("Inference2::destroy");
  _premise1->decRefCnt();
  _premise2->decRefCnt();
  delete this;
}

/**
 * Destroy an inference with many premises.
 * @since 04/01/2008 Torrevieja
 */
void InferenceMany::destroy()
{
  CALL ("InferenceMany::destroy");
  UnitList* it=_premises;
  while(it) {
    it->head()->decRefCnt();
    it=it->tail();
  }

  delete this;
}

/**
 * Return an iterator for an inference with zero premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference0::iterator() const
{
  Iterator it;
#if VDEBUG
  it.integer=0;
#endif
  return it;
}

/**
 * Return an iterator for an inference with one premise.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference1::iterator() const
{
  Iterator it;
  it.integer = 1;
  return it;
}

/**
 * Return an iterator for an inference with two premises.
 * @since 07/01/2008 Torrevieja
 */
Inference::Iterator Inference2::iterator() const
{
  Iterator it;
  it.integer = 0;
  return it;
}

/**
 * Return an iterator for an inference with many premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator InferenceMany::iterator() const
{
  Iterator it;
  it.pointer = _premises;
  return it;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool Inference0::hasNext(Iterator&) const
{
  return false;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool Inference1::hasNext(Iterator& it) const
{
  return it.integer;
}

/**
 * True if there exists the next parent.
 * @since 07/01/2008 Torrevieja
 */
bool Inference2::hasNext(Iterator& it) const
{
  return it.integer < 2;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool InferenceMany::hasNext(Iterator& it) const
{
  return it.pointer;
}

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* Inference0::next(Iterator&) const
{
#if VDEBUG
  ASSERTION_VIOLATION;
#endif
  return 0;
} // Inference::next

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* Inference1::next(Iterator& it) const
{
  ASS(it.integer);
  it.integer = 0;
  return _premise1;
} // InferenceMany::next

/**
 * Return the next parent.
 * @since 07/01/2008 Torrevieja
 */
Unit* Inference2::next(Iterator& it) const
{
  ASS(it.integer >= 0);
  ASS(it.integer < 2);
  return it.integer++ ? _premise2 : _premise1;
} // InferenceMany::next

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* InferenceMany::next(Iterator& it) const
{
  ASS(it.pointer);
  UnitList* lst = reinterpret_cast<UnitList*>(it.pointer);
  it.pointer = lst->tail();
  return lst->head();
} // InferenceMany::next

/**
 * Return the rule name, such as "binary resolution".
 * @since 04/01/2008 Torrevieja
 */
vstring Inference::ruleName(Rule rule)
{
  CALL("Inference::ruleName");

  switch (rule) {
  case Rule::INPUT:
    return "input";
  case Rule::NEGATED_CONJECTURE:
    return "negated conjecture";
  case Rule::ANSWER_LITERAL:
    return "answer literal";
  case Rule::RECTIFY:
    return "rectify";
  case Rule::CLOSURE:
    return "closure";
  case Rule::FLATTEN:
    return "flattening";
  case Rule::FOOL_ELIMINATION:
    return "fool elimination";
  case Rule::FOOL_ITE_ELIMINATION:
    return "fool $ite elimination";
  case Rule::FOOL_LET_ELIMINATION:
    return "fool $let elimination";
  case Rule::FOOL_PARAMODULATION:
    return "fool paramodulation";
//  case CHOICE_AXIOM:
//  case MONOTONE_REPLACEMENT:
//  case FORALL_ELIMINATION:
//  case NOT_AND:
//  case NOT_OR:
//  case NOT_IMP:
//  case NOT_IFF:
//  case NOT_XOR:
//  case NOT_NOT:
//  case NOT_FORALL:
//  case NOT_EXISTS:
//  case IMP_TO_OR:
//  case IFF_TO_AND:
//  case XOR_TO_AND:
  case Rule::REORDER_LITERALS:
    return "literal reordering";
  case Rule::ENNF:
    return "ennf transformation";
  case Rule::NNF:
    return "nnf transformation";
//  case DUMMY_QUANTIFIER_REMOVAL:
//  case FORALL_AND:
//  case EXISTS_OR:
//  case QUANTIFIER_SWAP:
//  case FORALL_OR:
//  case EXISTS_AND:
//  case PERMUT:
//  case REORDER_EQ:
//  case HALF_EQUIV:
//  case MINISCOPE:
  case Rule::CLAUSIFY:
    return "cnf transformation";
  case Rule::FORMULIFY:
    return "formulify";
  case Rule::REMOVE_DUPLICATE_LITERALS:
    return "duplicate literal removal";
  case Rule::SKOLEMIZE:
    return "skolemisation";
  case Rule::RESOLUTION:
    return "resolution";
  case Rule::CONSTRAINED_RESOLUTION:
    return "constrained resolution";
  case Rule::EQUALITY_PROXY_REPLACEMENT:
    return "equality proxy replacement";
  case Rule::EQUALITY_PROXY_AXIOM1:
    return "equality proxy definition";
  case Rule::EQUALITY_PROXY_AXIOM2:
    return "equality proxy axiom";
  case Rule::EXTENSIONALITY_RESOLUTION:
    return "extensionality resolution";
  case Rule::DEFINITION_UNFOLDING:
    return "definition unfolding";
  case Rule::DEFINITION_FOLDING:
    return "definition folding";
  case Rule::PREDICATE_DEFINITION:
    return "predicate definition introduction";
  case Rule::PREDICATE_DEFINITION_UNFOLDING:
    return "predicate definition unfolding";
  case Rule::PREDICATE_DEFINITION_MERGING:
    return "predicate definition merging";
  case Rule::REDUCE_FALSE_TRUE:
    return "true and false elimination";

  case Rule::TRIVIAL_INEQUALITY_REMOVAL:
    return "trivial inequality removal";
  case Rule::FACTORING:
    return "factoring";
  case Rule::CONSTRAINED_FACTORING:
    return "constrained factoring";
  case Rule::SUBSUMPTION_RESOLUTION:
    return "subsumption resolution";
  case Rule::SUPERPOSITION:
    return "superposition";
  case Rule::CONSTRAINED_SUPERPOSITION:
    return "constrained superposition";
  case Rule::EQUALITY_FACTORING:
    return "equality factoring";
  case Rule::EQUALITY_RESOLUTION:
    return "equality resolution";
  case Rule::FORWARD_DEMODULATION:
    return "forward demodulation";
  case Rule::BACKWARD_DEMODULATION:
    return "backward demodulation";
  case Rule::FORWARD_LITERAL_REWRITING:
    return "forward literal rewriting";
  case Rule::INNER_REWRITING:
    return "inner rewriting";
  case Rule::CONDENSATION:
    return "condensation";
  case Rule::THEORY_NORMALIZATION:
    return "theory normalization";
  case Rule::EVALUATION:
    return "evaluation";
  case Rule::INTERPRETED_SIMPLIFICATION:
    return "interpreted simplification";
  case Rule::UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "unused predicate definition removal";
  case Rule::PURE_PREDICATE_REMOVAL:
    return "pure predicate removal";
  case Rule::INEQUALITY_SPLITTING:
    return "inequality splitting";
  case Rule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    return "inequality splitting name introduction";
  case Rule::GROUNDING:
    return "grounding";
  case Rule::EQUALITY_AXIOM:
    return "equality axiom";
  case Rule::CHOICE_AXIOM:
    return "choice axiom";
  case Rule::SAT_CONFLICT_CLAUSE:
    return "sat conflict clause";
  case Rule::SIMPLIFY_PROVER_DISTINCT_NUMBERS_AXIOM:
    return "distinct numbers";
  case Rule::GENERIC_THEORY_AXIOM:
  case Rule::THEORY_AXIOM_COMMUTATIVITY:
  case Rule::THEORY_AXIOM_ASSOCIATIVITY:
  case Rule::THEORY_AXIOM_RIGHT_IDENTINTY:
  case Rule::THEORY_AXIOM_LEFT_IDENTINTY:
  case Rule::THEORY_AXIOM_INVERSE_OP_OP_INVERSES:
  case Rule::THEORY_AXIOM_INVERSE_OP_UNIT:
  case Rule::THEORY_AXIOM_INVERSE_ASSOC:
  case Rule::THEORY_AXIOM_NONREFLEX:
  case Rule::THEORY_AXIOM_TRANSITIVITY:
  case Rule::THEORY_AXIOM_ORDER_TOTALALITY:
  case Rule::THEORY_AXIOM_ORDER_MONOTONICITY:
  case Rule::THEORY_AXIOM_PLUS_ONE_GREATER:
  case Rule::THEORY_AXIOM_ORDER_PLUS_ONE_DICHOTOMY:
  case Rule::THEORY_AXIOM_MINUS_MINUS_X:
  case Rule::THEORY_AXIOM_TIMES_ZERO:
  case Rule::THEORY_AXIOM_DISTRIBUTIVITY:
  case Rule::THEORY_AXIOM_DIVISIBILITY:
  case Rule::THEORY_AXIOM_MODULO_MULTIPLY:
  case Rule::THEORY_AXIOM_MODULO_POSITIVE:
  case Rule::THEORY_AXIOM_MODULO_SMALL:
  case Rule::THEORY_AXIOM_DIVIDES_MULTIPLY:
  case Rule::THEORY_AXIOM_NONDIVIDES_SKOLEM:
  case Rule::THEORY_AXIOM_ABS_EQUALS:
  case Rule::THEORY_AXIOM_ABS_MINUS_EQUALS:
  case Rule::THEORY_AXIOM_QUOTIENT_NON_ZERO:
  case Rule::THEORY_AXIOM_QUOTIENT_MULTIPLY:
  case Rule::THEORY_AXIOM_EXTRA_INTEGER_ORDERING:
  case Rule::THEORY_AXIOM_FLOOR_SMALL:
  case Rule::THEORY_AXIOM_FLOOR_BIG:
  case Rule::THEORY_AXIOM_CEILING_BIG:
  case Rule::THEORY_AXIOM_CEILING_SMALL:
  case Rule::THEORY_AXIOM_TRUNC1:
  case Rule::THEORY_AXIOM_TRUNC2:
  case Rule::THEORY_AXIOM_TRUNC3:
  case Rule::THEORY_AXIOM_TRUNC4:
  case Rule::THEORY_AXIOM_ARRAY_EXTENSIONALITY:
  case Rule::THEORY_AXIOM_BOOLEAN_ARRAY_EXTENSIONALITY:
  case Rule::THEORY_AXIOM_BOOLEAN_ARRAY_WRITE1:
  case Rule::THEORY_AXIOM_BOOLEAN_ARRAY_WRITE2:
  case Rule::THEORY_AXIOM_ARRAY_WRITE1:
  case Rule::THEORY_AXIOM_ARRAY_WRITE2:
    return "theory axiom";
  case Rule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    return "term algebras acyclicity";
  case Rule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    return "term algebras discriminators";
  case Rule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    return "term algebras distinctness";
  case Rule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    return "term algebras exhaustiveness";
  case Rule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    return "term algebras injectivity";
  case Rule::FOOL_AXIOM_TRUE_NEQ_FALSE:
  case Rule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
    return "fool axiom";
  case Rule::EXTERNAL_THEORY_AXIOM:
    return "external theory axiom";
  case Rule::TERM_ALGEBRA_ACYCLICITY:
    return "term algebras acyclicity";
  case Rule::TERM_ALGEBRA_DISTINCTNESS:
    return "term algebras distinctness";
  case Rule::TERM_ALGEBRA_INJECTIVITY_GENERATING:
  case Rule::TERM_ALGEBRA_INJECTIVITY_SIMPLIFYING:
    return "term algebras injectivity";
  case Rule::THEORY_FLATTENING:
    return "theory flattening";
  case Rule::BOOLEAN_TERM_ENCODING:
    return "boolean term encoding";
  case Rule::AVATAR_DEFINITION:
    return "avatar definition";
  case Rule::AVATAR_COMPONENT:
    return "avatar component clause";
  case Rule::AVATAR_REFUTATION:
    return "avatar sat refutation";
  case Rule::AVATAR_SPLIT_CLAUSE:
    return "avatar split clause";
  case Rule::AVATAR_CONTRADICTION_CLAUSE:
    return "avatar contradiction clause";
  case Rule::SAT_COLOR_ELIMINATION:
    return "sat color elimination";
  case Rule::GENERAL_SPLITTING_COMPONENT:
    return "general splitting component introduction";
  case Rule::GENERAL_SPLITTING:
    return "general splitting";


  case Rule::COLOR_UNBLOCKING:
    return "color unblocking";
  case Rule::INSTANCE_GENERATION:
    return "instance generation";
  case Rule::UNIT_RESULTING_RESOLUTION:
    return "unit resulting resolution";
  case Rule::HYPER_SUPERPOSITION_SIMPLIFYING:
  case Rule::HYPER_SUPERPOSITION_GENERATING:
    return "hyper superposition";
  case Rule::GLOBAL_SUBSUMPTION:
    return "global subsumption";
  case Rule::SAT_INSTGEN_REFUTATION:
    return "sat instgen refutation";
  case Rule::DISTINCT_EQUALITY_REMOVAL:
    return "distinct equality removal";
  case Rule::EXTERNAL:
    return "external";
  case Rule::CLAIM_DEFINITION:
    return "claim definition";
  case Rule::BFNT_FLATTENING:
    return "bfnt flattening";
  case Rule::BFNT_DISTINCT:
    return "bfnt distinct";
  case Rule::BFNT_TOTALITY:
    return "bfnt totality";
  case Rule::FMB_FLATTENING:
    return "flattening (finite model building)";
  case Rule::FMB_FUNC_DEF:
    return "functional definition (finite model building)";
  case Rule::FMB_DEF_INTRO:
    return "definition introduction (finite model building)";
  case Rule::ADD_SORT_PREDICATES:
    return "add sort predicates";
  case Rule::ADD_SORT_FUNCTIONS:
    return "add sort functions";
  case Rule::INSTANTIATION:
    return "instantiation";
  case Rule::MODEL_NOT_FOUND:
    return "finite model not found";
  case Rule::INDUCTION_AXIOM:
    return "induction hypothesis";
  default:
    ASSERTION_VIOLATION;
    return "!UNKNOWN INFERENCE RULE!";
  }
} // Inference::name()



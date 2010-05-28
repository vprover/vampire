/**
 * @file Inference.cpp
 * Implements class Inference for various kinds of inference.
 *
 * @since 19/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Inference.hpp"

using namespace Kernel;

Inference::Inference(Rule r)
  : _rule(r)
{
  switch(r) {
  //TODO: move env.statistics object updates here.
  default: ;
  }
}


/**
 * Destroy an inference with no premises.
 * @since 04/01/2008 Torrevieja
 */
void Inference::destroy()
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
 * Create an inference object with multiple premisses
 */
InferenceMany::InferenceMany(Rule rule,UnitList* premises)
  : Inference(rule),
    _premises(premises)
{
  UnitList* it=_premises;
  while(it) {
    it->head()->incRefCnt();
    it=it->tail();
  }
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
 * Return an iterator for an inference with many premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator InferenceMany::iterator()
{
  Iterator it;
  it.pointer = _premises;
  return it;
}

/**
 * Return an iterator for an inference with one premise.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference1::iterator()
{
  Iterator it;
  it.integer = 1;
  return it;
}

/**
 * Return an iterator for an inference with two premises.
 * @since 07/01/2008 Torrevieja
 */
Inference::Iterator Inference2::iterator()
{
  Iterator it;
  it.integer = 0;
  return it;
}

/**
 * Return an iterator for an inference with zero premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference::iterator()
{
  Iterator it;
#if VDEBUG
  it.integer=0;
#endif
  return it;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool InferenceMany::hasNext(Iterator& it)
{
  return it.pointer;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool Inference1::hasNext(Iterator& it)
{
  return it.integer;
}

/**
 * True if there exists the next parent.
 * @since 07/01/2008 Torrevieja
 */
bool Inference2::hasNext(Iterator& it)
{
  return it.integer < 2;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool Inference::hasNext(Iterator&)
{
  return false;
}

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* InferenceMany::next(Iterator& it)
{
  ASS(it.pointer);
  UnitList* lst = reinterpret_cast<UnitList*>(it.pointer);
  it.pointer = lst->tail();
  return lst->head();
} // InferenceMany::next

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* Inference1::next(Iterator& it)
{
  ASS(it.integer);
  it.integer = 0;
  return _premise1;
} // InferenceMany::next

/**
 * Return the next parent.
 * @since 07/01/2008 Torrevieja
 */
Unit* Inference2::next(Iterator& it)
{
  ASS(it.integer >= 0);
  ASS(it.integer < 2);
  return it.integer++ ? _premise2 : _premise1;
} // InferenceMany::next

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* Inference::next(Iterator&)
{
#if VDEBUG
  ASSERTION_VIOLATION;
#endif
  return 0;
} // Inference::next



/**
 * Return the rule name, such as "binary resolution".
 * @since 04/01/2008 Torrevieja
 */
string Inference::ruleName(Rule rule)
{
  CALL("Inference::ruleName");

  switch (rule) {
  case INPUT:
    return "input";
  case NEGATED_CONJECTURE:
    return "negated conjecture";
  case RECTIFY:
    return "rectify";
  case CLOSURE:
    return "closure";
  case FLATTEN:
    return "flattening";
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
  case REORDER_LITERALS:
    return "literal reordering";
  case ENNF:
    return "ennf transformation";
  case NNF:
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
  case CLAUSIFY:
    return "CNF transformation";
  case REMOVE_DUPLICATE_LITERALS:
    return "duplicate literal removal";
  case SKOLEMIZE:
    return "skolemisation";
  case RESOLUTION:
    return "resolution";
  case EQUALITY_PROXY_REPLACEMENT:
    return "equality proxy replacement";
  case EQUALITY_PROXY_AXIOM1:
    return "equality proxy axiom E(x,x)";
  case EQUALITY_PROXY_AXIOM2:
    return "equality proxy axiom";
  case DEFINITION_UNFOLDING:
    return "definition unfolding";
  case DEFINITION_FOLDING:
    return "definition folding";
//  case ROW_VARIABLE_EXPANSION:
  case PREDICATE_DEFINITION:
    return "predicate definition introduction";
  case REDUCE_FALSE_TRUE:
    return "true and false elimination";
  case TRIVIAL_INEQUALITY_REMOVAL:
    return "trivial inequality removal";
  case FACTORING:
    return "factoring";
  case SUBSUMPTION_RESOLUTION:
    return "subsumption resolution";
  case SUPERPOSITION:
    return "superposition";
  case EQUALITY_FACTORING:
    return "equality factoring";
  case EQUALITY_RESOLUTION:
    return "equality resolution";
  case FORWARD_DEMODULATION:
    return "forward demodulation";
  case BACKWARD_DEMODULATION:
    return "backward demodulation";
  case FORWARD_LITERAL_REWRITING:
    return "forward literal rewriting";
  case CONDENSATION:
    return "condensation";
  case EVALUATION:
    return "evaluation";
  case INTERPRETED_SIMPLIFICATION:
    return "interpreted simplification";
  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "unused predicate definition removal";
  case PURE_PREDICATE_REMOVAL:
    return "pure predicate removal";
  case INEQUALITY_SPLITTING:
    return "inequality splitting";
  case INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    return "inequality splitting name introduction";
  case GROUNDING:
    return "grounding";
  case EQUALITY_AXIOM:
    return "equality axiom";
  case THEORY:
    return "theory axiom";
  case BOOLEAN_TERM_ENCODING:
    return "boolean term encoding";
  case TERM_IF_THEN_ELSE_DEFINITION:
    return "term if-then-else definition";
  case SPLITTING_COMPONENT:
    return "splitting component introduction";
  case SPLITTING:
    return "splitting";
  case BACKTRACKING_SPLITTING_COMPONENT:
    return "backtracking splitting";
  case BACKTRACKING_SPLIT_REFUTATION:
    return "backtracking split refutation";
  case COMMON_NONPROP_MERGE:
    return "merge";
  case PROP_REDUCE:
    return "prop reduce";
  case CLAUSE_NAMING:
    return "clause naming";
  case BDDZATION:
    return "bddzation";
  case TAUTOLOGY_INTRODUCTION:
    return "tautology introduction";

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Inference::name()




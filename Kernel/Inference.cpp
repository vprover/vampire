
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

Inference::Inference(Rule r)
  : _rule(r), _extra(""),_maxDepth(0)
{
//  switch(r) {
//  //TODO: move env.statistics object updates here.
//  default: ;
//  }
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
  CALL("InferenceMany::InferenceMany");
  UnitList* it=_premises;
  unsigned md = 0;
  while(it) {
    it->head()->incRefCnt();
    md = max(md,it->head()->inference()->maxDepth());
    it=it->tail();
  }
  _maxDepth = md+1;
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
vstring Inference::ruleName(Rule rule)
{
  CALL("Inference::ruleName");

  switch (rule) {
  case INPUT:
    return "input";
  case NEGATED_CONJECTURE:
    return "negated conjecture";
  case ANSWER_LITERAL:
    return "answer literal";
  case RECTIFY:
    return "rectify";
  case CLOSURE:
    return "closure";
  case FLATTEN:
    return "flattening";
  case FOOL_ELIMINATION:
    return "fool elimination";
  case FOOL_ITE_ELIMINATION:
    return "fool $ite elimination";
  case FOOL_LET_ELIMINATION:
    return "fool $let elimination";
  case FOOL_PARAMODULATION:
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
    return "cnf transformation";
  case FORMULIFY:
    return "formulify";
  case REMOVE_DUPLICATE_LITERALS:
    return "duplicate literal removal";
  case SKOLEMIZE:
    return "skolemisation";
  case RESOLUTION:
    return "resolution";
  case CONSTRAINED_RESOLUTION:
    return "constrained resolution";
  case EQUALITY_PROXY_REPLACEMENT:
    return "equality proxy replacement";
  case EQUALITY_PROXY_AXIOM1:
    return "equality proxy definition";
  case EQUALITY_PROXY_AXIOM2:
    return "equality proxy axiom";
  case EXTENSIONALITY_RESOLUTION:
    return "extensionality resolution";
  case DEFINITION_UNFOLDING:
    return "definition unfolding";
  case DEFINITION_FOLDING:
    return "definition folding";
  case SKOLEM_PREDICATE_INTRODUCTION:
  return "skolem predicate introduction";
  case PREDICATE_SKOLEMIZE:
    return "predicate skolemization";
//  case ROW_VARIABLE_EXPANSION:
  case PREDICATE_DEFINITION:
    return "predicate definition introduction";
  case PREDICATE_DEFINITION_UNFOLDING:
    return "predicate definition unfolding";
  case PREDICATE_DEFINITION_MERGING:
    return "predicate definition merging";
  case EQUIVALENCE_DISCOVERY:
    return "equivalence discovery";
  case FORMULA_SHARING:
    return "formula sharing";
  case REDUCE_FALSE_TRUE:
    return "true and false elimination";
  case LOCAL_SIMPLIFICATION:
    return "local simplification";
  case NORMALIZATION:
    return "normalization";
  case EQUALITY_PROPAGATION:
    return "equality propagation";
  case TRIVIAL_INEQUALITY_REMOVAL:
    return "trivial inequality removal";
  case FACTORING:
    return "factoring";
  case CONSTRAINED_FACTORING:
    return "constrained factoring";
  case SUBSUMPTION_RESOLUTION:
    return "subsumption resolution";
  case SUPERPOSITION:
    return "superposition";
  case CONSTRAINED_SUPERPOSITION:
    return "constrained superposition";
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
  case INNER_REWRITING:
    return "inner rewriting";
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
  case CHOICE_AXIOM:
    return "choice axiom";
  case THEORY:
    return "theory axiom";
  case FOOL_AXIOM:
    return "fool axiom";
  case THEORY_FLATTENING:
    return "theory flattening";
  case BOOLEAN_TERM_ENCODING:
    return "boolean term encoding";
  case AVATAR_DEFINITION:
    return "avatar definition";
  case AVATAR_COMPONENT:
    return "avatar component clause";
  case AVATAR_REFUTATION:
    return "avatar sat refutation";
  case AVATAR_SPLIT_CLAUSE:
    return "avatar split clause";
  case AVATAR_CONTRADICTION_CLAUSE:
    return "avatar contradiction clause";
  case SAT_COLOR_ELIMINATION:
    return "sat color elimination";
  case GENERAL_SPLITTING_COMPONENT:
    return "general splitting component introduction";
  case GENERAL_SPLITTING:
    return "general splitting";
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
  case COLOR_UNBLOCKING:
    return "color unblocking";
  case INSTANCE_GENERATION:
    return "instance generation";
  case UNIT_RESULTING_RESOLUTION:
    return "unit resulting resolution";
  case HYPER_SUPERPOSITION:
    return "hyper superposition";
  case GLOBAL_SUBSUMPTION:
    return "global subsumption";
  case SAT_INSTGEN_REFUTATION:
    return "sat instgen refutation";
  case DISTINCT_EQUALITY_REMOVAL:
    return "distinct equality removal";
  case TERM_ALGEBRA_EXHAUSTIVENESS:
    return "term algebras exhaustiveness";
  case TERM_ALGEBRA_DISTINCTNESS:
    return "term algebras distinctness";
  case TERM_ALGEBRA_INJECTIVITY:
    return "term algebras injectivity";
  case TERM_ALGEBRA_DISCRIMINATION:
    return "term algebras discriminators";
  case TERM_ALGEBRA_ACYCLICITY:
    return "term algebras acyclicity";
  case EXTERNAL:
    return "external";
  case CLAIM_DEFINITION:
    return "claim definition";
  case BFNT_FLATTENING:
    return "bfnt flattening";
  case BFNT_DISTINCT:
    return "bfnt distinct";
  case BFNT_TOTALITY:
    return "bfnt totality";
  case FMB_FLATTENING:
    return "flattening (finite model building)";
  case FMB_FUNC_DEF:
    return "functional definition (finite model building)";
  case FMB_DEF_INTRO:
    return "definition introduction (finite model building)";
  case ADD_SORT_PREDICATES:
    return "add sort predicates";
  case ADD_SORT_FUNCTIONS:
    return "add sort functions";
  case INSTANTIATION:
    return "instantiation";
  case MODEL_NOT_FOUND:
    return "finite model not found";
  case INDUCTION:
    return "induction hypothesis";
  case INDUCTIVE_STRENGTH:
    return "inductive strengthening";
  case COMBINATOR_AXIOM:
    return "combinator axiom";
  case FUNC_EXT_AXIOM:
    return "functional extensionality axiom";
  case EQUALITY_PROXY_AXIOM:
    return "equality proxy axiom";
  case NOT_PROXY_AXIOM:
    return "logical not proxy axiom";
  case AND_PROXY_AXIOM:
    return "logical and proxy axiom";
  case OR_PROXY_AXIOM:
    return "logical or proxy axiom";
  case IMPLIES_PROXY_AXIOM:
    return "implies proxy axiom";
  case PI_PROXY_AXIOM:
    return "pi proxy axiom";
  case SIGMA_PROXY_AXIOM:
    return "sigma proxy axiom";
  case ARG_CONG:
    return "argument congruence";
  case NARROW:
    return "narrow";
  case SUB_VAR_SUP:
    return "sub-var superposition";
  case COMBINATOR_DEMOD:
    return "combinator demodulation";
  case COMBINATOR_NORMALISE:
    return "combinator normalisation";  
  case NEGATIVE_EXT:
    return "negative extensionality";
  case INJECTIVITY:
    return "injectivity";
  case HOL_NOT_ELIMINATION:
    return "not proxy clausification";
  case BINARY_CONN_ELIMINATION:
    return "binary proxy clausification";
  case VSIGMA_ELIMINATION:
    return "sigma clausification";
  case VPI_ELIMINATION:
    return "pi clausification";
  case HOL_EQUALITY_ELIMINATION:
    return "equality proxy clausification";
  case BINARY_CONN_SHORT_CIRUCIT_EVAL:
    return "short circuit evaluation";
  default:
    ASSERTION_VIOLATION;
    return "!UNKNOWN INFERENCE RULE!";
  }
} // Inference::name()

bool Inference::positionIn(TermList& subterm,TermList* term,vstring& position)
{
  CALL("Inference::positionIn(TermList)");
   //cout << "positionIn " << subterm.toString() << " in " << term->toString() << endl;

  if(!term->isTerm()){
    if(subterm.isTerm()) return false;
    if (term->var()==subterm.var()){
      position = "1";
      return true;
    }
    return false;
  }
  return positionIn(subterm,term->term(),position);
}

bool Inference::positionIn(TermList& subterm,Term* term,vstring& position)
{
  CALL("Inference::positionIn(Term)");
  //cout << "positionIn " << subterm.toString() << " in " << term->toString() << endl;

  if(subterm.isTerm() && subterm.term()==term){
    position = "1";
    return true;
  }
  if(term->arity()==0) return false;

  unsigned pos=1;
  TermList* ts = term->args();
  while(true){
    if(*ts==subterm){
      position=Lib::Int::toString(pos); 
      return true;
    }
    if(positionIn(subterm,ts,position)){
      position = Lib::Int::toString(pos) + "." + position;
      return true;
    }
    pos++;
    ts = ts->next();
    if(ts->isEmpty()) break;
  }

  return false;
}


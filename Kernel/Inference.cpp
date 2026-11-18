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
 * @file Inference.cpp
 * Implements class Inference for various kinds of inference.
 *
 * @since 19/05/2007 Manchester
 */

#include "Lib/Environment.hpp"
#include "Kernel/Clause.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Inference.hpp"

using namespace std;
using namespace Kernel;


/**
 * A child is as close to the goal as its closest parent.
 */
GoalAffinity Kernel::childAffinity(GoalAffinity t1, GoalAffinity t2)
{
  return std::max(t1, t2);
}

/**
 * The binary childAffinity() folded over @c units, which must be a non-empty list.
 */
GoalAffinity Kernel::childAffinity(UnitList* units)
{
  ASS(units);

  UnitList::Iterator uit(units);
  ALWAYS(uit.hasNext());
  GoalAffinity res = uit.next()->goalAffinity();

  while(uit.hasNext()) {
    res = Kernel::childAffinity(res, uit.next()->goalAffinity());
  }
  return res;
}

/**
 * To be kept around in _ptr2 of INFERENCE_FROM_SAT_REFUTATION
 **/
struct NeedsMinimizationInfo {
  USE_ALLOCATOR(NeedsMinimizationInfo);

  NeedsMinimizationInfo(const NeedsMinimization& fsr) : _satPremises(fsr._satPremises), _usedAssumptions(fsr._usedAssumptions)
  { ASS(_satPremises); }

  SAT::SATClauseList* _satPremises;
  SAT::SATLiteralStack _usedAssumptions; // possibly an empty stack
};


void Inference::destroyDirectlyOwned()
{
  switch(_kind) {
    case Kind::SAT_NEEDS_MINIMIZATION:
      delete static_cast<NeedsMinimizationInfo*>(_ptr2);
      // intentionally fall further
    case Kind::SAT:
    case Kind::INFERENCE_MANY:
      UnitList::destroy(static_cast<UnitList*>(_ptr1));
    default:
      ;
  }
}

void Inference::destroy()
{
  switch(_kind) {
    case Kind::INFERENCE_012:
      if (_ptr1) static_cast<Unit*>(_ptr1)->decRefCnt();
      if (_ptr2) static_cast<Unit*>(_ptr2)->decRefCnt();
      break;
    case Kind::SAT:
      static_cast<SATClause *>(_ptr2)->destroy();
    case Kind::SAT_NEEDS_MINIMIZATION:
      delete static_cast<NeedsMinimizationInfo*>(_ptr2);
      // intentionally fall further
    case Kind::INFERENCE_MANY:
      UnitList* it=static_cast<UnitList*>(_ptr1);
      while(it) {
        it->head()->decRefCnt();
        it=it->tail();
      }

      UnitList::destroy(static_cast<UnitList*>(_ptr1));
      break;
  }
}

Inference::Inference(const NeedsMinimization& fsr) {
  initMany(fsr._rule,fsr._premises);

  ASS_REP(fsr._rule == InferenceRule::GLOBAL_SUBSUMPTION, ruleName(fsr._rule));

  _kind = Kind::SAT_NEEDS_MINIMIZATION;
  _ptr2 = new NeedsMinimizationInfo(fsr);
}

Inference::Inference(const InferenceOfASatClause& isc) {
  initMany(isc.rule, isc.premises);
  _kind = Kind::SAT;
  _ptr2 = isc.clause;
}

Inference::Inference(const ComponentClauseInference& cci) {
  initMany(cci.rule, cci.premises);
  _ptr2 = cci.causalParent;
}

/**
 * Return an iterator for an inference with zero premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference::iterator() const
{
  Iterator it;
  switch(_kind) {
    case Kind::INFERENCE_012:
      it.integer=0;
      break;
    case Kind::INFERENCE_MANY:
    case Kind::SAT:
    case Kind::SAT_NEEDS_MINIMIZATION:
      it.pointer = _ptr1;
      break;
  }

  return it;
}

/**
 * True if there exists the next parent.
 * @since 04/01/2008 Torrevieja
 */
bool Inference::hasNext(Iterator& it) const
{
  switch(_kind) {
    case Kind::INFERENCE_012:
      switch(it.integer) {
      case 0:
        return (_ptr1 != nullptr);
      case 1:
        return (_ptr2 != nullptr);
      case 2:
        return false;
      default:
        ASSERTION_VIOLATION;
        return false;
      }
      break;
    case Kind::INFERENCE_MANY:
    case Kind::SAT:
    case Kind::SAT_NEEDS_MINIMIZATION:
      return (it.pointer != nullptr);
    default:
      ASSERTION_VIOLATION;
  }
}

/**
 * Return the next parent.
 * @since 04/01/2008 Torrevieja
 */
Unit* Inference::next(Iterator& it) const
{
  switch(_kind) {
    case Kind::INFERENCE_012:
      switch(it.integer) {
      case 0:
        it.integer++;
        return static_cast<Unit*>(_ptr1);
      case 1:
        it.integer++;
        return static_cast<Unit*>(_ptr2);
      default:
        ASSERTION_VIOLATION;
        return nullptr;
      }
      break;
    case Kind::INFERENCE_MANY:
    case Kind::SAT:
    case Kind::SAT_NEEDS_MINIMIZATION: {
      UnitList* lst = static_cast<UnitList*>(it.pointer);
      it.pointer = lst->tail();
      return lst->head();
    }
    default:
      ASSERTION_VIOLATION;
      return nullptr;
  }
} // Inference::next

void Inference::updateStatistics()
{
  switch(_kind) {
    case Kind::INFERENCE_012:
      if (_ptr1 == nullptr) {
        /* Inference0 does not update (it does not have parents anyway).
        * So if any of Inference0's statistics have been set externally during
        * proof search, update statistics won't reset these "hacky" values.
        * (C.f., inductionDepth assigned in AVATAR to AVATAR_DEFINITION
        * and thus later propagated to AVATAR_COMPONENT, AVATAR_SPLIT_CLAUSE, and transitively to AVATAR_REFUTATION,
        * and similarly inductionDepth assigned to induction formulas in Induction.)
        */
      } else if (_ptr2 == nullptr) {
        _inductionDepth = static_cast<Unit*>(_ptr1)->inference().inductionDepth();
      } else {
        _inductionDepth = max(static_cast<Unit*>(_ptr1)->inference().inductionDepth(),
            static_cast<Unit*>(_ptr2)->inference().inductionDepth());
      }

      break;
    case Kind::INFERENCE_MANY:
    case Kind::SAT:
    case Kind::SAT_NEEDS_MINIMIZATION:
      _inductionDepth = 0;
      UnitList* it = static_cast<UnitList*>(_ptr1);
      while(it) {
        _inductionDepth = max(_inductionDepth,it->head()->inference().inductionDepth());
        it=it->tail();
      }
      break;
  }
}

std::ostream& Kernel::operator<<(std::ostream& out, Inference const& self)
{
  switch(self._kind) {
    case Inference::Kind::INFERENCE_012:
      out << "INFERENCE_012, (";
      break;
    case Inference::Kind::INFERENCE_MANY:
      out << "INFERENCE_MANY, (";
      break;
    case Inference::Kind::SAT:
      out << "SAT, (";
      break;
    case Inference::Kind::SAT_NEEDS_MINIMIZATION:
      out << "SAT_NEEDS_MINIMIZATION, (";
      break;
  }
  // TODO get rid of intermediate string generation by ruleName
  out << ruleName(self._rule);
  out << "), ga: " << self.goalAffinity();

  out << ", ptd: " << self._isPureTheoryDescendant;
  out << ", sl: " << self._sineLevel;
  out << ", age: " << self._age;
  return out;
}


void Inference::init0(GoalAffinity affinity, InferenceRule r)
{
  initDefault(affinity,r);
  _kind = Kind::INFERENCE_012;
  _ptr1 = nullptr;
  _ptr2 = nullptr;

  _isPureTheoryDescendant = isTheoryAxiom();

  //_inductionDepth = 0 from initDefault (or set externally)
  //_sineLevel = MAX from initDefault (or set externally)
}

void Inference::init1(InferenceRule r, Unit* premise)
{
  initDefault(premise->goalAffinity(),r);

  _kind = Kind::INFERENCE_012;
  _ptr1 = premise;
  _ptr2 = nullptr;

  premise->incRefCnt();

  _isPureTheoryDescendant = premise->isPureTheoryDescendant();
  _sineLevel = premise->getSineLevel();

  updateStatistics();
}

void Inference::init2(InferenceRule r, Unit* premise1, Unit* premise2)
{
  initDefault(childAffinity(premise1->goalAffinity(),premise2->goalAffinity()),r);

  _kind = Kind::INFERENCE_012;
  _ptr1 = premise1;
  _ptr2 = premise2;

  premise1->incRefCnt();
  premise2->incRefCnt();

  _isPureTheoryDescendant = premise1->isPureTheoryDescendant() && premise2->isPureTheoryDescendant();
  _sineLevel = min(premise1->getSineLevel(),premise2->getSineLevel());

  updateStatistics();
}

void Inference::initMany(InferenceRule r, UnitList* premises)
{
  initDefault(MIN_AFFINITY /* we later compute maximum over premises*/,r);

  _kind = Kind::INFERENCE_MANY;
  _ptr1 = premises;
  _ptr2 = nullptr;

  UnitList* it= premises;
  while(it) {
    it->head()->incRefCnt();
    it=it->tail();
  }

  if (premises) {
    _isPureTheoryDescendant = true;
    it=premises;
    while(it) {
      const Inference& inf = it->head()->inference();
      _goalAffinity = childAffinity(_goalAffinity,inf.goalAffinity());
      _isPureTheoryDescendant &= inf.isPureTheoryDescendant();
      _sineLevel = min(_sineLevel,inf.getSineLevel());
      it=it->tail();
    }
  } else {
    _isPureTheoryDescendant = isTheoryAxiom();
  }

  updateStatistics();
}

Inference::Inference(const FromInput& fi) {
  init0(fi.affinity,InferenceRule::INPUT);
}

Inference::Inference(const InputConjecture&) {
  init0(GoalAffinity::CONJECTURE,InferenceRule::INPUT_CONJECTURE);
}

Inference::Inference(const TheoryAxiom& ta) {
  init0(GoalAffinity::AXIOM,ta.rule);
  ASS_REP(isTheoryAxiom(), ruleName(ta.rule));
}

Inference::Inference(const FormulaClauseTransformation& ft) {
  init1(ft.rule,ft.premise);

  ASS_REP(isFormulaClauseTransformation(ft.rule),ruleName(ft.rule));
}

Inference::Inference(const FormulaClauseTransformationMany& ft) {
  initMany(ft.rule,ft.premises);

  ASS_REP(isFormulaClauseTransformation(ft.rule),ruleName(ft.rule));
  ASS_NEQ(ft.premises,UnitList::empty());
}

Inference::Inference(const GeneratingInference1& gi) {
  init1(gi.rule,gi.premise);

  ASS_REP(isGeneratingInferenceRule(gi.rule),ruleName(gi.rule));
  ASS(gi.premise->isClause());

  _age = gi.premise->age()+1;
}

Inference::Inference(const GeneratingInference2& gi) {
  init2(gi.rule,gi.premise1,gi.premise2);

  ASS_REP(isGeneratingInferenceRule(gi.rule),ruleName(gi.rule));
  ASS(gi.premise1->isClause());
  ASS(gi.premise2->isClause());

  _age = std::max(gi.premise1->age(),gi.premise2->age())+1;
}

Inference::Inference(const GeneratingInferenceMany& gi) {
  initMany(gi.rule,gi.premises);

  ASS_REP(isGeneratingInferenceRule(gi.rule),ruleName(gi.rule));
  _age = 0;
  UnitList* it= gi.premises;
  while(it) {
    Unit* prem = it->head();
    ASS(prem->isClause());
    _age = std::max(_age,prem->inference().age());
    it=it->tail();
  }
  _age++;
}

Inference::Inference(const SimplifyingInference1& si) {
  init1(si.rule,si.premise);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS(si.premise->isClause());

  _age = si.premise->age();
}

Inference::Inference(const SimplifyingInference2& si) {
  init2(si.rule,si.premise1,si.premise2);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS(si.premise1->isClause());
  ASS(si.premise2->isClause());

  _age = si.premise1->age();
}

Inference::Inference(const SimplifyingInferenceMany& si) {
  initMany(si.rule,si.premises);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS_NEQ(si.premises,UnitList::empty());
  ASS(si.premises->head()->isClause()); // TODO: assert also for all others?

  _age = si.premises->head()->inference().age();
}

Inference::Inference(const NonspecificInference0& gi) {
  init0(gi.affinity,gi.rule);

  ASS_REP(isNonSpecificInferenceRule(gi.rule), ruleName(gi.rule));
}

Inference::Inference(const NonspecificInference1& gi) {
  init1(gi.rule,gi.premise);

  ASS_REP(isNonSpecificInferenceRule(gi.rule), ruleName(gi.rule));
}

Inference::Inference(const NonspecificInference2& gi) {
  init2(gi.rule,gi.premise1,gi.premise2);

  ASS_REP(isNonSpecificInferenceRule(gi.rule), ruleName(gi.rule));
}

Inference::Inference(const NonspecificInferenceMany& gi) {
  initMany(gi.rule,gi.premises);

  ASS_REP(isNonSpecificInferenceRule(gi.rule), ruleName(gi.rule));
}

void Inference::minimizePremises()
{
  if (_kind != Kind::SAT_NEEDS_MINIMIZATION)
    return;
  if(!env.options->minimizeSatProofs())
    return;

  TIME_TRACE("sat proof minimization");

  NeedsMinimizationInfo* info = static_cast<NeedsMinimizationInfo*>(_ptr2);
  ASS(info)

  SATClauseList* minimized = MinisatInterfacing<>::minimizePremiseList(info->_satPremises,info->_usedAssumptions);

  SATClause* newSatRef = new(0) SATClause(0);
  newSatRef->setInference(new PropInference(minimized));

  // TODO dubious: isn't this just getOrigin() of all the info->_satPremises?
  UnitList* newFOPrems = SATInference::getFOPremises(newSatRef);

  // cout << "Minimized from " << _premises->length() << " to " << newFOPrems->length() << endl;

  // "release" the old list
  {
    UnitList* it = static_cast<UnitList*>(_ptr1);
    while(it) {
      it->head()->decRefCnt();
      it=it->tail();
    }
  }

  // assign and keep the new one
  {
    _ptr1 = newFOPrems;
    UnitList* it= newFOPrems;
    while(it) {
      it->head()->incRefCnt();
      it=it->tail();
    }
  }

  newSatRef->destroy(); // deletes also the inference and with it the list minimized, but not the clauses inside

  delete info;
  _ptr2 = nullptr;
}


std::string Kernel::goalAffinityName(GoalAffinity type)
{
  switch (type) {
    case GoalAffinity::DISTANT_AXIOM:
      return "distant axiom";
    case GoalAffinity::AXIOM:
      return "axiom";
    case GoalAffinity::ASSUMPTION:
      return "assumption";
    case GoalAffinity::CONJECTURE:
      return "conjecture";
  default:
      return "unknown";
  }
}

std::ostream& Kernel::operator<<(std::ostream& out, GoalAffinity type)
{ return out << goalAffinityName(type); }

/**
 * Return the rule name, such as "binary_resolution".
 * @since 04/01/2008 Torrevieja
 */
std::string Kernel::ruleName(InferenceRule rule)
{
  switch (rule) {
  case InferenceRule::INPUT:
    return "input";
  case InferenceRule::INPUT_CONJECTURE:
    return "input_conjecture";
  case InferenceRule::CONJECTURE_NEGATION:
    return "conjecture_negation";
  case InferenceRule::ANSWER_LITERAL_INJECTION:
    return "answer_literal_injection";
  case InferenceRule::ANSWER_LITERAL_RESOLVER:
    return "answer_literal_resolver";
  case InferenceRule::ANSWER_LITERAL_INPUT_SKOLEMISATION:
    return "answer_literal_with_input_var_skolemisation";
  case InferenceRule::ANSWER_LITERAL_REMOVAL:
    return "answer_literal_removal";
  case InferenceRule::ANSWER_LITERAL_JOIN_WITH_CONSTRAINTS:
    return "answer_literal_join_with_constraints";
  case InferenceRule::ANSWER_LITERAL_JOIN_AS_ITE:
    return "answer_literal_if_then_else";
  case InferenceRule::AVATAR_ASSERTION_REINTRODUCTION:
    return "avatar_assertion_reintroduction";
  case InferenceRule::RECTIFY:
    return "rectify";
  case InferenceRule::CLOSURE:
    return "closure";
  case InferenceRule::FLATTEN:
    return "flattening";
  case InferenceRule::FOOL_ELIMINATION:
    return "fool_elimination";
  case InferenceRule::FOOL_ITE_DEFINITION:
    return "fool_ite_definition";
  case InferenceRule::FOOL_LET_DEFINITION:
    return "fool_let_definition";
  case InferenceRule::FOOL_FORMULA_DEFINITION:
    return "fool_formula_definition";
  case InferenceRule::FOOL_MATCH_DEFINITION:
    return "fool_match_definition";
  case InferenceRule::FOOL_PARAMODULATION:
    return "fool_paramodulation";
  case InferenceRule::REORDER_LITERALS:
    return "literal_reordering";
  case InferenceRule::ENNF:
    return "ennf_transformation";
  case InferenceRule::NNF:
    return "nnf_transformation";
  case InferenceRule::CLAUSIFY:
    return "cnf_transformation";
  case InferenceRule::REORIENT_EQUATIONS:
    return "reorient_equations";
  case InferenceRule::FORMULIFY:
    return "formulify";
  case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    return "duplicate_literal_removal";
  case InferenceRule::SKOLEMIZE:
    return "skolemize";
  case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    return "skolem_symbol_introduction";
  case InferenceRule::RESOLUTION:
    return "resolution";
  case InferenceRule::CONSTRAINED_RESOLUTION:
    return "constrained_resolution";
  case InferenceRule::EQUALITY_PROXY_REPLACEMENT:
    return "equality_proxy_replacement";
  case InferenceRule::EQUALITY_PROXY_DEFINITION:
    return "equality_proxy_definition";
  case InferenceRule::EQUALITY_PROXY_AXIOM:
    return "equality_proxy_axiom";
  case InferenceRule::ALASCA_INTEGRALITY_AXIOM:
    return "alasca_integrality_axiom";
  case InferenceRule::EXTENSIONALITY_RESOLUTION:
    return "extensionality_resolution";
  case InferenceRule::DEFINITION_UNFOLDING:
    return "definition_unfolding";
  case InferenceRule::DEFINITION_FOLDING:
    return "definition_folding";
  case InferenceRule::FUNCTION_DEFINITION:
    return "function_definition";
  case InferenceRule::PREDICATE_DEFINITION:
    return "predicate_definition_introduction";
  case InferenceRule::PREDICATE_DEFINITION_UNFOLDING:
    return "predicate_definition_unfolding";
  case InferenceRule::PREDICATE_DEFINITION_MERGING:
    return "predicate_definition_merging";
  case InferenceRule::REDUCE_FALSE_TRUE:
    return "true_and_false_elimination";
  case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    return "trivial_inequality_removal";
  case InferenceRule::FACTORING:
    return "factoring";
  case InferenceRule::CONSTRAINED_FACTORING:
    return "constrained_factoring";
  case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    return "forward_subsumption_resolution";
  case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
    return "backward_subsumption_resolution";
  case InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION:
    return "subsumption_equality_resolution";
  case InferenceRule::SUPERPOSITION:
    return "superposition";
  case InferenceRule::FUNCTION_DEFINITION_REWRITING:
    return "function_definition_rewriting";
  case InferenceRule::FUNCTION_DEFINITION_DEMODULATION:
    return "function_definition_demodulation";
  case InferenceRule::CONSTRAINED_SUPERPOSITION:
    return "constrained_superposition";
  case InferenceRule::EQUALITY_FACTORING:
    return "equality_factoring";
  case InferenceRule::EQUALITY_RESOLUTION:
  case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    return "equality_resolution";
  case InferenceRule::FORWARD_DEMODULATION:
    return "forward_demodulation";
  case InferenceRule::BACKWARD_DEMODULATION:
    return "backward_demodulation";
  case InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION:
    return "forward_subsumption_demodulation";
  case InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION:
    return "backward_subsumption_demodulation";
  case InferenceRule::FORWARD_LITERAL_REWRITING:
    return "forward_literal_rewriting";
  case InferenceRule::INNER_REWRITING:
    return "inner_rewriting";
  case InferenceRule::CONDENSATION:
    return "condensation";
  case InferenceRule::ALASCA_INTEGER_TRANSFORMATION:
    return "alasca_integer_transformation";
  case InferenceRule::THEORY_NORMALIZATION:
    return "theory_normalization";
  case InferenceRule::POLARITY_FLIPPING:
    return "consistent_polarity_flipping";
  case InferenceRule::EVALUATION:
    return "evaluation";
  case InferenceRule::CANCELLATION:
    return "cancellation";
  case InferenceRule::INTERPRETED_SIMPLIFICATION:
    return "interpreted_simplification";
  case InferenceRule::UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "unused_predicate_definition_removal";
  case InferenceRule::PURE_PREDICATE_REMOVAL:
    return "pure_predicate_removal";
  case InferenceRule::PREDICATE_ELIMINATION:
    return "predicate_elimination";
  case InferenceRule::INEQUALITY_SPLITTING:
    return "inequality_splitting";
  case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    return "inequality_splitting_name_introduction";
  case InferenceRule::DISTINCTNESS_AXIOM:
    return "distinctness_axiom";
  case InferenceRule::DISTINCT_EXPANSION:
    return "distinct_expansion";
  case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    return "theory_tautology_sat_conflict";
  case InferenceRule::THA_COMMUTATIVITY:
    return "tha_commutativity";
  case InferenceRule::THA_ASSOCIATIVITY:
    return "tha_associativity";
  case InferenceRule::THA_RIGHT_IDENTITY:
    return "tha_right_identity";
  case InferenceRule::THA_LEFT_IDENTITY:
    return "tha_left_identity";
  case InferenceRule::THA_INVERSE_OP_OP_INVERSES:
    return "tha_inverse_op_op_inverses";
  case InferenceRule::THA_INVERSE_OP_UNIT:
    return "tha_inverse_op_unit";
  case InferenceRule::THA_INVERSE_ASSOC:
    return "tha_inverse_associativity";
  case InferenceRule::THA_NONREFLEX:
    return "tha_non_reflexivity";
  case InferenceRule::THA_TRANSITIVITY:
    return "tha_transitivity";
  case InferenceRule::THA_ORDER_TOTALITY:
    return "tha_order_totality";
  case InferenceRule::THA_ORDER_MONOTONICITY:
    return "tha_order_monotonicity";
  case InferenceRule::THA_ALASCA:
    return "tha_alasca";
  case InferenceRule::THA_PLUS_ONE_GREATER:
    return "tha_plus_one_greater";
  case InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY:
    return "tha_order_plus_one_dichotomy";
  case InferenceRule::THA_MINUS_MINUS_X:
    return "tha_minus_minus_x";
  case InferenceRule::THA_TIMES_ZERO:
    return "tha_times_zero";
  case InferenceRule::THA_DISTRIBUTIVITY:
    return "tha_distributivity";
  case InferenceRule::THA_DIVISIBILITY:
    return "tha_divisibility";
  case InferenceRule::THA_MODULO_MULTIPLY:
    return "tha_modulo_multiply";
  case InferenceRule::THA_MODULO_POSITIVE:
    return "tha_modulo_positive";
  case InferenceRule::THA_MODULO_SMALL:
    return "tha_modulo_small";
  case InferenceRule::THA_DIVIDES_MULTIPLY:
    return "tha_divides_multiply";
  case InferenceRule::THA_NONDIVIDES_SKOLEM:
    return "tha_nondivides_skolem";
  case InferenceRule::THA_ABS_EQUALS:
    return "tha_abs_equals";
  case InferenceRule::THA_ABS_MINUS_EQUALS:
    return "tha_abs_minus_equals";
  case InferenceRule::THA_QUOTIENT_NON_ZERO:
    return "tha_quotient_non_zero";
  case InferenceRule::THA_QUOTIENT_MULTIPLY:
    return "tha_quotient_multiply";
  case InferenceRule::THA_EXTRA_INTEGER_ORDERING:
    return "tha_extra_integer_ordering";
  case InferenceRule::THA_FLOOR_SMALL:
    return "tha_floor_small";
  case InferenceRule::THA_FLOOR_BIG:
    return "tha_floor_big";
  case InferenceRule::THA_CEILING_BIG:
    return "tha_ceiling_big";
  case InferenceRule::THA_CEILING_SMALL:
    return "tha_ceiling_small";
  case InferenceRule::THA_TRUNC1:
    return "tha_trunc1";
  case InferenceRule::THA_TRUNC2:
    return "tha_trunc2";
  case InferenceRule::THA_TRUNC3:
    return "tha_trunc3";
  case InferenceRule::THA_TRUNC4:
    return "tha_trunc4";
  case InferenceRule::THA_ARRAY_EXTENSIONALITY:
    return "tha_array_extensionality";
  case InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY:
    return "tha_boolen_array_extensionality";
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE1:
    return "tha_boolean_array_write1";
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE2:
    return "tha_boolean_array_write2";
  case InferenceRule::THA_ARRAY_WRITE1:
    return "tha_array_write1";
  case InferenceRule::THA_ARRAY_WRITE2:
    return "tha_array_write2";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    return "term_algebras_acyclicity_axiom";
  case InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    return "term_algebras_discriminators_axiom";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    return "term_algebras_distinctness_axiom";
  case InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    return "term_algebras_exhaustiveness_axiom";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    return "term_algebras_injectivity_axiom";
  case InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE:
    return "fool_distinctness_axiom";
  case InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
    return "fool_exhaustiveness_axiom";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY:
    return "term_algebras_acyclicity";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS:
    return "term_algebras_distinctness";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_GENERATING:
    return "term_algebras_injectivity_generating";
  case InferenceRule::TERM_ALGEBRA_POSITIVE_INJECTIVITY_SIMPLIFYING:
    return "term_algebras_positive_injectivity_simplifying";
  case InferenceRule::TERM_ALGEBRA_NEGATIVE_INJECTIVITY_SIMPLIFYING:
    return "term_algebras_negative_injectivity_simplifying";
  case InferenceRule::THEORY_FLATTENING:
    return "theory_flattening";
  case InferenceRule::BOOLEAN_TERM_ENCODING:
    return "boolean_term_encoding";
  case InferenceRule::AVATAR_DEFINITION:
    return "avatar_definition";
  case InferenceRule::AVATAR_COMPONENT:
    return "avatar_component_clause";
  case InferenceRule::AVATAR_REFUTATION:
    return "avatar_sat_refutation";
  case InferenceRule::AVATAR_REFUTATION_SMT:
    return "avatar_smt_refutation";
  case InferenceRule::AVATAR_SPLIT_CLAUSE:
    return "avatar_split_clause";
  case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    return "avatar_contradiction_clause";
  case InferenceRule::SAT_COLOR_ELIMINATION:
    return "sat_color_elimination";
  case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    return "general_splitting_component_introduction";
  case InferenceRule::GENERAL_SPLITTING:
    return "general_splitting";
  case InferenceRule::COLOR_UNBLOCKING:
    return "color_unblocking";
  case InferenceRule::UNIT_RESULTING_RESOLUTION:
    return "unit_resulting_resolution";
  case InferenceRule::GLOBAL_SUBSUMPTION:
    return "global_subsumption";
  case InferenceRule::DISTINCT_EQUALITY_REMOVAL:
    return "distinct_equality_removal";
  case InferenceRule::CLAIM_DEFINITION:
    return "claim_definition";
  case InferenceRule::FMB_FLATTENING:
    return "flattening_finite_model_building";
  case InferenceRule::FMB_FUNC_DEF:
    return "functional_definition_finite_model_building";
  case InferenceRule::FMB_DEF_INTRO:
    return "definition_introduction_finite_model_building";
  case InferenceRule::ADD_SORT_PREDICATES:
    return "add_sort_predicates";
  case InferenceRule::ADD_SORT_FUNCTIONS:
    return "add_sort_functions";
  case InferenceRule::INSTANTIATION:
    return "instantiation";
  case InferenceRule::ALASCA_VARIABLE_ELIMINATION:
    return "alasca_variable_elimination";
  case InferenceRule::ALASCA_VIRAS_QE:
    return "alasca_viras_quantifier_elimination";
  case InferenceRule::ALASCA_COHERENCE:
    return "alasca_coherence";
  case InferenceRule::ALASCA_COHERENCE_NORMALIZATION:
    return "alasca_coherence_normalization";
  case InferenceRule::ALASCA_SUPERPOSITION:
    return "alasca_superposition";
  case InferenceRule::ALASCA_LITERAL_FACTORING:
    return "alasca_inequality_literal_factoring";
  case InferenceRule::ALASCA_EQ_FACTORING:
    return "alasca_equality_factoring";
  case InferenceRule::ALASCA_FLOOR_BOUNDS:
    return "alasca_floor_bounds";
  case InferenceRule::ALASCA_TERM_FACTORING:
    return "alasca_term_factoring";
  case InferenceRule::ALASCA_INTEGER_FOURIER_MOTZKIN:
    return "alasca_integer_fourier_motzkin";
  case InferenceRule::ALASCA_FOURIER_MOTZKIN:
    return "alasca_fourier_motzkin";
  case InferenceRule::ALASCA_FLOOR_ELIMINATION:
    return "alasca_floor_elimination";
  case InferenceRule::ALASCA_NORMALIZATION:
    return "alasca_normalization";
  case InferenceRule::ALASCA_ABSTRACTION:
    return "alasca_abstraction";
  case InferenceRule::ALASCA_FWD_DEMODULATION:
    return "alasca_forward_demodulation";
  case InferenceRule::ALASCA_BWD_DEMODULATION:
    return "lascsa_backward_demodulation";
  case InferenceRule::MODEL_NOT_FOUND:
    return "finite_model_not_found_exhaustively_excluded_all_possible_domain_size_assignments";
  case InferenceRule::ARITHMETIC_SUBTERM_GENERALIZATION:
    return "arithmetic_subterm_generalization";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_ONE:
    return "structural_induction_formula_one";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_TWO:
    return "structural_induction_formula_two";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_THREE:
    return "structural_induction_formula_three";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_RECURSION:
    return "structural_induction_formula_recursion";
  case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    return "integer_induction_formula_up_infinite_interval";
  case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    return "integer_induction_formula_down_infinite_interval";
  case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    return "integer_induction_formula_up_finite_interval";
  case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    return "integer_induction_formula_down_finite_interval";
  case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    return "integer_induction_formula_up_default_bound";
  case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    return "integer_induction_formula_down_default_bound";
  case InferenceRule::INDUCTION_HYPERRESOLUTION:
    return "induction_hyperresolution";
  case InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION:
    return "gaussian_variable_elimination";
  case InferenceRule::ARG_CONG:
    return "argument_congruence";
  case InferenceRule::NEGATIVE_EXTENSIONALITY:
    return "negative_extensionality";
  case InferenceRule::POSITIVE_EXTENSIONALITY:
    return "positive_extensionality";
  case InferenceRule::INJECTIVITY:
    return "injectivity";
  case InferenceRule::NOT_PROXY_CLAUSIFICATION:
    return "not_proxy_clausification";
  case InferenceRule::AND_PROXY_CLAUSIFICATION:
    return "and_proxy_clausification";
  case InferenceRule::OR_PROXY_CLAUSIFICATION:
    return "or_proxy_clausification";
  case InferenceRule::IMP_PROXY_CLAUSIFICATION:
    return "imp_proxy_clausification";
  case InferenceRule::IFF_PROXY_CLAUSIFICATION:
    return "iff_proxy_clausification";
  case InferenceRule::XOR_PROXY_CLAUSIFICATION:
    return "xor_proxy_clausification";
  case InferenceRule::SIGMA_PROXY_CLAUSIFICATION:
    return "sigma_proxy_clausification";
  case InferenceRule::PI_PROXY_CLAUSIFICATION:
    return "pi_proxy_clausification";
  case InferenceRule::EQUALITY_PROXY_CLAUSIFICATION:
    return "equality_proxy_clausification";
  case InferenceRule::BOOL_SIMP:
    return "boolean_simplification";
  case InferenceRule::FLEX_FLEX_SIMPLIFICATION:
    return "flex_flex_simplification";
  case InferenceRule::BETA_ETA_NORMALIZATION:
    return "beta_eta_normalization";
  case InferenceRule::NOT_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "not_proxy_clausification_simplifying";
  case InferenceRule::AND_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "and_proxy_clausification_simplifying";
  case InferenceRule::OR_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "or_proxy_clausification_simplifying";
  case InferenceRule::IMP_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "imp_proxy_clausification_simplifying";
  case InferenceRule::IFF_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "iff_proxy_clausification_simplifying";
  case InferenceRule::XOR_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "xor_proxy_clausification_simplifying";
  case InferenceRule::SIGMA_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "sigma_proxy_clausification_simplifying";
  case InferenceRule::PI_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "pi_proxy_clausification_simplifying";
  case InferenceRule::EQUALITY_PROXY_CLAUSIFICATION_SIMPLIFYING:
    return "equality_proxy_clausification_simplifying";
  case InferenceRule::EQ_TO_DISEQ:
    return "bool_equality_to_disequality";
  case InferenceRule::HEURISTIC_INSTANTIATION:
    return "heuristic_instantiation";
  case InferenceRule::PRIMITIVE_INSTANTIATION:
    return "primitive_instantiation";
  case InferenceRule::IMITATION:
    return "imitation";
  case InferenceRule::PROJECTION:
    return "projection";
  case InferenceRule::LEIBNIZ_ELIMINATION:
    return "leibniz_equality_elimination";
  case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    return "hilbertian_choice_axiom_instance";
  case InferenceRule::CASES_SIMP:
    return "cases_simplifying";
  case InferenceRule::TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM:
    return "term_algebra_direct_subterm_axiom";
  case InferenceRule::TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM:
    return "term_algebra_subterm_transitivity_axiom";
  case InferenceRule::FUNCTIONAL_EXTENSIONALITY_AXIOM:
    return "functional_extensionality_axiom";
    /* this cases are no actual inference rules but only markeres to separatea groups of rules */
  case InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION:
  case InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION_LAST:
  case InferenceRule::GENERIC_SIMPLIFYING_INFERENCE:
  case InferenceRule::GENERIC_SIMPLIFYING_INFERENCE_LAST:
  case InferenceRule::GENERIC_GENERATING_INFERENCE:
  case InferenceRule::GENERIC_GENERATING_INFERENCE_LAST:
  case InferenceRule::GENERIC_AVATAR_INFERENCE:
  case InferenceRule::GENERIC_AVATAR_INFERENCE_LAST:
  case InferenceRule::GENERIC_THEORY_AXIOM:
  case InferenceRule::GENERIC_THEORY_AXIOM_LAST:
  case InferenceRule::GENERIC_NONSPECIFIC_INFERENCE:
  case InferenceRule::GENERIC_NONSPECIFIC_INFERENCE_LAST:
    { /* explicitly ignoring this cases */ }
  }

  INVALID_OPERATION("invalid inference rule");
} // ruleName()


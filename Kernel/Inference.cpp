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
 * Return UnitInputType of which should be a formula that has
 * units of types @c t1 and @c t2 as premises.
 */
UnitInputType Kernel::getInputType(UnitInputType t1, UnitInputType t2)
{
  return static_cast<UnitInputType>(std::max(toNumber(t1), toNumber(t2)));
}

/**
 * Return UnitInputType of which should be a formula that has
 * @c units as premises.
 *
 * @c units must be a non-empty list.
 */
UnitInputType Kernel::getInputType(UnitList* units)
{
  ASS(units);

  UnitList::Iterator uit(units);
  ALWAYS(uit.hasNext());
  UnitInputType res = uit.next()->inputType();

  while(uit.hasNext()) {
    res = Kernel::getInputType(res, uit.next()->inputType());
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
        _XXNarrows = static_cast<Unit*>(_ptr1)->inference().xxNarrows();
        _reductions = static_cast<Unit*>(_ptr1)->inference().reductions();
      } else {
        _inductionDepth = max(static_cast<Unit*>(_ptr1)->inference().inductionDepth(),
            static_cast<Unit*>(_ptr2)->inference().inductionDepth());
        _XXNarrows = max(static_cast<Unit*>(_ptr1)->inference().xxNarrows(),
            static_cast<Unit*>(_ptr2)->inference().xxNarrows());
        _reductions = max(static_cast<Unit*>(_ptr1)->inference().reductions(),
            static_cast<Unit*>(_ptr2)->inference().reductions());
      }

      break;
    case Kind::INFERENCE_MANY:
    case Kind::SAT:
    case Kind::SAT_NEEDS_MINIMIZATION:
      _inductionDepth = 0;
      _XXNarrows = 0;
      _reductions = 0;
      UnitList* it = static_cast<UnitList*>(_ptr1);
      while(it) {
        _inductionDepth = max(_inductionDepth,it->head()->inference().inductionDepth());
        _XXNarrows = max(_XXNarrows,it->head()->inference().xxNarrows());
        _reductions = max(_reductions,it->head()->inference().reductions());
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
  out << "), it: " << toNumber(self._inputType);

  out << ", incl: " << self._included;
  out << ", ptd: " << self._isPureTheoryDescendant;
  out << ", sl: " << self._sineLevel;
  out << ", age: " << self._age;
  out << ", thAx:" << static_cast<int>(self.th_ancestors);
  out << ", allAx:" << static_cast<int>(self.all_ancestors);

  return out;
}


void Inference::init0(UnitInputType inputType, InferenceRule r)
{
  initDefault(inputType,r);
  _kind = Kind::INFERENCE_012;
  _ptr1 = nullptr;
  _ptr2 = nullptr;

  computeTheoryRunningSums();

  _isPureTheoryDescendant = isTheoryAxiom();

  //_inductionDepth = 0 from initDefault (or set externally)
  //_sineLevel = MAX from initDefault (or set externally)
}

void Inference::init1(InferenceRule r, Unit* premise)
{
  initDefault(premise->inputType(),r);

  _kind = Kind::INFERENCE_012;
  _ptr1 = premise;
  _ptr2 = nullptr;

  premise->incRefCnt();

  computeTheoryRunningSums();
  _isPureTheoryDescendant = premise->isPureTheoryDescendant();
  _sineLevel = premise->getSineLevel();

  updateStatistics();
}

void Inference::init2(InferenceRule r, Unit* premise1, Unit* premise2)
{
  initDefault(getInputType(premise1->inputType(),premise2->inputType()),r);

  _kind = Kind::INFERENCE_012;
  _ptr1 = premise1;
  _ptr2 = premise2;

  premise1->incRefCnt();
  premise2->incRefCnt();

  computeTheoryRunningSums();
  _isPureTheoryDescendant = premise1->isPureTheoryDescendant() && premise2->isPureTheoryDescendant();
  _sineLevel = min(premise1->getSineLevel(),premise2->getSineLevel());

  updateStatistics();
}

void Inference::initMany(InferenceRule r, UnitList* premises)
{
  initDefault(UnitInputType::AXIOM /* the minimal element; we later compute maximum over premises*/,r);

  _kind = Kind::INFERENCE_MANY;
  _ptr1 = premises;
  _ptr2 = nullptr;

  UnitList* it= premises;
  while(it) {
    it->head()->incRefCnt();
    it=it->tail();
  }

  computeTheoryRunningSums();

  if (premises) {
    _isPureTheoryDescendant = true;
    it=premises;
    while(it) {
      const Inference& inf = it->head()->inference();
      _inputType = getInputType(_inputType,inf.inputType());
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
  init0(fi.inputType,InferenceRule::INPUT);
}

Inference::Inference(const TheoryAxiom& ta) {
  init0(UnitInputType::AXIOM,ta.rule);
  ASS_REP(isTheoryAxiom(), ruleName(ta.rule));
}

Inference::Inference(const FormulaClauseTransformation& ft) {
  init1(ft.rule,ft.premise);

  ASS_REP(isFormulaClauseTransformation(ft.rule),ruleName(ft.rule));

  _included = ft.premise->included();
}

Inference::Inference(const FormulaClauseTransformationMany& ft) {
  initMany(ft.rule,ft.premises);

  ASS_REP(isFormulaClauseTransformation(ft.rule),ruleName(ft.rule));
  ASS_NEQ(ft.premises,UnitList::empty());

  _included = ft.premises->head()->included();
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
  init0(gi.inputType,gi.rule);
}

Inference::Inference(const NonspecificInference1& gi) {
  init1(gi.rule,gi.premise);
}

Inference::Inference(const NonspecificInference2& gi) {
  init2(gi.rule,gi.premise1,gi.premise2);
}

Inference::Inference(const NonspecificInferenceMany& gi) {
  initMany(gi.rule,gi.premises);
}

std::string Inference::name() const {
  if (_rule == InferenceRule::INPUT) {
    return ruleName(_rule)+"("+inputTypeName(_inputType)+")";
  } else {
    return ruleName(_rule);
  }
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

void Inference::computeTheoryRunningSums()
{
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
      th_ancestors = mainPremise->inference().th_ancestors;
      all_ancestors = mainPremise->inference().all_ancestors;
    }
    // for non-simplifying inferences, compute running sums as sum over all parents
    else
    {
      th_ancestors = 0.0;
      all_ancestors = 0.0; // there is going to be at least one, eventually
      while (hasNext(parentIt))
      {
        Unit *parent = next(parentIt);
        th_ancestors += parent->inference().th_ancestors;
        all_ancestors += parent->inference().all_ancestors;
      }
    }
  }
}

std::string Kernel::inputTypeName(UnitInputType type)
{
  switch (type) {
    case UnitInputType::AXIOM:
      return "axiom";
    case UnitInputType::ASSUMPTION:
      return "assumption";
    case UnitInputType::CONJECTURE:
      return "conjecture";
    case UnitInputType::NEGATED_CONJECTURE:
      return "negated conjecture";
    case UnitInputType::CLAIM:
      return "claim";
    case UnitInputType::EXTENSIONALITY_AXIOM:
      return "extensionality axiom";
  default:
      return "unknown";
  }
}

/**
 * Return the rule name, such as "binary resolution".
 * @since 04/01/2008 Torrevieja
 */
std::string Kernel::ruleName(InferenceRule rule)
{
  switch (rule) {
  case InferenceRule::INPUT:
    return "input";
  case InferenceRule::NEGATED_CONJECTURE:
    return "negated conjecture";
  case InferenceRule::ANSWER_LITERAL_INJECTION:
    return "answer literal injection";
  case InferenceRule::ANSWER_LITERAL_RESOLVER:
    return "answer literal resolver";
  case InferenceRule::ANSWER_LITERAL_INPUT_SKOLEMISATION:
    return "answer literal with input var skolemisation";
  case InferenceRule::ANSWER_LITERAL_REMOVAL:
    return "answer literal removal";
  case InferenceRule::ANSWER_LITERAL_JOIN_WITH_CONSTRAINTS:
    return "answer literal join with constraints";
  case InferenceRule::ANSWER_LITERAL_JOIN_AS_ITE:
    return "answer literal if-then-else";
  case InferenceRule::AVATAR_ASSERTION_REINTRODUCTION:
    return "avatar assertion reintroduction";
  case InferenceRule::RECTIFY:
    return "rectify";
  case InferenceRule::CLOSURE:
    return "closure";
  case InferenceRule::FLATTEN:
    return "flattening";
  case InferenceRule::FOOL_ELIMINATION:
    return "fool elimination";
  case InferenceRule::FOOL_ITE_DEFINITION:
    return "fool ite definition";
  case InferenceRule::FOOL_LET_DEFINITION:
    return "fool let definition";
  case InferenceRule::FOOL_FORMULA_DEFINITION:
    return "fool formula definition";
  case InferenceRule::FOOL_MATCH_DEFINITION:
    return "fool match definition";
  case InferenceRule::FOOL_PARAMODULATION:
    return "fool paramodulation";
  case InferenceRule::REORDER_LITERALS:
    return "literal reordering";
  case InferenceRule::ENNF:
    return "ennf transformation";
  case InferenceRule::NNF:
    return "nnf transformation";
  case InferenceRule::CLAUSIFY:
    return "cnf transformation";
  case InferenceRule::REORIENT_EQUATIONS:
    return "reorient equations";
  case InferenceRule::FORMULIFY:
    return "formulify";
  case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    return "duplicate literal removal";
  case InferenceRule::SKOLEMIZE:
    return "skolemisation";
  case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    return "skolem symbol introduction";
  case InferenceRule::RESOLUTION:
    return "resolution";
  case InferenceRule::CONSTRAINED_RESOLUTION:
    return "constrained resolution";
  case InferenceRule::EQUALITY_PROXY_REPLACEMENT:
    return "equality proxy replacement";
  case InferenceRule::EQUALITY_PROXY_AXIOM1:
    return "equality proxy definition";
  case InferenceRule::EQUALITY_PROXY_AXIOM2:
    return "equality proxy axiom";
  case InferenceRule::EXTENSIONALITY_RESOLUTION:
    return "extensionality resolution";
  case InferenceRule::DEFINITION_UNFOLDING:
    return "definition unfolding";
  case InferenceRule::DEFINITION_FOLDING:
    return "definition folding";
  case InferenceRule::FUNCTION_DEFINITION:
    return "function definition";
  case InferenceRule::PREDICATE_DEFINITION:
    return "predicate definition introduction";
  case InferenceRule::PREDICATE_DEFINITION_UNFOLDING:
    return "predicate definition unfolding";
  case InferenceRule::PREDICATE_DEFINITION_MERGING:
    return "predicate definition merging";

  case InferenceRule::REDUCE_FALSE_TRUE:
    return "true and false elimination";

  case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    return "trivial inequality removal";
  case InferenceRule::FACTORING:
    return "factoring";
  case InferenceRule::CONSTRAINED_FACTORING:
    return "constrained factoring";
  case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    return "forward subsumption resolution";
  case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
    return "backward subsumption resolution";
  case InferenceRule::SUPERPOSITION:
    return "superposition";
  case InferenceRule::FUNCTION_DEFINITION_REWRITING:
    return "function definition rewriting";
  case InferenceRule::FUNCTION_DEFINITION_DEMODULATION:
    return "function definition demodulation";
  case InferenceRule::CONSTRAINED_SUPERPOSITION:
    return "constrained superposition";
  case InferenceRule::EQUALITY_FACTORING:
    return "equality factoring";
  case InferenceRule::EQUALITY_RESOLUTION:
  case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    return "equality resolution";
  case InferenceRule::FORWARD_DEMODULATION:
    return "forward demodulation";
  case InferenceRule::BACKWARD_DEMODULATION:
    return "backward demodulation";
  case InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION:
    return "forward subsumption demodulation";
  case InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION:
    return "backward subsumption demodulation";
  case InferenceRule::FORWARD_LITERAL_REWRITING:
    return "forward literal rewriting";
  case InferenceRule::INNER_REWRITING:
    return "inner rewriting";
  case InferenceRule::CONDENSATION:
    return "condensation";
  case InferenceRule::ALASCA_INTEGER_TRANSFORMATION:
    return "alasca integer transformation";
  case InferenceRule::THEORY_NORMALIZATION:
    return "theory normalization";
  case InferenceRule::POLARITY_FLIPPING:
    return "consistent polarity flipping";
  case InferenceRule::EVALUATION:
    return "evaluation";
  case InferenceRule::CANCELLATION:
    return "cancellation";
  case InferenceRule::INTERPRETED_SIMPLIFICATION:
    return "interpreted simplification";
  case InferenceRule::UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "unused predicate definition removal";
  case InferenceRule::PURE_PREDICATE_REMOVAL:
    return "pure predicate removal";
  case InferenceRule::INEQUALITY_SPLITTING:
    return "inequality splitting";
  case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    return "inequality splitting name introduction";
  case InferenceRule::DISTINCTNESS_AXIOM:
    return "distinctness axiom";
  case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    return "theory tautology sat conflict";
  case InferenceRule::THA_COMMUTATIVITY:
    return "tha commutativity";
  case InferenceRule::THA_ASSOCIATIVITY:
    return "tha associativity";
  case InferenceRule::THA_RIGHT_IDENTITY:
    return "tha right identity";
  case InferenceRule::THA_LEFT_IDENTITY:
    return "tha left identity";
  case InferenceRule::THA_INVERSE_OP_OP_INVERSES:
    return "tha inverse op op inverses";
  case InferenceRule::THA_INVERSE_OP_UNIT:
    return "tha inverse op unit";
  case InferenceRule::THA_INVERSE_ASSOC:
    return "tha inverse associativity";
  case InferenceRule::THA_NONREFLEX:
    return "tha non-reflexivity";
  case InferenceRule::THA_TRANSITIVITY:
    return "tha transitivity";
  case InferenceRule::THA_ORDER_TOTALITY:
    return "tha order totality";
  case InferenceRule::THA_ORDER_MONOTONICITY:
    return "tha order monotonicity";
  case InferenceRule::THA_ALASCA:
    return "tha alasca";
  case InferenceRule::THA_PLUS_ONE_GREATER:
    return "tha plus one greater";
  case InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY:
    return "tha order plus one dichotomy";
  case InferenceRule::THA_MINUS_MINUS_X:
    return "tha minus minus x";
  case InferenceRule::THA_TIMES_ZERO:
    return "tha times zero";
  case InferenceRule::THA_DISTRIBUTIVITY:
    return "tha distributivity";
  case InferenceRule::THA_DIVISIBILITY:
    return "tha divisibility";
  case InferenceRule::THA_MODULO_MULTIPLY:
    return "tha modulo multiply";
  case InferenceRule::THA_MODULO_POSITIVE:
    return "tha modulo positive";
  case InferenceRule::THA_MODULO_SMALL:
    return "tha modulo small";
  case InferenceRule::THA_DIVIDES_MULTIPLY:
    return "tha divides multiply";
  case InferenceRule::THA_NONDIVIDES_SKOLEM:
    return "tha nondivides skolem";
  case InferenceRule::THA_ABS_EQUALS:
    return "tha abs equals";
  case InferenceRule::THA_ABS_MINUS_EQUALS:
    return "tha abs minus equals";
  case InferenceRule::THA_QUOTIENT_NON_ZERO:
    return "tha quotient non-zero";
  case InferenceRule::THA_QUOTIENT_MULTIPLY:
    return "tha quotient multiply";
  case InferenceRule::THA_EXTRA_INTEGER_ORDERING:
    return "tha extra integer ordering";
  case InferenceRule::THA_FLOOR_SMALL:
    return "tha floor small";
  case InferenceRule::THA_FLOOR_BIG:
    return "tha floor big";
  case InferenceRule::THA_CEILING_BIG:
    return "tha ceiling big";
  case InferenceRule::THA_CEILING_SMALL:
    return "tha ceiling small";
  case InferenceRule::THA_TRUNC1:
    return "tha trunc1";
  case InferenceRule::THA_TRUNC2:
    return "tha trunc2";
  case InferenceRule::THA_TRUNC3:
    return "tha trunc3";
  case InferenceRule::THA_TRUNC4:
    return "tha trunc4";
  case InferenceRule::THA_ARRAY_EXTENSIONALITY:
    return "tha array extensionality";
  case InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY:
    return "tha boolen array extensionality";
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE1:
    return "tha boolean array write1";
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE2:
    return "tha boolean array write2";
  case InferenceRule::THA_ARRAY_WRITE1:
    return "tha array write1";
  case InferenceRule::THA_ARRAY_WRITE2:
    return "tha array write2";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    return "term algebras acyclicity axiom";
  case InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    return "term algebras discriminators axiom";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    return "term algebras distinctness axiom";
  case InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    return "term algebras exhaustiveness axiom";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    return "term algebras injectivity axiom";
  case InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE:
    return "fool distinctness axiom";
  case InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
    return "fool exhaustiveness axiom";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY:
    return "term algebras acyclicity";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS:
    return "term algebras distinctness";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_GENERATING:
    return "term algebras injectivity (generating)";
  case InferenceRule::TERM_ALGEBRA_POSITIVE_INJECTIVITY_SIMPLIFYING:
    return "term algebras positive injectivity (simplifying)";
  case InferenceRule::TERM_ALGEBRA_NEGATIVE_INJECTIVITY_SIMPLIFYING:
    return "term algebras negative injectivity (simplifying)";
  case InferenceRule::THEORY_FLATTENING:
    return "theory flattening";
  case InferenceRule::BOOLEAN_TERM_ENCODING:
    return "boolean term encoding";
  case InferenceRule::AVATAR_DEFINITION:
    return "avatar definition";
  case InferenceRule::AVATAR_COMPONENT:
    return "avatar component clause";
  case InferenceRule::AVATAR_REFUTATION:
    return "avatar sat refutation";
  case InferenceRule::AVATAR_REFUTATION_SMT:
    return "avatar smt refutation";
  case InferenceRule::AVATAR_SPLIT_CLAUSE:
    return "avatar split clause";
  case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    return "avatar contradiction clause";
  case InferenceRule::SAT_COLOR_ELIMINATION:
    return "sat color elimination";
  case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    return "general splitting component introduction";
  case InferenceRule::GENERAL_SPLITTING:
    return "general splitting";


  case InferenceRule::COLOR_UNBLOCKING:
    return "color unblocking";
  case InferenceRule::UNIT_RESULTING_RESOLUTION:
    return "unit resulting resolution";
  case InferenceRule::GLOBAL_SUBSUMPTION:
    return "global subsumption";
  case InferenceRule::DISTINCT_EQUALITY_REMOVAL:
    return "distinct equality removal";
  case InferenceRule::CLAIM_DEFINITION:
    return "claim definition";
  case InferenceRule::FMB_FLATTENING:
    return "flattening (finite model building)";
  case InferenceRule::FMB_FUNC_DEF:
    return "functional definition (finite model building)";
  case InferenceRule::FMB_DEF_INTRO:
    return "definition introduction (finite model building)";
  case InferenceRule::ADD_SORT_PREDICATES:
    return "add sort predicates";
  case InferenceRule::ADD_SORT_FUNCTIONS:
    return "add sort functions";
  case InferenceRule::INSTANTIATION:
    return "instantiation";
  case InferenceRule::ALASCA_VARIABLE_ELIMINATION:
    return "alasca variable elimination";
  case InferenceRule::ALASCA_VIRAS_QE:
    return "alasca viras quantifier elimination";
  case InferenceRule::ALASCA_COHERENCE:
    return "alasca coherence";
  case InferenceRule::ALASCA_COHERENCE_NORMALIZATION:
    return "alasca coherence normalization";
  case InferenceRule::ALASCA_SUPERPOSITION:
    return "alasca superposition";
  case InferenceRule::ALASCA_LITERAL_FACTORING:
    return "alasca inequality literal factoring";
  case InferenceRule::ALASCA_EQ_FACTORING:
    return "alasca equality factoring";
  case InferenceRule::ALASCA_FLOOR_BOUNDS:
    return "alasca floor bounds";
  case InferenceRule::ALASCA_TERM_FACTORING:
    return "alasca term factoring";
  case InferenceRule::ALASCA_INTEGER_FOURIER_MOTZKIN:
    return "alasca integer fourier motzkin";
  case InferenceRule::ALASCA_FOURIER_MOTZKIN:
    return "alasca fourier motzkin";
  case InferenceRule::ALASCA_FLOOR_ELIMINATION:
    return "alasca floor elimination";
  case InferenceRule::ALASCA_NORMALIZATION:
    return "alasca normalization";
  case InferenceRule::ALASCA_ABSTRACTION:
    return "alasca abstraction";
  case InferenceRule::ALASCA_FWD_DEMODULATION:
    return "alasca forward demodulation";
  case InferenceRule::ALASCA_BWD_DEMODULATION:
    return "lascsa backward demodulation";
  case InferenceRule::MODEL_NOT_FOUND:
    return "finite model not found (exhaustively excluded all possible domain size assignments)";
  case InferenceRule::ARITHMETIC_SUBTERM_GENERALIZATION:
    return "arithmetic subterm generalization";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_ONE:
    return "structural induction formula (one)";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_TWO:
    return "structural induction formula (two)";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_THREE:
    return "structural induction formula (three)";
  case InferenceRule::STRUCT_INDUCTION_AXIOM_RECURSION:
    return "structural induction formula (recursion)";
  case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    return "integer induction formula (up, infinite interval)";
  case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    return "integer induction formula (down, infinite interval)";
  case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    return "integer induction formula (up, finite interval)";
  case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    return "integer induction formula (down, finite interval)";
  case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    return "integer induction formula (up, default bound)";
  case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    return "integer induction formula (down, default bound)";
  case InferenceRule::INDUCTION_HYPERRESOLUTION:
    return "induction hyperresolution";
  case InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION:
    return "gaussian variable elimination";
  case InferenceRule::ARG_CONG:
    return "argument congruence";
  case InferenceRule::NEGATIVE_EXT:
    return "negative extensionality";
  case InferenceRule::INJECTIVITY:
    return "injectivity";
  case InferenceRule::HOL_NOT_ELIMINATION:
    return "not proxy clausification";
  case InferenceRule::BINARY_CONN_ELIMINATION:
    return "binary proxy clausification";
  case InferenceRule::VSIGMA_ELIMINATION:
    return "sigma clausification";
  case InferenceRule::VPI_ELIMINATION:
    return "pi clausification";
  case InferenceRule::HOL_EQUALITY_ELIMINATION:
    return "equality proxy clausification";
  case InferenceRule::BOOL_SIMP:
    return "boolean simplification";
  case InferenceRule::EQ_TO_DISEQ:
    return "bool equality to disequality";
  case InferenceRule::PRIMITIVE_INSTANTIATION:
    return "primitive instantiation";
  case InferenceRule::LEIBNIZ_ELIMINATION:
    return "leibniz equality elimination";
  case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    return "Hilbert's choice axiom instance";
  case InferenceRule::CASES_SIMP:
    return "cases simplifying";
  case InferenceRule::TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM:
    return "term algebra direct subterm axiom";
  case InferenceRule::TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM:
    return "term algebra subterm transitivity axiom";
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
    { /* explicitly ignoring this cases */ }
  }

  ASSERTION_VIOLATION;
  /* moved outside of the case statement to get a compiler warning */
  return "!UNKNOWN INFERENCE RULE!";
} // Inference::name()


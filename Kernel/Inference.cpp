
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
#include "Kernel/Clause.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/MinisatInterfacing.hpp"

#include "Inference.hpp"

using namespace Kernel;


/**
 * Return UnitInputType of which should be a formula that has
 * units of types @c t1 and @c t2 as premises.
 */
UnitInputType Kernel::getInputType(UnitInputType t1, UnitInputType t2)
{
  CALL("getInputType");

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
  CALL("Inference::getInputType");
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
struct FromSatRefutationInfo {
  CLASS_NAME(FromSatRefutationInfo);
  USE_ALLOCATOR(FromSatRefutationInfo);

  FromSatRefutationInfo(const FromSatRefutation& fsr) : _satPremises(fsr._satPremises), _usedAssumptions(fsr._usedAssumptions)
  { ASS(_satPremises); }

  SAT::SATClauseList* _satPremises;
  SAT::SATLiteralStack _usedAssumptions; // possibly an empty stack
};


void Inference::destroyDirectlyOwned()
{
  CALL("Inference::destroyDirectlyOwned");

  switch(_kind) {
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
      delete static_cast<FromSatRefutationInfo*>(_ptr2);
      // intentionally fall further
    case Kind::INFERENCE_MANY:
      UnitList::destroy(static_cast<UnitList*>(_ptr1));
    default:
      ;
  }
}

void Inference::destroy()
{
  CALL("Inference::destroy");

  switch(_kind) {
    case Kind::INFERENCE_012:
      if (_ptr1) static_cast<Unit*>(_ptr1)->decRefCnt();
      if (_ptr2) static_cast<Unit*>(_ptr2)->decRefCnt();
      break;
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
      delete static_cast<FromSatRefutationInfo*>(_ptr2);
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

Inference::Inference(const FromSatRefutation& fsr) {
  CALL("Inference::Inference(FromSatRefutation)");

  initMany(fsr._rule,fsr._premises);

  ASS_REP(isSatRefutationRule(fsr._rule),ruleName(fsr._rule));

  if (fsr._satPremises == nullptr) {
    return; // SAT solver did not support minimization anyway
  }

  _kind = Kind::INFERENCE_FROM_SAT_REFUTATION;
  _ptr2 = new FromSatRefutationInfo(fsr);
}

/**
 * Return an iterator for an inference with zero premises.
 * @since 04/01/2008 Torrevieja
 */
Inference::Iterator Inference::iterator() const
{
  CALL("Inference::iterator");

  Iterator it;
  switch(_kind) {
    case Kind::INFERENCE_012:
      it.integer=0;
      break;
    case Kind::INFERENCE_MANY:
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
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
  CALL("Inference::hasNext");

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
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
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
  CALL("Inference::next");

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
    case Kind::INFERENCE_FROM_SAT_REFUTATION: {
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
  CALL("Inference::updateStatistics");

  switch(_kind) {
    case Kind::INFERENCE_012:
      if (_ptr1 == nullptr) {
        /* Inference0 does not update (it does not have parents anyway).
        * So if any of Inference0's statistics have been set externally during
        * proof search, update statistics won't reset these "hacky" values.
        * (C.f., inductionDepth assigned in AVATAR to AVATAR_DEFINITION
        * and thus later propagated to AVATAR_COMPONENT, AVATAR_SPLIT_CLAUSE, and transitively to AVATAR_REFUTATION,
        * and similarly inductionDepth assigned to INDUCTION "hypothesis" formulas in Induction.)
        */
      } else if (_ptr2 == nullptr) {
        _inductionDepth = static_cast<Unit*>(_ptr1)->inference().inductionDepth();
      } else {
        _inductionDepth = max(static_cast<Unit*>(_ptr1)->inference().inductionDepth(),
            static_cast<Unit*>(_ptr2)->inference().inductionDepth());
      }

      break;
    case Kind::INFERENCE_MANY:
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
      _inductionDepth = 0;
      UnitList* it= static_cast<UnitList*>(_ptr1);
      while(it) {
        _inductionDepth = max(_inductionDepth,it->head()->inference().inductionDepth());
        it=it->tail();
      }
      break;
  }
}

vstring Inference::toString() const
{
  CALL("Inference::toString");

  vstring result;

  switch(_kind) {
    case Kind::INFERENCE_012:
      result = "INFERENCE_012, (";
      break;
    case Kind::INFERENCE_MANY:
      result = "INFERENCE_MANY, (";
      break;
    case Kind::INFERENCE_FROM_SAT_REFUTATION:
      result = "INFERENCE_FROM_SAT_REFUTATION, (";
      break;
  }
  result += ruleName(_rule);
  result += "), it: " + Int::toString(toNumber(_inputType));

  result += ", incl: " + Int::toString(_included);
  result += ", ptd: " + Int::toString(_isPureTheoryDescendant);
  result += ", id: " + Int::toString(_inductionDepth);
  result += ", sl: " + Int::toString(_sineLevel);
  result += ", age: " + Int::toString(_age);
  result += ", thAx:" + Int::toString((int)(th_ancestors));
  result += ", allAx:" + Int::toString((int)(all_ancestors));

  return result;
}


void Inference::init0(UnitInputType inputType, InferenceRule r)
{
  CALL("Inference::init0");

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
  CALL("Inference::init1");

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
  CALL("Inference::init2");

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
  CALL("Inference::initMany");

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
  CALL("Inference::Inference(FromInput)");

  init0(fi.inputType,InferenceRule::INPUT);
}

Inference::Inference(const TheoryAxiom& ta) {
  CALL("Inference::Inference(TheoryAxiom)");

  init0(UnitInputType::AXIOM,ta.rule);
  ASS_REP(isTheoryAxiomRule(ta.rule),ruleName(ta.rule));
}

Inference::Inference(const FormulaTransformation& ft) {
  CALL("Inference::Inference(FormulaTransformation)");

  init1(ft.rule,ft.premise);

  ASS_REP(isFormulaTransformation(ft.rule),ruleName(ft.rule));
  ASS(!ft.premise->isClause());

  _included = ft.premise->included();
}

Inference::Inference(const FormulaTransformationMany& ft) {
  CALL("Inference::Inference(FormulaTransformationMany)");

  initMany(ft.rule,ft.premises);

  ASS_REP(isFormulaTransformation(ft.rule),ruleName(ft.rule));
  ASS_NEQ(ft.premises,UnitList::empty());
  ASS(!ft.premises->head()->isClause()); // TODO: assert also for all others?

  _included = ft.premises->head()->included();
}

Inference::Inference(const GeneratingInference1& gi) {
  CALL("Inference::Inference(GeneratingInference1)");

  init1(gi.rule,gi.premise);

  ASS_REP(isGeneratingInferenceRule(gi.rule),ruleName(gi.rule));
  ASS(gi.premise->isClause());

  _age = gi.premise->age()+1;
}

Inference::Inference(const GeneratingInference2& gi) {
  CALL("Inference::Inference(GeneratingInference2)");

  init2(gi.rule,gi.premise1,gi.premise2);

  ASS_REP(isGeneratingInferenceRule(gi.rule),ruleName(gi.rule));
  ASS(gi.premise1->isClause());
  ASS(gi.premise2->isClause());

  _age = std::max(gi.premise1->age(),gi.premise2->age())+1;
}

Inference::Inference(const GeneratingInferenceMany& gi) {
  CALL("Inference::Inference(GeneratingInferenceMany)");

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
  CALL("Inference::Inference(SimplifyingInference1)");

  init1(si.rule,si.premise);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS(si.premise->isClause());

  _age = si.premise->age();
}

Inference::Inference(const SimplifyingInference2& si) {
  CALL("Inference::Inference(SimplifyingInference2)");

  init2(si.rule,si.premise1,si.premise2);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS(si.premise1->isClause());
  ASS(si.premise2->isClause());

  _age = si.premise1->age();
}

Inference::Inference(const SimplifyingInferenceMany& si) {
  CALL("Inference::Inference(SimplifyingInferenceMany)");

  initMany(si.rule,si.premises);

  ASS_REP(isSimplifyingInferenceRule(si.rule),ruleName(si.rule));
  ASS_NEQ(si.premises,UnitList::empty());
  ASS(si.premises->head()->isClause()); // TODO: assert also for all others?

  _age = si.premises->head()->inference().age();
}

Inference::Inference(const NonspecificInference0& gi) {
  CALL("Inference::Inference(GenericInference0)");

  init0(gi.inputType,gi.rule);
}

Inference::Inference(const NonspecificInference1& gi) {
  CALL("Inference::Inference(GenericInference1)");

  init1(gi.rule,gi.premise);
}

Inference::Inference(const NonspecificInference2& gi) {
  CALL("Inference::Inference(GenericInference2)");

  init2(gi.rule,gi.premise1,gi.premise2);
}

Inference::Inference(const NonspecificInferenceMany& gi) {
  CALL("Inference::Inference(GenericInferenceMany)");

  initMany(gi.rule,gi.premises);
}

void Inference::minimizePremises()
{
  CALL("Inference::minimizePremises");

  if (_kind != Kind::INFERENCE_FROM_SAT_REFUTATION)
    return;
  if (_ptr2 == nullptr)
    return; // already minimized

  TimeCounter tc(TC_SAT_PROOF_MINIMIZATION);

  FromSatRefutationInfo* info = static_cast<FromSatRefutationInfo*>(_ptr2);

  SATClauseList* minimized = MinisatInterfacing::minimizePremiseList(info->_satPremises,info->_usedAssumptions);

  SATClause* newSatRef = new(0) SATClause(0);
  newSatRef->setInference(new PropInference(minimized));

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

/**
 * Return the rule name, such as "binary resolution".
 * @since 04/01/2008 Torrevieja
 */
vstring Kernel::ruleName(InferenceRule rule)
{
  CALL("Kernel::ruleName");

  switch (rule) {
  case InferenceRule::INPUT:
    return "input";
  case InferenceRule::NEGATED_CONJECTURE:
    return "negated conjecture";
  case InferenceRule::ANSWER_LITERAL:
  case InferenceRule::ANSWER_LITERAL_RESOLVER:
    return "answer literal";
  case InferenceRule::RECTIFY:
    return "rectify";
  case InferenceRule::CLOSURE:
    return "closure";
  case InferenceRule::FLATTEN:
    return "flattening";
  case InferenceRule::FOOL_ELIMINATION:
    return "fool elimination";
  case InferenceRule::FOOL_ITE_ELIMINATION:
    return "fool $ite elimination";
  case InferenceRule::FOOL_LET_ELIMINATION:
    return "fool $let elimination";
  case InferenceRule::FOOL_PARAMODULATION:
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
  case InferenceRule::REORDER_LITERALS:
    return "literal reordering";
  case InferenceRule::ENNF:
    return "ennf transformation";
  case InferenceRule::NNF:
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
  case InferenceRule::CLAUSIFY:
    return "cnf transformation";
  case InferenceRule::FORMULIFY:
    return "formulify";
  case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    return "duplicate literal removal";
  case InferenceRule::SKOLEMIZE:
    return "skolemisation";
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
  case InferenceRule::SUBSUMPTION_RESOLUTION:
    return "subsumption resolution";
  case InferenceRule::SUPERPOSITION:
    return "superposition";
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
  case InferenceRule::THEORY_NORMALIZATION:
    return "theory normalization";
  case InferenceRule::EVALUATION:
    return "evaluation";
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
  case InferenceRule::GROUNDING:
    return "grounding";
  case InferenceRule::EQUALITY_AXIOM:
    return "equality axiom";
  case InferenceRule::CHOICE_AXIOM:
    return "choice axiom";
  case InferenceRule::SIMPLIFY_PROVER_DISTINCT_NUMBERS_AXIOM:
    return "distinct numbers";
  case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    return "theory tautology sat conflict";
  case InferenceRule::GENERIC_THEORY_AXIOM:
  case InferenceRule::THA_COMMUTATIVITY:
  case InferenceRule::THA_ASSOCIATIVITY:
  case InferenceRule::THA_RIGHT_IDENTINTY:
  case InferenceRule::THA_LEFT_IDENTINTY:
  case InferenceRule::THA_INVERSE_OP_OP_INVERSES:
  case InferenceRule::THA_INVERSE_OP_UNIT:
  case InferenceRule::THA_INVERSE_ASSOC:
  case InferenceRule::THA_NONREFLEX:
  case InferenceRule::THA_TRANSITIVITY:
  case InferenceRule::THA_ORDER_TOTALALITY:
  case InferenceRule::THA_ORDER_MONOTONICITY:
  case InferenceRule::THA_PLUS_ONE_GREATER:
  case InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY:
  case InferenceRule::THA_MINUS_MINUS_X:
  case InferenceRule::THA_TIMES_ZERO:
  case InferenceRule::THA_DISTRIBUTIVITY:
  case InferenceRule::THA_DIVISIBILITY:
  case InferenceRule::THA_MODULO_MULTIPLY:
  case InferenceRule::THA_MODULO_POSITIVE:
  case InferenceRule::THA_MODULO_SMALL:
  case InferenceRule::THA_DIVIDES_MULTIPLY:
  case InferenceRule::THA_NONDIVIDES_SKOLEM:
  case InferenceRule::THA_ABS_EQUALS:
  case InferenceRule::THA_ABS_MINUS_EQUALS:
  case InferenceRule::THA_QUOTIENT_NON_ZERO:
  case InferenceRule::THA_QUOTIENT_MULTIPLY:
  case InferenceRule::THA_EXTRA_INTEGER_ORDERING:
  case InferenceRule::THA_FLOOR_SMALL:
  case InferenceRule::THA_FLOOR_BIG:
  case InferenceRule::THA_CEILING_BIG:
  case InferenceRule::THA_CEILING_SMALL:
  case InferenceRule::THA_TRUNC1:
  case InferenceRule::THA_TRUNC2:
  case InferenceRule::THA_TRUNC3:
  case InferenceRule::THA_TRUNC4:
  case InferenceRule::THA_ARRAY_EXTENSIONALITY:
  case InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY:
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE1:
  case InferenceRule::THA_BOOLEAN_ARRAY_WRITE2:
  case InferenceRule::THA_ARRAY_WRITE1:
  case InferenceRule::THA_ARRAY_WRITE2:
    return "theory axiom";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    return "term algebras acyclicity";
  case InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    return "term algebras discriminators";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    return "term algebras distinctness";
  case InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    return "term algebras exhaustiveness";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    return "term algebras injectivity";
  case InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE:
  case InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
    return "fool axiom";
  case InferenceRule::EXTERNAL_THEORY_AXIOM:
    return "external theory axiom";
  case InferenceRule::TERM_ALGEBRA_ACYCLICITY:
    return "term algebras acyclicity";
  case InferenceRule::TERM_ALGEBRA_DISTINCTNESS:
    return "term algebras distinctness";
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_GENERATING:
  case InferenceRule::TERM_ALGEBRA_INJECTIVITY_SIMPLIFYING:
    return "term algebras injectivity";
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
  case InferenceRule::INSTANCE_GENERATION:
    return "instance generation";
  case InferenceRule::UNIT_RESULTING_RESOLUTION:
    return "unit resulting resolution";
  case InferenceRule::HYPER_SUPERPOSITION_SIMPLIFYING:
  case InferenceRule::HYPER_SUPERPOSITION_GENERATING:
    return "hyper superposition";
  case InferenceRule::GLOBAL_SUBSUMPTION:
    return "global subsumption";
  case InferenceRule::SAT_INSTGEN_REFUTATION:
    return "sat instgen refutation";
  case InferenceRule::DISTINCT_EQUALITY_REMOVAL:
    return "distinct equality removal";
  case InferenceRule::EXTERNAL:
    return "external";
  case InferenceRule::CLAIM_DEFINITION:
    return "claim definition";
  case InferenceRule::BFNT_FLATTENING:
    return "bfnt flattening";
  case InferenceRule::BFNT_DISTINCT:
    return "bfnt distinct";
  case InferenceRule::BFNT_TOTALITY:
    return "bfnt totality";
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
  case InferenceRule::MODEL_NOT_FOUND:
    return "finite model not found";
  case InferenceRule::INDUCTION_AXIOM:
    return "induction hypothesis";
  case InferenceRule::GEN_INDUCTION_AXIOM:
    return "generalized induction hypothesis";
  default:
    ASSERTION_VIOLATION;
    return "!UNKNOWN INFERENCE RULE!";
  }
} // Inference::name()


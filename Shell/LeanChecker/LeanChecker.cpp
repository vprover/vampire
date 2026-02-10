#include "LeanChecker.hpp"
#include "Forwards.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Unit.hpp"
#include "LeanPrinter.hpp"
#include "SAT/SATSolver.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include "VariablePrenexOrderingTree.hpp"
#include <deque>
#include <initializer_list>
#include <map>
#include <ostream>

namespace Shell {
using namespace LeanPrinter;

template <unsigned N, typename T>
std::array<T *, N> getParents(T *unit)
{
  std::array<T *, N> parents;
  UnitIterator it = unit->getParents();
  for (unsigned i = 0; i < N; i++) {
    ALWAYS(it.hasNext())
    parents[i] = static_cast<T *>(it.next());
  }
  ALWAYS(!it.hasNext())
  return parents;
}


bool LeanChecker::isUncheckedInference(const InferenceRule &rule)
{
  switch (rule) {
    case InferenceRule::INPUT:
    case InferenceRule::DISTINCTNESS_AXIOM:
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::AVATAR_COMPONENT:
    case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    // Skolemization is only handled later in the full proof
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::SKOLEMIZE:
    case InferenceRule::PREDICATE_DEFINITION:
    case InferenceRule::NEGATED_CONJECTURE:
    case InferenceRule::FUNCTION_DEFINITION:
    case InferenceRule::DEFINITION_FOLDING_PRED:
      return true;
    default:
      return false;
  }
}

bool LeanChecker::isUncheckedInProof(const InferenceRule &rule)
{
  if(isTheoryAxiomRule(rule)){
    return true;
  }
  switch (rule) {
    case InferenceRule::INPUT:
    case InferenceRule::DISTINCTNESS_AXIOM:
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::AVATAR_COMPONENT:
    case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::NEGATED_CONJECTURE:
      return true;
    default:
      return false;
  }  
}

bool LeanChecker::inferenceNeedsReplayInfromation(const InferenceRule &rule)
{
  switch (rule) {
    case InferenceRule::RESOLUTION:
    case InferenceRule::FACTORING:
    case InferenceRule::EQUALITY_RESOLUTION:
    case InferenceRule::SUPERPOSITION:
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
      return true;
    default:
      return false;
  }
}

void LeanChecker::print()
{
  std::deque<Unit*> inputPremises;
  std::deque<Unit*> negatedConjectures;
  outputPreamble(out);

  for (Unit *u : proof) {
    if(u->inference().rule() == InferenceRule::INPUT){
      inputPremises.push_back(u);
    } else if (u->inference().rule() == InferenceRule::NEGATED_CONJECTURE){
      negatedConjectures.push_back(u);
    }
    outputInferenceStep(out, u);
  }
  outputFullProofPreamble(out, inputPremises, negatedConjectures);
  for (Unit *u : proof) {
    outputProofStep(out, u);
  }
  out << indent << "exact " << stepIdent << (*proof.rbegin())->number() << "\n\n";
}

void LeanChecker::outputPreamble(std::ostream &out)
{
  out << preambleLean << "\n";

  Signature &sig = *env.signature;

  //Default sort
  out << "variable {" << SortName(sig.getDefaultSort()) << " : Type u}\n";
  out << "variable [inst : Inhabited " << SortName(sig.getDefaultSort()) << "]\n";

  //
  for (unsigned i = Signature::FIRST_USER_CON; i < sig.typeCons(); i++) {
    out << "variable {" << SortName(i) << " : Type u}\n";
    out << "variable [inst : Inhabited " << SortName(i) << "]\n";
  }

  for (unsigned i = 0; i < sig.functions(); i++) {
    Signature::Symbol *fun = sig.getFunction(i);
    if (fun->interpreted() || fun->linMul())
      continue;

    auto name = FunctionName(fun);
    out << "variable {" << name;
    OperatorType *type = fun->fnType();
    TermList range = type->result();

    ASS_EQ(type->numTypeArguments(), 0)
    out << " : (";
    int arity = 0;
    // we don't support polymorphism yet
    arity = type->arity();
    for (unsigned i = 0; i < arity; i++) {
      out << (i == 0 ? "" : " → ") << Sort{type->arg(i)};
    }
    if(range.isNonEmpty()){
      out << (arity == 0 ? "" : " → ") << Sort{range} << ") }";
    }
    out << "\n";
  }

  for (unsigned i = 0; i < sig.predicates(); i++) {
    Signature::Symbol *fun = sig.getPredicate(i);
    if (fun->interpreted())
      continue;

    out << "variable {" << PredicateName(fun);
    OperatorType *type = fun->fnType();
    TermList resRange = type->result();

    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)
    out << " : (";
    for (unsigned i = 0; i < type->arity(); i++) {
      out << (i == 0 ? "" : " → ") << Sort{type->arg(i)};
    }
    if(resRange.isNonEmpty()){
      out <<  (type->arity() == 0 ? "" : " → ") << resRange << ")}\n";
    } else {
      out << (type->arity() == 0 ? "" : " → ") << "Prop)}\n";
    }
  }
}

void LeanChecker::outputFullProofPreamble(std::ostream &out, std::deque<Unit*> premises, std::deque<Unit*> negatedConjectures){
  out << "theorem fullProof : ";
  for(Unit* input : premises){
    outputUnit(out, input);
    out << " → ";
  }
  for(auto iter = negatedConjectures.begin(); iter != negatedConjectures.end(); ++iter){
    auto [parent] = getParents<1>(*iter);
    outputUnit(out, parent);
    if(std::next(iter) != negatedConjectures.end()){
      out << " → ";
    }
  }
  if(negatedConjectures.empty()){
    out << "False";
  } 
  out << " := by\n" << indent << "intros ";
  for(Unit* input : premises){
    out << stepIdent << input->number() << " ";
  }
  out << "\n";
  for(Unit* negConj : negatedConjectures){
    out << indent << "by_contra " << stepIdent << negConj->number() << "\n";
  }
}

void LeanChecker::outputProofStep(std::ostream &out, Kernel::Unit *u)
{
  const InferenceRule& rule = u->inference().rule();
  if (isUncheckedInProof(rule)) {
    return;
  }
  SortMap conclSorts;
  SortHelper::collectVariableSorts(u, conclSorts);
  if (rule == InferenceRule::SKOLEMIZE) {
    skolemize(out, conclSorts, u);
  } else if (rule == InferenceRule::PREDICATE_DEFINITION){
    predicateDefinitionIntroduction(out, conclSorts, u);
  } else if (rule == InferenceRule::FUNCTION_DEFINITION){
    functionDefinitionIntroduction(out, conclSorts, u);
  } else if (rule == InferenceRule::DEFINITION_FOLDING_PRED){
    definitionFoldingPred(out, conclSorts, u);
  } else {
    out << indent << "have " << stepIdent << u->number() << " := inf_s" << u->number() << " ";
    for (auto parents = u->getParents(); parents.hasNext();) {
      Unit *parent = parents.next();
      out << " " << stepIdent << parent->number();
    }
    out << "\n";
  }
}

void LeanChecker::outputInferenceStep(std::ostream &out, Kernel::Unit *u){
  const InferenceRule& rule = u->inference().rule();
  if(isUncheckedInference(rule)){
    return;
  }
  out << "-- step " << u->number() << " " << ruleName(rule) << "\n";

  //outputUnitBeginning(out, u);

  SortMap conclSorts;
  SortHelper::collectVariableSorts(u, conclSorts);

  const InferenceRecorder::InferenceInformation* info = nullptr;
  if(inferenceNeedsReplayInfromation(u->inference().rule())){
    InferenceRecorder::instance()->setCurrentGoal(u->asClause());
    _replayer.replayInference(u);
    info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
  }
  if(isTheoryAxiomRule(u->inference().rule())){
    out << "axiom " << stepIdent << u->number() << " : ";
    outputUnit(out, u);
    out << "\n\n";
    return;
  } else {
    out << "theorem inf_s" << u->number() << " : ";
  }
  switch(u->inference().rule()){
    case InferenceRule::RESOLUTION: 
      resolution(out, conclSorts, u->asClause(), info);
      break;
    case InferenceRule::SUPERPOSITION:
      superposition(out, conclSorts, u->asClause(), info);
      break;
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
      demodulation(out, conclSorts, u->asClause(),info);
      break;
    case InferenceRule::FACTORING:
      factoring(out, conclSorts, u->asClause(), info);
      break;
    case InferenceRule::EQUALITY_RESOLUTION:
      equalityResolution(out, conclSorts, u->asClause(), info);
      break;
    case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
      subsumptionResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::DEFINITION_UNFOLDING:
      genericNPremiseInferenceNoSubs(out, conclSorts, u->asClause());
      break;
    case InferenceRule::DEFINITION_FOLDING_TWEE:
      definitionFoldingTwee(out, conclSorts, u->asClause());
      break;
    case InferenceRule::EVALUATION:
      genericNPremiseInferenceNoSubs(out, conclSorts, u->asClause(), 
      "norm_num1<;> norm_num1 at " + intIdent + "0 <;> simp_all\n");
      break;
    case InferenceRule::NNF:
    case InferenceRule::ENNF:
    case InferenceRule::FLATTEN:
    case InferenceRule::RECTIFY:
    case InferenceRule::REDUCE_FALSE_TRUE:
    case InferenceRule::THEORY_NORMALIZATION:
      normalForm(out, conclSorts, u);
      break;
    case InferenceRule::CLAUSIFY:
      clausify(out, conclSorts, u);
      break;
    default:
      genericInference(out, conclSorts, u);
  }
}

unsigned LeanChecker::outputPremises(std::ostream &out, Unit *u){
  UnitIterator parents = u->getParents();
  unsigned count = 0;
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    outputUnit(out, parent);
    count++;
    if(parents.hasNext()){
      out << " →\n" << indent;
    }
  }
  return count;
}

void LeanChecker::outputPremiseAndConclusion(std::ostream &out, Unit *concl){
  unsigned premiseCount = outputPremises(out, concl);
  if(premiseCount > 0){
    out << " →\n" << indent;
  }
  outputUnit(out, concl);
}

void LeanChecker::genericInference(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic){
  
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << tactic << "\n\n";
}

void LeanChecker::instantiateConclusionVars(std::ostream &out, SortMap &conclSorts, Unit *concl){
  VirtualIterator<unsigned> domain = conclSorts.domain();
  outputVariables(out, domain, conclSorts, conclSorts);
}

void LeanChecker::genericNPremiseInference(std::ostream &out, SortMap &conclSorts, Clause *concl, std::initializer_list<Substitution> substitutions, std::string tactic){
  auto parents = concl->getParents();
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros ";
  for(unsigned i = 0; i < substitutions.size(); i++){
    out << "h" << i << " ";
  }
  instantiateConclusionVars(out, conclSorts, concl);
  for (unsigned i = 0; i < substitutions.size(); i++) {
    ASS(parents.hasNext())
    auto parent = parents.next();
    ASS(parent->isClause())
    out << "\n" << indent << "have " << intIdent << i << " := h"<<i<<" ";
    instantiatePremiseVars(out, conclSorts, parent->asClause(), DoSubst(substitutions.begin()[i]));
  }
  out << "\n" << indent << tactic << "\n\n";
}

void LeanChecker::genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Clause *concl, std::string tactic){
  auto parents = concl->getParents();
  unsigned size = 0;
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros ";
  while(parents.hasNext()){
    parents.next();
    out << "h" << size << " ";
    size++;
  }
  parents = concl->getParents();
  instantiateConclusionVars(out, conclSorts, concl);
  for (unsigned i = 0; i < size; i++) {
    ASS(parents.hasNext())
    auto parent = parents.next();
    ASS(parent->isClause())
    out << "\n" << indent << "have " << intIdent << i << " := h"<<i<<" ";
    instantiatePremiseVars(out, conclSorts, parent->asClause());
  }
  out << "\n" << indent << tactic << "\n\n";
}

void LeanChecker::genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic){
  if(concl->isClause()){
    genericNPremiseInferenceNoSubs(out,conclSorts,concl->asClause(), tactic);
    return;
  }
  auto parents = concl->getParents();
  unsigned size = 0;
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros ";
  while(parents.hasNext()){
    parents.next();
    out << "h" << size << " ";
    size++;
  }
  parents = concl->getParents();
  instantiateConclusionVars(out, conclSorts, concl);
  for (unsigned i = 0; i < size; i++) {
    ASS(parents.hasNext())
    auto parent = parents.next();
    out << "\n" << indent << "have " << intIdent << i << " := h"<<i<<" ";
    instantiatePremiseVars(out, conclSorts, parent);
  }
  out << "\n" << indent << tactic << "\n\n";
}

void LeanChecker::resolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const Shell::InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0], info->substitutionForBanksSub[1]}, "exact resolve " + intIdent + "0 " + intIdent + "1");
}

void LeanChecker::subsumptionResolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto sr = env.proofExtra.get<Inferences::LiteralInferenceExtra>(concl);
  Literal *m = sr.selectedLiteral;

  // reconstruct match by calling into the SATSR code
  SATSubsumption::SATSubsumptionAndResolution satSR;
  ALWAYS(satSR.checkSubsumptionResolutionWithLiteral(right, left, left->getLiteralPosition(m)))
  auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();

  genericNPremiseInference(out, conclSorts, concl, {Substitution(), subst}, "grind only");
}

void LeanChecker::factoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only");
}

void LeanChecker::equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info)
{
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only");
}

void LeanChecker::superposition(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0], info->substitutionForBanksSub[1]}, "grind only");
}

void LeanChecker::demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {Substitution(), info->substitutionForBanksSub[0]}, "grind only");
}

void LeanChecker::clausify(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto [parent] = getParents<1>(concl);
  SortMap parentMap;
  SortHelper::collectVariableSorts(parent, parentMap);
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros h ";
  instantiateConclusionVars(out, conclSorts, concl);
  out << "\n" << indent << "prenexify at h \n" << indent << "have h1 := h ";
  VariablePrenexOrderingTree tree; 
  tree.buildTreeFromFormula(parent->getFormula(), Kernel::FORALL);
  auto ordering = tree.determineVariableOrdering();
  outputVariables(out, ordering, conclSorts, parentMap, Identity{}, 0);
  out << "\n" << indent << "grind only\n\n";
}

void LeanChecker::predicateDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl){
  //auto [parent] = getParents<1>(concl);
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  auto introducedFunctionSymbols = _is->getIntroducedSymbols(concl);
  ASS(introducedFunctionSymbols.size() == 1);
  unsigned sym = introducedFunctionSymbols.top().second;
  auto pred = env.signature->getPredicate(sym);
  auto formula = _is->formulaReplacedByIntroducedSymbol(sym);
  
  ASS(!concl->isClause())
  ASS(concl->getFormula()->connective()==Kernel::FORALL);
  auto fDomain = concl->getFormula()->vars();
  
  out << indent << "let " << PredicateName(pred);

  auto fDomainIter = fDomain->iter();
  out << " ";
  outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, -1, true);
  out << " := ";
  outputFormula(out, formula, &conclSorts);
  out << "\n" << indent << "have "<< stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by\n" << indent << indent << "intros ";
  fDomainIter = fDomain->iter();
  outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 1, false);
  out << "\n" << indent << indent << "have s : ";
  outputFormula(out, formula);
  out << " ↔ " << PredicateName(pred) << " ";
  fDomainIter = fDomain ->iter();
  outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, -1, false);
  out << " := Iff.rfl\n" << indent << indent;
  out << "(first | exact s | exact or_comm.mp (imp_iff_not_or.mp s.mpr) | exact imp_iff_not_or.mp s.mp)\n\n";
}

void LeanChecker::functionDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl){
  //auto [parent] = getParents<1>(concl);
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  auto introducedFunctionSymbols = _is->getIntroducedSymbols(concl);
  out << indent << "let " << FunctionName(env.signature->getFunction(introducedFunctionSymbols.top().second)) << " := ";
  auto x = concl->asClause()->literals()[0];
  ASS(x->isEquality())
  auto lhsEqDefinition = x->termArg(0);
  out << Args{&lhsEqDefinition, conclSorts, conclSorts} << "\n";
  out << indent << "have " << stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := rfl\n";
}

void LeanChecker::definitionFoldingTwee(std::ostream &out, SortMap &conclSorts, Clause *concl){
  genericNPremiseInferenceNoSubs(out, conclSorts, concl);
}

void LeanChecker::definitionFoldingPred(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto [left, right] = getParents<2>(concl);
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  out << indent << "have " << stepIdent << concl->number() << " := " << stepIdent << left->number() << "\n";
  out << indent << "change ";
  outputUnit(out, concl);
  out << " at " << stepIdent << concl->number() << "\n";
}

void LeanChecker::normalForm(std::ostream &out, SortMap &conclSorts, Unit *concl){
  outputPremiseAndConclusion(out, concl);
  out << " := by\n";
  auto rule = concl->inference().rule();
  if (rule == InferenceRule::ENNF) {
    out << "  intros h\n";
    out << "  ennf_transformation at h\n";
    out << "  exact h\n";
  }
  else if (rule == InferenceRule::FLATTEN) {
    out << "  intro h\n";
    out << "  flattening at h\n";
    out << "  first | exact h | grind | omega | aesop | sorry\n";
  }
  else if (rule == InferenceRule::NNF) {
    out << "  intro h\n";
    out << "  nnf_transformation at h\n";
    out << "  first | exact h | grind | omega | aesop | sorry\n";
  }
  else if (rule == Kernel::InferenceRule::RECTIFY) {
    out << "  exact fun x => x\n";
  }
  else if (rule == Kernel::InferenceRule::REDUCE_FALSE_TRUE) {
    out << "  intro h\n";
    out << "  remove_tauto at h\n";
    out << "  first | exact h | grind | omega | aesop | sorry\n";
  } else if (rule == InferenceRule::THEORY_NORMALIZATION) {
    out << "  intro h\n";
    out << "  try simp only [← not_lt, gt_iff_lt] at h\n";
    out << "  first | exact h | grind | omega | aesop | sorry\n";
  }
  out << "\n";
}
void LeanChecker::skolemize(std::ostream &out, SortMap &conclSorts, Unit *concl){
  UnitIterator parents = concl->getParents();
  // The first parent is the original formula
  Unit *parent = parents.next();

  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";

  ASS(_is->hasIntroducedSymbols(concl))
  auto syms = _is->getIntroducedSymbols(concl).iter();
  
  std::map<unsigned,Signature::Symbol*> replacedVarMap;
  while(syms.hasNext()){
    unsigned symNum = syms.next().second;
    long replacedVar = _is->variableReplacedByIntroducedSymbol(symNum);
    ASS(replacedVar != -1)
    replacedVarMap[replacedVar] = env.signature->getFunction(symNum);
  }
  VariablePrenexOrderingTree tree;
  tree.buildTreeFromFormula(parent->getFormula(), Kernel::EXISTS);
  out << indent << "exists_prenex at "<< stepIdent;
  out << parent->number() << "\n";
  out << indent << "choose ";
  for (unsigned var : *tree.determineVariableOrdering()) {
    out << FunctionName(replacedVarMap[var]) << " ";
  }
  out << " step" << concl->number() << "' using step" << parent->number() << "\n";
  out << indent << "have step" << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by symm_match using " << stepIdent << concl->number() << "'\n";
}


void LeanChecker::axiom(std::ostream &out, SortMap &conclSorts, Unit *concl)
{
}

} // namespace Shell
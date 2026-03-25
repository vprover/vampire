#include "LeanChecker.hpp"
#include "Forwards.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/MLVariant.hpp"
#include "LeanPrinter.hpp"
#include "Lib/Metaiterators.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/FunctionDefinition.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include "VariablePrenexOrderingTree.hpp"
#include <algorithm>
#include <cstdlib>
#include <deque>
#include <initializer_list>
#include <map>
#include <ostream>
#include <utility>
#include <vector>

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
    //definitions are handled later
    case InferenceRule::AVATAR_DEFINITION:
    // Skolemization is only handled later in the full proof
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::SKOLEMIZE:
    case InferenceRule::PREDICATE_DEFINITION:
    case InferenceRule::NEGATED_CONJECTURE:
    case InferenceRule::FUNCTION_DEFINITION:
    case InferenceRule::DEFINITION_FOLDING_PRED:
    case InferenceRule::CLAUSIFY:
      return true;
    default:
      return false;
  }
}

bool LeanChecker::isUncheckedInProof(const InferenceRule &rule)
{
  switch (rule) {
    case InferenceRule::INPUT:
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::NEGATED_CONJECTURE:
      return true;
    default:
      return false;
  }  
}

bool LeanChecker::inferenceNeedsReplayInformation(const InferenceRule &rule)
{
  switch (rule) {
    case InferenceRule::RESOLUTION:
    case InferenceRule::FACTORING:
    case InferenceRule::EQUALITY_RESOLUTION:
    case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    case InferenceRule::EQUALITY_FACTORING:
    case InferenceRule::SUPERPOSITION:
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
    case InferenceRule::RECTIFY:
      return true;
    default:
      return false;
  }
}

bool LeanChecker::doesOutputSplits(const InferenceRule &rule)
{
  switch (rule) {
    case InferenceRule::AVATAR_COMPONENT:
      return false;
    default:
      return true;
  }
}

void LeanChecker::print()
{
  std::deque<Unit*> inputPremises;
  std::deque<Unit*> negatedConjectures;
  std::set<Signature::Symbol*> usedFunctionSymbols;
  std::set<Signature::Symbol*> usedPredicateSymbols;
  std::set<Signature::Symbol*> functionSymbolsInUsedInput;
  std::set<Signature::Symbol*> predicateSymbolsInUsedInput;

  //Collect used symbols for the preamble
  for (Unit *u : proof) {

    if(u->isClause()){
      SymbolHelper::collectUsedSymbols(u->asClause(), usedFunctionSymbols, SymbolHelper::SymbolType::FUNCTION);
      SymbolHelper::collectUsedSymbols(u->asClause(), usedPredicateSymbols, SymbolHelper::SymbolType::PREDICATE);
      if(u->inference().rule() == InferenceRule::INPUT){
        SymbolHelper::collectUsedSymbols(u->asClause(), functionSymbolsInUsedInput, SymbolHelper::SymbolType::FUNCTION);
        SymbolHelper::collectUsedSymbols(u->asClause(), predicateSymbolsInUsedInput, SymbolHelper::SymbolType::PREDICATE);
      }
    } else {
      SymbolHelper::collectUsedSymbols(u->getFormula(), usedFunctionSymbols, SymbolHelper::SymbolType::FUNCTION);
      SymbolHelper::collectUsedSymbols(u->getFormula(), usedPredicateSymbols, SymbolHelper::SymbolType::PREDICATE);
      if(u->inference().rule() == InferenceRule::INPUT){
        SymbolHelper::collectUsedSymbols(u->getFormula(), functionSymbolsInUsedInput, SymbolHelper::SymbolType::FUNCTION);
        SymbolHelper::collectUsedSymbols(u->getFormula(), predicateSymbolsInUsedInput, SymbolHelper::SymbolType::PREDICATE);
      }
    }
  }

  std::set <Signature::Symbol*> unusedFunctionSymbols;
  std::set <Signature::Symbol*> unusedPredicateSymbols;
  std::set_difference(usedFunctionSymbols.begin(), usedFunctionSymbols.end(), functionSymbolsInUsedInput.begin(), functionSymbolsInUsedInput.end(), std::inserter(unusedFunctionSymbols, unusedFunctionSymbols.end()));
  std::set_difference(usedPredicateSymbols.begin(), usedPredicateSymbols.end(), predicateSymbolsInUsedInput.begin(), predicateSymbolsInUsedInput.end(), std::inserter(unusedPredicateSymbols, unusedPredicateSymbols.end()));


  outputPreamble(out, usedFunctionSymbols, usedPredicateSymbols);
  outputCumulativeSplits(proof, " ", "sA" ,"variable {", " : Prop}\n");

  for (Unit *u : proof) {
    if(u->inference().rule() == InferenceRule::INPUT){
      if (u->inference().inputType() != UnitInputType::CONJECTURE) {
        inputPremises.push_back(u);
      }
    } else if (u->inference().rule() == InferenceRule::NEGATED_CONJECTURE){
      negatedConjectures.push_back(u);
    }
    outputInferenceStep(out, u);
  }
  outputFullProofPreamble(out, inputPremises, negatedConjectures, unusedFunctionSymbols, unusedPredicateSymbols);
  for (Unit *u : proof) {
    outputProofStep(out, u);
  }
  out << indent << "exact " << stepIdent << (*proof.rbegin())->number() << "\n\n";
  out << "end vamproof" << "\n";
}

void LeanChecker::outputPreamble(std::ostream &out, std::set<Signature::Symbol*> usedFunctionSymbols, std::set<Signature::Symbol*> usedPredicateSymbols)
{
  out << preambleLean << "\n";

  Signature &sig = *env.signature;

  //Default sort
  out << "variable {" << SortName(sig.getDefaultSort()) << " : Type u}\n";
  out << "variable [inst : Inhabited " << SortName(sig.getDefaultSort()) << "]\n";

  for (unsigned i = Signature::FIRST_USER_CON; i < sig.typeCons(); i++) {
    out << "variable {" << SortName(i) << " : Type u}\n";
    out << "variable [inst : Inhabited " << SortName(i) << " ]\n";
  }

  out << "variable {df : Nat → (α : Type u) → (α → ι)}\n"
      << "variable {dcf : Nat → ι}\n"
      << "variable {dp : Nat → (α : Type u) → α → Prop}\n"
      << "variable {dcp : Nat → Prop}\n";

  unsigned variableCounter = 0;

  for (auto fun : usedFunctionSymbols) {
    if (fun->interpreted() || fun->linMul() || fun->introduced())
      continue;
    OperatorType *type = fun->fnType();
    TermList range = type->result();
    ASS_EQ(type->numTypeArguments(), 0)
    if(type->arity() == 0) {
      out << "def " << FunctionName(fun) << " := dcf " << variableCounter++ << "\n";
      continue;
    }
    out << "def " << FunctionName(fun) << ": (";
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? " " : " → ") << Sort{type->arg(i)};
    }
    if(range.isNonEmpty()){
      out << " → " << Sort{range};
    }
    out << ") ";

    out << " := fun ";
    for (unsigned i = 0; i < type->arity(); i++){
      out << "x" << i << " ";
    }
    out << " => (df " << variableCounter++;
    out << " (";
    for (unsigned i = 0; i < type->arity(); i++) {
      out << (i == 0 ? "" : " × ") << Sort{type->arg(i)};
    }
    out << ") (";
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? "" : ", ") << "x" << i;
    }
    out << "))\n";
  }
  
  for (auto pred : usedPredicateSymbols) {
    if (pred->interpreted() || pred->skolem() || pred->introduced())
      continue;
    OperatorType *type = pred->fnType();
    TermList resRange = type->result();
    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)

    if(type->arity() == 0) {
      out << "def " << PredicateName(pred) << " := dcp " << variableCounter++ << "\n";
      continue;
    }
    out << "def " << PredicateName(pred) << ": (";
  
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? " " : " → ") << Sort{type->arg(i)};
    }
    out << " → Prop) ";

    out << " := fun ";
    for (unsigned i = 0; i < type->arity(); i++){
      out << "x" << i << " ";
    }
    out << " => (dp " << variableCounter++;
    //output input args
    out << " (";
    for (unsigned i = 0; i < type->arity(); i++) {
      out << (i == 0 ? "" : " × ") << Sort{type->arg(i)};
    }
    out << ") (";
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? "" : ", ") << "x" << i;
    }
    out << "))\n";
  }
    
  bool firstVariableDef = true;
  std::map<OperatorType*, std::vector<Signature::Symbol*>> funMap;
  for(auto fun : usedFunctionSymbols){
    if(fun->introduced()){
      if(funMap.find(fun->fnType()) == funMap.end()){
        funMap.emplace(fun->fnType(), std::vector<Signature::Symbol*>());
      }
      funMap[fun->fnType()].push_back(fun);
    }
  }
  for (auto [type, funcs] : funMap){
    TermList range = type->result();
    ASS_EQ(type->numTypeArguments(), 0)
    if(firstVariableDef){
      out << "variable ";
      firstVariableDef = false;
    } else {
      out << indent;
    }
    out << "{";
    for(auto fun : funcs){
      out << FunctionName(fun) << " ";
    }
    out << ": ";
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? " " : " → ") << Sort{type->arg(i)};
    }
    if(range.isNonEmpty()){
      out << (type->arity() != 0 ? " → " : "") << Sort{range};
    }
    out << "}\n";
  }
  std::map<OperatorType*, std::vector<Signature::Symbol*>> predMap;
  for(auto pred : usedPredicateSymbols){
    if(pred->introduced()){
      if(predMap.find(pred->fnType()) == predMap.end()){
        predMap.emplace(pred->fnType(), std::vector<Signature::Symbol*>());
      }
      predMap[pred->fnType()].push_back(pred);
    }
  }
  for (auto [type, preds] : predMap){
    ASS_EQ(type->numTypeArguments(), 0)
    if(firstVariableDef){
      out << "variable ";
      firstVariableDef = false;
    } else {
      out << indent;
    }
    out << "{";
    for(auto pred : preds){
      out << PredicateName(pred) << " ";
    }
    out << ": ";
    for (unsigned i = 0; i < type->arity(); i++){
      out << (i==0 ? " " : " → ") << Sort{type->arg(i)};
    }
    out << (type->arity() != 0 ? " → " : "") << "Prop}\n";
  }
}

void LeanChecker::outputFullProofPreamble(std::ostream &out, std::deque<Unit*> premises, std::deque<Unit*> negatedConjectures, std::set<Signature::Symbol*>& unusedFunctionSymbols, std::set<Signature::Symbol*>& unusedPredicateSymbols){
  //out << "set_option maxHeartbeats 200000000 in\n";
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
  out << " := by\n";
  
  /*for(Signature::Symbol* sym : unusedFunctionSymbols){
    if(sym->introduced()) {
      continue;
    }
    out << indent << "let " << FunctionName(sym) << " := ";
    for(unsigned i = 0; i < sym->arity(); i++){
      out << "fun x" << i << " : " << Sort{sym->fnType()->arg(i)} << " => ";
    }
    out << "(default : " << Sort{sym->fnType()->result()} << ")\n";
  }
  for(Signature::Symbol* sym : unusedPredicateSymbols){
    if(sym->introduced()) {
      continue;
    }
    out << indent << "let " << PredicateName(sym) << " := ";
    for(unsigned i = 0; i < sym->arity(); i++){
      out << "fun x" << i << " : " << Sort{sym->fnType()->arg(i)} << " => ";
    }
    out << "False\n";
  }*/
  if(!premises.empty()){
    out << indent << "intros ";
    for(Unit* input : premises){
      out << stepIdent << input->number() << " ";
    }
  }
  
  out << "\n";
  for(Unit* negConj : negatedConjectures){
    out << indent << "apply Classical.byContradiction; intro " << stepIdent << negConj->number() << "\n";
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
  } else if (rule == InferenceRule::AVATAR_DEFINITION){
    avatarDefinitionIntroduction(out, conclSorts, u); 
  } else if (rule == InferenceRule::AVATAR_REFUTATION ||
             rule == InferenceRule::AVATAR_REFUTATION_SMT){
    avatarRefutationProofStep(out, conclSorts, u);
  } else if (rule == InferenceRule::CLAUSIFY) {
    clausify(out, conclSorts, u);
  } else if (isTheoryAxiomRule(rule) || rule == Kernel::InferenceRule::DISTINCTNESS_AXIOM){
    out << indent << "have " << stepIdent << u->number() << " : ";
    outputUnit(out, u);
    out << " := ax" << u->number() << "\n"; 
  } else {
    out << indent << "have " << stepIdent << u->number() << " := inf_s" << u->number() << " ";
    for (auto parent : iterTraits(u->getParents())) {
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

  SortMap conclSorts;
  SortHelper::collectVariableSorts(u, conclSorts);

  const InferenceRecorder::InferenceInformation* info = nullptr;
  const InferenceRecorder::RectifyInferenceExtra* rectifyInfo = nullptr;
  if(inferenceNeedsReplayInformation(u->inference().rule())){
    if(u->isClause()){
      InferenceRecorder::instance()->setCurrentGoal(u->asClause());
    }
    _replayer.replayInference(u);
    if(u->inference().rule() == InferenceRule::RECTIFY){
      rectifyInfo = static_cast<const InferenceRecorder::RectifyInferenceExtra*>(InferenceRecorder::instance()->getGenericLastInferenceInformation());
    } else {
      info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
    }
  }
  if(isTheoryAxiomRule(u->inference().rule()) || u->inference().rule() == Kernel::InferenceRule::DISTINCTNESS_AXIOM){
    out << "axiom " << "ax" << u->number() << " : ";
    outputUnit(out, u);
    out << "\n\n";
    return;
  } else {
    if(rule == InferenceRule::AVATAR_REFUTATION){
      out << "set_option maxHeartbeats 200000000 in\n-- this is probably due to a suboptimal encoding\n";
    }
    out << "theorem inf_s" << u->number();
    if(u->inference().rule()!=InferenceRule::AVATAR_REFUTATION
       && u->inference().rule()!=InferenceRule::AVATAR_REFUTATION_SMT){
      out << " : ";
    }
  }
  switch(u->inference().rule()){
    case InferenceRule::AVATAR_COMPONENT:
      avatarComponent(out, conclSorts, u);
      break;
    case InferenceRule::AVATAR_REFUTATION:
    case Kernel::InferenceRule::AVATAR_REFUTATION_SMT:
      avatarRefutation(out, conclSorts, u);
      break;
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
      avatarSplitClause(out, conclSorts, u);
      break;
    default:
      genericInference(out, conclSorts, u, "duper [*]");
  }
}

unsigned LeanChecker::outputPremises(std::ostream &out, Unit *u, std::string seperator){
  auto parents = iterTraits(u->getParents());
  unsigned count = 0;
  for(auto parent : parents) {
    outputUnit(out, parent);
    count++;
    if(parents.hasNext()){
      out << seperator << indent;
    }
  }
  return count;
}

void LeanChecker::outputPremiseAndConclusion(std::ostream &out, Unit *concl, std::string premiseSeperator){
  
  unsigned premiseCount = outputPremises(out, concl, premiseSeperator);
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
  if(concl->isClause()) {
    auto cl = concl->asClause();
    if(!cl->noSplits()){
      outputCumulativeSplits({cl}, " ", "x", true);
      out << " ";
    }
  }
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
  for([[maybe_unused]] auto _ : iterTraits(concl->getParents())) {
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
  //if(concl->isClause()){
  //  genericNPremiseInferenceNoSubs(out,conclSorts,concl->asClause(), tactic);
  //  return;
  //}
  unsigned size = 0;
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros ";
  for([[maybe_unused]] auto _ : iterTraits(concl->getParents())) {
    out << "h" << size << " ";
    size++;
  }
  UnitIterator parents = concl->getParents();
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
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0], info->substitutionForBanksSub[1]}, "grind only [cases Or]");
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

  genericNPremiseInference(out, conclSorts, concl, {Substitution(), subst}, "grind only [cases Or]");
}

void LeanChecker::factoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

void LeanChecker::equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info)
{
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

void LeanChecker::equalityFactoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info)
{
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

void LeanChecker::superposition(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0], info->substitutionForBanksSub[1]}, "grind only [cases Or]");
}

void LeanChecker::demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  if(info == nullptr){
    out << "PROBLEM IN DEMODULATION\n";
    exit(10);
  }
  genericNPremiseInference(out, conclSorts, concl, {Substitution(), info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

unsigned countConnectives(Formula *f)
{
  switch (f->connective()) {
    case AND:
    case OR: {
      unsigned thisCount=0;
      for(auto arg : iterTraits(f->args()->iter())){
        thisCount += 1+countConnectives(arg);
      }
      return thisCount;
    }
    case IMP:
    case IFF:
    case XOR: {
      return 1+countConnectives(f->left()) + countConnectives(f->right());
    }
    case NOT: {
      return 1+countConnectives(f->uarg());
    }
    case FORALL:
    case EXISTS: {
      return 1+countConnectives(f->qarg());
      
    }
    default:
      return 0;
  } 
}

void outputReorderIfNeeded(std::ostream &out, Unit* parent, SortMap &conclSorts, std::string indent){
  VariablePrenexOrderingTree prenexTree;
  prenexTree.buildTreeFromFormula(parent->getFormula(), Kernel::FORALL);
  std::vector<unsigned>* variableOrdering = prenexTree.determineVariableOrdering();
  //check if reordering is actually needed
  bool needsReorder = false;
  unsigned currentMin = 0;
  for(unsigned var : *variableOrdering){
    if(conclSorts.findPtr(var) != nullptr){
      if(var < currentMin){
        needsReorder = true;
        break;
      }
      currentMin = var;
    }
  }
  if(needsReorder){
    auto domain = conclSorts.domain();
    out << indent << indent << "have reorder" << " (P :";
    //Todo sort sorts here
    for(auto [var, sort] : iterTraits(conclSorts.items())){
      out << Sort{sort} << "→";
    }
    out << "Prop) : ";
    out << "( " << "∀ ";
    domain = conclSorts.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << ", P ";
    domain = conclSorts.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << ") ↔ (" << "∀ ";
    domain = conclSorts.domain();
    for(unsigned var : *variableOrdering){
      if(conclSorts.findPtr(var) != nullptr){
        out << "v" << var << " ";
      }
    }
    out << ", P ";
    domain = conclSorts.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << ") := Iff.intro (fun f ";
    for(unsigned var : *variableOrdering){
      if(conclSorts.findPtr(var) != nullptr){
        out << "v" << var << " ";
      }
    }
    out << " => f ";
    domain = conclSorts.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << ") (fun f ";
    domain = conclSorts.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << " => f ";
    for(unsigned var : *variableOrdering){
      if(conclSorts.findPtr(var) != nullptr){
        out << "v" << var << " ";
      }
    }
    out << ")\n"
        << indent << indent << "rw[reorder]\n";
  }
}

void LeanChecker::clausify(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto [parent] = getParents<1>(concl);
  //auto cnfExtra = env.proofExtra.get<Inferences::CNFTransformationInferenceExtra>(concl);
  auto cnfParentExtra = env.proofExtra.get<Inferences::CNFTransformationInferenceExtra>(parent);
  if(cnfParentExtra.number == 1){
    //we can just use the clausified parent directly
    out << indent << "have " << stepIdent << concl->number() << " : ";
    outputUnit(out, concl);
    out << " := by\n" << 
      indent << indent << "duper [*]\n";
    return;
  }
  //SortMap parentMap;

  out << indent << "have " << stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by\n";
  out << indent << indent << "duper [*]\n";
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
  out << indent << "let " << PredicateName(pred);
  VSList* fDomain;
  if(concl->getFormula()->connective()==Kernel::FORALL){
    fDomain = concl->getFormula()->vars();
    auto fDomainIter = VSList::RefIterator(fDomain->iter());
    out << " ";
    outputVariablesGen<VSList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 0, true);
  }

  out << " := ";
  outputFormula(out, formula, &conclSorts);
  out << "\n" << indent << "have "<< stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by\n";
  if(concl->getFormula()->connective()==Kernel::FORALL){
    out << indent << indent << "intros ";
    auto fDomainIter = VSList::RefIterator(fDomain->iter());
    //This outputs the variable sorted, which relies on the rectification to be sorted
    outputVariablesGen<VSList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 1, false);
    out << "\n";
  }
  out << indent << indent << "have s : ";
  outputFormula(out, formula);
  out << " ↔ " << PredicateName(pred) << " ";
  if(concl->getFormula()->connective()==Kernel::FORALL){
    auto fDomainIter = VSList::RefIterator(fDomain->iter());
    outputVariablesGen<VSList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 0, false);
  }
  out << " := Iff.rfl\n" << indent << indent;
  out << "(first | exact s | exact or_comm.mp (imp_iff_not_or.mp s.mpr) | have res := (or_comm.mp (imp_iff_not_or.mp s.mpr)); simp only[or_assoc] at res; trivial | exact imp_iff_not_or.mp s.mp)\n";
}

void LeanChecker::functionDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl){
  //auto [parent] = getParents<1>(concl);
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  auto introducedFunctionSymbols = _is->getIntroducedSymbols(concl);
  auto fun = env.signature->getFunction(introducedFunctionSymbols.top().second);
  out << indent << "let " << FunctionName(fun) << " ";
  auto lit = concl->asClause()->literals()[0];
  SortMap variableMap;
  SortHelper::collectVariableSorts(lit, variableMap);
  ASS(fun->arity() == variableMap.size());
  auto domain = variableMap.domain();
  outputVariables(out, domain, conclSorts, conclSorts);
  out << ":= ";
  ASS(lit->isEquality())
  auto lhsEqDefinition = lit->termArg(0);
  out << Args{&lhsEqDefinition, conclSorts, conclSorts} << "\n";
  out << indent << "have " << stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := ";
  if(fun->arity()>0){
    out << "fun ";
    auto domain = variableMap.domain();
    outputVariables(out, domain, conclSorts, conclSorts);
    out << " => ";
  }
  out << "rfl\n";
}

void LeanChecker::avatarDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl){
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  ASS(!concl->isClause())
  ASS(concl->getFormula()->connective()==Kernel::IFF);
  out << indent << "let ";
  outputFormula(out, concl->getFormula()->left());
  out << " := ";
  outputFormula(out, concl->getFormula()->right());
  out << "\n" << indent << "have " << stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := Iff.rfl\n";
}

void LeanChecker::avatarComponent(std::ostream &out, SortMap &conclSorts, Unit *concl){
  outputPremiseAndConclusion(out, concl);
  auto lit = Saturation::Splitter::getLiteralFromName(concl->asClause()->splits()->sval());
  out << " := by\n" << indent << "intro h component ";
  auto varDomain = conclSorts.domain();
  outputVariables(out, varDomain, conclSorts, conclSorts);
  out << "\n" << indent << "have new := ";
  if(lit.positive()){
    out << "h.mp component ";
  } else {
    out << "not_imp_not.mpr h.mpr component";
  }
  varDomain = conclSorts.domain();
  outputVariables(out, varDomain, conclSorts, conclSorts);
  out << "\n" << indent << "(first | trivial | ac_nf at new ⊢ | grind [cases Or])\n\n";
}

void LeanChecker::outputSatClause(std::ostream &out, std::map<unsigned int, bool> &seen, std::string primed, bool boolSymbols)
{
  out << "(";
  for (auto iter = seen.begin(); iter != seen.end(); ++iter) {
    auto [var, positive] = *iter;
    if (boolSymbols) {
      out << (positive ? "" : "!")
          << "sA" << var << primed;
    }
    else {
      out << (positive ? "" : "(¬")
          << "sA" << var << primed
          << (positive ? "" : ")");
    }
    if (std::next(iter) != seen.end()) {
      if (boolSymbols) {
        out << " || ";
      }
      else {
        out << " ∨ ";
      }
    }
  }
  out << ")";
}

void LeanChecker::outputSatFormula(std::ostream &out, std::set<Unit *, CompareUnits> &parents, std::string primed, bool boolSymbols, bool useImplication)
{
  
  for(auto unitIter = parents.begin(); unitIter != parents.end(); ++unitIter){
    Unit *u = *unitIter;
    auto extras = env.proofExtra.get<Indexing::SATClauseExtra>(u).clause;
    std::map<unsigned, bool, std::less<unsigned>> seen;
    for(auto l : iterTraits(extras->iter())){
      seen.insert(std::make_pair(l.var(), l.positive()));
    }
    outputSatClause(out, seen, primed, boolSymbols);
    if (std::next(unitIter) != parents.end()) {
      if(useImplication){
        out << " → ";
      } else {
        if(boolSymbols){
          out << " && ";
        } else {
          out << " ∧ ";
        }
      }
    }
  }
}

void LeanChecker::avatarRefutation(std::ostream &out, SortMap &conclSorts, Unit *concl)
{

  std::set<Unit *, CompareUnits> sortedParents;
  for(Unit *u : iterTraits(concl->getParents())){
    sortedParents.insert(u);
  }
 

  //out << "set_option maxHeartbeats 0 in\n-- this is probably due to a suboptimal encoding\n";
  //Convert the SAT bool refuation proof to prop
  out << " : ";
  outputSatFormula(out, sortedParents, "", false, true);
  out << " → ";
  outputUnit(out, concl);
  out << " := by\n" 
      << indent << "duper [*]\n";
}

void LeanChecker::avatarRefutationProofStep(std::ostream &out, SortMap &conclSorts, Unit *concl){
  std::set<Unit *, CompareUnits> sortedParents;
  for(Unit *u : iterTraits(concl->getParents())){
    sortedParents.insert(u);
  }
  out << indent << "have " << stepIdent << concl->number() << " := inf_s" << concl->number() << " ";
  //out << "and_constr ⟨";
  for (auto parents = sortedParents.begin(); parents != sortedParents.end(); ++parents) {
    Unit *parent = *parents;
    out << stepIdent << parent->number() ;
    if(std::next(parents) != sortedParents.end()){
      out << " ";
    }
  }
  out << "\n"; 
}

void LeanChecker::avatarSplitClause(std::ostream &out, SortMap &conclSorts, Unit *concl){
  UnitIterator parents = concl->getParents();
  ALWAYS(parents.hasNext())
  Clause *parent = parents.next()->asClause();
  SortMap mainParentMap;
  SortHelper::collectVariableSorts(parent, mainParentMap);
  
  std::set<unsigned> previousSplits;
  if(!parent->noSplits()){
    for(unsigned split : iterTraits(parent->splits()->iter())){
      auto s = Splitter::getLiteralFromName(split);
      previousSplits.insert(s.var());
    }
  }

  outputPremises(out, concl);
  std::map<unsigned, bool> currentSplits;
  for(SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(concl).clause->iter())
    currentSplits.insert(std::make_pair(l.var(), l.positive()));
  
  out << " → \n"<<indent;
  outputSatClause(out, currentSplits, "", false);

  unsigned parentNo = 0;
  out << " := by\n" << indent << "duper [*]";

}


void LeanChecker::definitionFoldingTwee(std::ostream &out, SortMap &conclSorts, Clause *concl){
  genericNPremiseInferenceNoSubs(out, conclSorts, concl);
}

void LeanChecker::definitionFoldingPred(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto parents = concl->getParents();
  auto firstParent = parents.next();
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  out << indent << "have " << stepIdent << concl->number() << " := " << stepIdent << firstParent->number() << "\n";
  out << indent << "duper [*]\n";
}

void LeanChecker::definitionUnfolding(std::ostream &out, SortMap &conclSorts, Unit *concl){
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
  auto proofExtra = env.proofExtra.get<FunctionDefinitionExtra>(concl);
  instantiateConclusionVars(out, conclSorts, concl);
  ASS(parents.hasNext())
  auto parent = parents.next();
  ASS(parent->isClause())
  out << "\n" << indent << "have " << intIdent << 0 << " := h"<<0<<" ";
  instantiatePremiseVars(out, conclSorts, parent->asClause());

  out << "\n";
  parents = concl->getParents();
  for (unsigned i = 0; i < size; i++) {
    auto parent = parents.next();
    if(i==0){
      continue;
    }
    
    auto rw = parent->asClause();
    ASS(rw->size()==1);
    auto lit = rw->literals()[0];
    ASS(lit->isEquality());
    auto recordedLhs = proofExtra.lhs;
    if(lit->termArg(0).term() == recordedLhs[i-1]){
      out << indent << "nth_rewrite 1 [h" << i << "] at i0\n";
    } else {
      out << indent << "nth_rewrite 1 [ ← h" << i << "] at i0\n";
    }
  }
  out << indent << "grind only\n";
}
void LeanChecker::normalForm(std::ostream &out, SortMap &conclSorts, Unit *concl){
  outputPremiseAndConclusion(out, concl);
  out << " := by\n";
  auto rule = concl->inference().rule();
  if (rule == InferenceRule::ENNF) {
    out << indent << "intros h\n"
        << indent << "ennf_transformation at h<;>\n"
        << indent << "exact h\n";
  }
  else if (rule == InferenceRule::FLATTEN) {
    out << indent << "intro h\n"
        << indent << "flattening at h<;>\n"
        << indent << "first | exact h | grind \n";
  }
  else if (rule == InferenceRule::NNF) {
    out << indent << "intro h\n"
        << indent << "nnf_transformation at h<;>\n"
        << indent << "first | exact h | grind \n";
  }
  else if (rule == Kernel::InferenceRule::RECTIFY) {
    out << indent << "first | exact fun x => x\n";
  }
  else if (rule == Kernel::InferenceRule::REDUCE_FALSE_TRUE) {
    out << indent << "intro h\n";
    out << indent << "remove_tauto at h<;>\n";
    out << indent << "first | exact h | grind \n";
  } /*else if (rule == InferenceRule::THEORY_NORMALIZATION) {
    out << indent << "intro h\n";
    out << indent << "try simp only [← not_lt, gt_iff_lt] at h\n";
    out << indent << "first | exact h | grind | sorry\n";
  }*/
  out << "\n";
}

void LeanChecker::skolemize(std::ostream &out, SortMap &conclSorts, Unit *concl){
  UnitIterator parents = concl->getParents();
  // The first parent is the original formula
  Unit *parent = parents.next();

  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";

  ASS(_is->hasIntroducedSymbols(concl))
  std::map<unsigned,Signature::Symbol*> replacedVarMap;
  for(auto [_, symNum] : iterTraits(_is->getIntroducedSymbols(concl).iter())){
    long replacedVar = _is->variableReplacedByIntroducedSymbol(symNum);
    ASS(replacedVar != -1)
    replacedVarMap[replacedVar] = env.signature->getFunction(symNum);
  }
  VariablePrenexOrderingTree tree;
  tree.buildTreeFromFormula(parent->getFormula(), Kernel::EXISTS);
  out << indent << "exists_prenex at "<< stepIdent;
  out << parent->number() << "\n";
  out << indent << "let ⟨";
  for (unsigned var : *tree.determineVariableOrdering()) {
    out << FunctionName(replacedVarMap[var]) << ",";
  }
  out << "step" << concl->number() << "'⟩ := step" << parent->number() << "\n";
  out << indent << "have step" << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by symm_match using " << stepIdent << concl->number() << "'\n";
}

void LeanChecker::rectify(std::ostream &out, SortMap &conclSorts, Unit *concl, const InferenceRecorder::RectifyInferenceExtra* rectifyInfo)
{
  outputPremiseAndConclusion(out, concl);
  out << " := by\n";
  out << indent << "intro h\n";
  out << indent << "try simp only [forall_const, exists_const, -iff_self, -eq_self] at h\n";
  unsigned counter = 0;
  for(auto [newFormula, formulaAndSubst] : rectifyInfo->renamings) {
    auto [formula, subst] = formulaAndSubst;
    //check if subst is identity, if so we can skip this formula
    bool identity = true;
    for(auto [var, term] : iterTraits(subst.items())){
      if(term != TermList::var(var)){
        identity = false;
        break;
      }
    }
    if(identity){
      continue;
    }
    SortMap allFormulaSorts;
    SortHelper::collectVariableSorts(formula, allFormulaSorts);
    SortMap allNewFormulaSorts;
    SortHelper::collectVariableSorts(newFormula, allNewFormulaSorts);
    SortMap sorts;
    SortMap newFormulaSorts;
    auto conn = formula->connective();
    if(conn==Kernel::FORALL || conn==Kernel::EXISTS){
      for(auto var : iterTraits(formula->vars()->iter())){
        sorts.insert(var.first, allFormulaSorts.get(var.first));
      }
      for(auto var : iterTraits(newFormula->vars()->iter())){
        newFormulaSorts.insert(var.first, allNewFormulaSorts.get(var.first));
      }
    }
    out << indent << "have r" << counter << " (P :";
    //Todo sort sorts here
    for(auto [var, sort] : iterTraits(sorts.items())){
      out << Sort{sort} << "→";
    }
    out << "Prop) : ";
    out << "( " << (conn == Kernel::FORALL ? "∀" : "∃") << " ";
    auto domain = sorts.domain();
    outputVariables(out, domain, sorts, sorts);
    out << ", P ";
    domain = sorts.domain();
    outputVariables(out, domain, sorts, sorts);
    out << ") ↔ (" << (conn == Kernel::FORALL ? "∀" : "∃") << " ";
    domain = sorts.domain();
    outputVariables(out, domain, sorts, sorts, DoSubst(subst));
    out << ", P ";
    domain = sorts.domain();
    outputVariables(out, domain, sorts, sorts);
    out << ") := \n"
        << indent << indent << "Iff.intro (fun f ";
    if(conn == FORALL){
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts,DoSubst(subst));
      out << " => f ";
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts);
      out << ") (fun f ";
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts);
      out << " => f ";
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts,DoSubst(subst));
      out << ")\n";
    } else if (conn == EXISTS) {
      domain = sorts.domain();
      out << " => " << "let ⟨";
      outputVariables(out, domain, sorts, sorts, Identity{}, true, false, ", ");
      out << ", hP⟩ := f\n";
      out << indent << indent << indent << "Exists.intro ";
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts, DoSubst(subst), true, false, " (Exists.intro ");
      out << " hP";
      out << std::string(sorts.size(), ')') << "\n"
          << indent << indent << indent << "(fun f ";
      domain = sorts.domain();
      out << " => " << "let ⟨";
      outputVariables(out, domain, sorts, sorts, DoSubst(subst), true, false, ", ");
      out << ", hP⟩ := f\n";
      out << indent << indent << indent << "Exists.intro ";
      domain = sorts.domain();
      outputVariables(out, domain, sorts, sorts, Identity{}, true, false, " (Exists.intro ");
      out << " hP";
      out << std::string(sorts.size(), ')') << "\n";
    }
    out << indent << "conv in ";
    SortMap newFormulaAllSorts;
    SortHelper::collectVariableSorts(newFormula, newFormulaAllSorts);
    printFormula(out, newFormula, newFormulaSorts, newFormulaAllSorts, true);
    out << " =>\n"
        << indent << indent << "rw [r" << counter << "]\n";
    counter++;
  }
  out << indent << "symm_match using h\n\n";
}

void LeanChecker::axiom(std::ostream &out, SortMap &conclSorts, Unit *concl)
{
}


void LeanChecker::outputCumulativeSplits(std::initializer_list<Kernel::Clause *> cl, std::string seperator, std::string splitPrefix, bool ignoreNegation)
{
  std::set<unsigned> splits;
  for (Kernel::Clause *c : cl) {
    if (c->noSplits()) {
      continue;
    }
    SplitSet &clSplits = *c->splits();
    for (int i = 0; i < clSplits.size(); i++) {
      if (ignoreNegation) {
        auto satLiteral = Saturation::Splitter::getLiteralFromName(clSplits[i]);
        splits.insert(satLiteral.var());
      } else {
        splits.insert(clSplits[i]);
      }
    }
  }

  for (unsigned split : splits) {
    if(ignoreNegation){
      out << splitPrefix << split;
    } else {
      out << Split<false>(split);
    }
    if (split != *splits.rbegin()) {
      out << seperator;
    }
  }
}

void LeanChecker::outputCumulativeSplits(std::set<Kernel::Unit*, CompareUnits> cl, std::string seperator, std::string splitPrefix ,std::string prefix, std::string suffix)
{
  std::set<unsigned> splits;
  for (Kernel::Unit *c : cl) {
    if(c->inference().rule() == InferenceRule::AVATAR_SPLIT_CLAUSE){
      for(SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(c).clause->iter())
        splits.insert(l.var());
      continue;
    }
    if(!c->isClause()){
      continue;
    }
    if (c->asClause()->noSplits()) {
      continue;
    }
    SplitSet &clSplits = *c->asClause()->splits();
    for (int i = 0; i < clSplits.size(); i++) {
      auto spl = clSplits[i];
      auto satLiteral = Saturation::Splitter::getLiteralFromName(spl);
      
      splits.insert(satLiteral.var());
    }
  }
  if (splits.empty()) {
    return;
  }
  out << prefix;
  for (unsigned split : splits) {
    out << "sA" << split;
    if (split != *splits.rbegin()) {
      out << seperator;
    }
  }
  out << suffix;
}

void LeanChecker::outputUnit(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts, bool outputSplits)
{
  if (u->isClause()) {
    auto cl = u->asClause();
    if (outputSplits && !cl->noSplits()) {
      out << "("; // closed after printing the whole clause
      outputCumulativeSplits({cl}, "→");
      out << "→";
    }
    outputClause(out, cl, conclSorts, Identity{});
    if(outputSplits && !cl->noSplits()){
      out << ")";
    }
  }
  else {
    outputFormula(out, u->getFormula(), conclSorts, Identity{});
  }
}

void LeanChecker::outputUnitBeginning(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts)
{
  for(auto parent : iterTraits(u->getParents())){
    if (this->alreadyPrintedFormulas.find(parent->number()) == this->alreadyPrintedFormulas.end()) {
      out << "def φ" << parent->number() << " :=";
      outputUnit(out, parent);
      out << "\n";
    }
    alreadyPrintedFormulas.insert(parent->number());
  }
}
} // namespace Shell
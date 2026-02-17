#include "LeanChecker.hpp"
#include "Forwards.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/EqHelper.hpp"
#include "LeanPrinter.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/FunctionDefinition.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include "VariablePrenexOrderingTree.hpp"
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
    case InferenceRule::DISTINCTNESS_AXIOM:
    //definitions are handled later
    case InferenceRule::AVATAR_DEFINITION:
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
    case InferenceRule::SUPERPOSITION:
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
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
  outputPreamble(out);
  outputCumulativeSplits(proof, " ", "sA" ,"variable {", " : Prop}\n");
  //outputCumulativeSplits(proof, "]\n[Decidable ", "sA" ,"[Decidable ", "]\n");
  
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
  //out << "[DecidableEq " << SortName(sig.getDefaultSort())<< " ]\n";
  //
  for (unsigned i = Signature::FIRST_USER_CON; i < sig.typeCons(); i++) {
    out << "variable {" << SortName(i) << " : Type u}\n";
    out << "variable [inst : Inhabited " << SortName(i) << " ]\n";
    //out << "[DecidableEq " << SortName(i)<< " ]\n";
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
      out << (arity == 0 ? "" : " → ") << Sort{range};
    }
    out << ")}\n";
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
  if(inferenceNeedsReplayInformation(u->inference().rule())){
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
    if(rule == InferenceRule::AVATAR_REFUTATION){
      out << "set_option maxHeartbeats 200000000 in\n-- this is probably due to a suboptimal encoding\n";
    }
    out << "theorem inf_s" << u->number();
    /*std::set<Kernel::Unit*, CompareUnits> clauses;
    auto parents = u->getParents();
    while(parents.hasNext()){
      auto parent = parents.next();
      if(parent->isClause()){
        clauses.insert(parent);
      }
    }
    if(u->isClause()){
      clauses.insert(u);
    }
    outputCumulativeSplits(clauses, " ", "sA","{", ": Prop} ");*/
    if(u->inference().rule()!=InferenceRule::AVATAR_REFUTATION
       && u->inference().rule()!=InferenceRule::AVATAR_REFUTATION_SMT){
      out << " : ";
    }
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
    case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    case InferenceRule::REORIENT_EQUATIONS:
    case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    case InferenceRule::REORDER_LITERALS:
      genericNPremiseInferenceNoSubs(out, conclSorts, u);
      break;
    case InferenceRule::EQUALITY_RESOLUTION:
    case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
      equalityResolution(out, conclSorts, u->asClause(), info);
      break;
    case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
      subsumptionResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::DEFINITION_UNFOLDING:
      definitionUnfolding(out, conclSorts, u);
      break;
    case InferenceRule::DEFINITION_FOLDING_TWEE:
      definitionFoldingTwee(out, conclSorts, u->asClause());
      break;
    case InferenceRule::EVALUATION:
      genericNPremiseInferenceNoSubs(out, conclSorts, u->asClause(), 
      "norm_num1\n" + 
      indent +"norm_num1 at "  + intIdent + "0\n" + 
      indent + "try simp only [our_int_not_lt] at i0\n"+
      indent + "(first | exact i0 | try grind)\n\n");
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
    case InferenceRule::AVATAR_COMPONENT:
      avatarComponent(out, conclSorts, u);
      break;
    case InferenceRule::AVATAR_REFUTATION:
    case Kernel::InferenceRule::AVATAR_REFUTATION_SMT:
      avatarRefutation(out, conclSorts, u);
      break;
    case Kernel::InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
      genericInference(out, conclSorts, u, "intro h\n" +
        indent + "have h' := Not.intro h\n" +
        indent + "try simp only [and_iff_not_or_not, not_not] at h'\n" +
        indent + "exact h'\n");
      break;
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
      avatarSplitClause(out, conclSorts, u);
      break;
    default:
      genericInference(out, conclSorts, u);
  }
}

unsigned LeanChecker::outputPremises(std::ostream &out, Unit *u, std::string seperator){
  UnitIterator parents = u->getParents();
  unsigned count = 0;
  while (parents.hasNext()) {
    Unit *parent = parents.next();
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
      if(cl->splits()->size() == 1){
        outputCumulativeSplits({cl}, " ", "x", true);
        out << " ";
      } else {
        out << "splits ";
      }
    }
  }
  VirtualIterator<unsigned> domain = conclSorts.domain();
  outputVariables(out, domain, conclSorts, conclSorts);
  if(concl->isClause()) {
    auto cl = concl->asClause();
    if(!cl->noSplits() && cl->splits()->size() > 1){
      out << "\n" << indent << "rcases splits with ⟨";
      outputCumulativeSplits({cl}, ",", "x", true);
      out << "⟩";
    }
  }
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
  //if(concl->isClause()){
  //  genericNPremiseInferenceNoSubs(out,conclSorts,concl->asClause(), tactic);
  //  return;
  //}
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

  genericNPremiseInference(out, conclSorts, concl, {Substitution(), subst}, "grind only [cases Or]");
}

void LeanChecker::factoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

void LeanChecker::equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info)
{
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0]}, "grind only [cases Or]");
}

void LeanChecker::superposition(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation *info){
  genericNPremiseInference(out, conclSorts, concl, {info->substitutionForBanksSub[0], info->substitutionForBanksSub[1]}, "grind only [cases Or]");
}

// check whether `demodulator` l = r rewrites left-to-right in the context of C[t] -> C[s]
// TODO copied from Dedukti, merge at some point
static bool isL2RDemodulatorFor(Literal *demodulator, Clause *rewritten, TermList target, Clause *result)
{
  ASS(demodulator->isEquality())
  ASS(demodulator->isPositive())

  // TODO this is waaay overkill, but it's very hard to work out which way a demodulator was used
  // consult MH about how best to do this
  Substitution subst;
  if (!MatchingUtils::matchTerms(demodulator->termArg(0), target, subst))
    return false;
  TermList rhsSubst = SubstHelper::apply(demodulator->termArg(1), subst);

  for (Literal *l : rewritten->iterLits())
    if (!result->contains(l) && !result->contains(EqHelper::replace(l, target, rhsSubst)))
      return false;

  return true;
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
      auto args = f->args()->iter();
      unsigned thisCount=0;
      while (args.hasNext()) {
        thisCount += 1+countConnectives(args.next());
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

void LeanChecker::clausify(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto [parent] = getParents<1>(concl);
  
  SortMap parentMap;
  SortHelper::collectVariableSorts(parent, parentMap);
  outputPremiseAndConclusion(out, concl);
  out << " := by\n" << indent << "intros h ";
  if(countConnectives(parent->getFormula()) < 500){
    instantiateConclusionVars(out, conclSorts, concl);
    out << "\n" << indent << "prenexify at h \n" << indent << "have h1 := h ";
    VariablePrenexOrderingTree tree; 
    tree.buildTreeFromFormula(parent->getFormula(), Kernel::FORALL);
    auto ordering = tree.determineVariableOrdering();
    outputVariables(out, ordering, conclSorts, parentMap, Identity{}, 0);
    out << "\n" << indent << "grind only [cases Or]\n\n";
  } else {
    out << "\n" << indent << "duper [h]\n\n";
  } 
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
  //ASS(concl->getFormula()->connective()==Kernel::FORALL);
  out << indent << "let " << PredicateName(pred);
  VList* fDomain;
  if(concl->getFormula()->connective()==Kernel::FORALL){
    fDomain = concl->getFormula()->vars();
    auto fDomainIter = fDomain->iter();
    out << " ";
    outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 0, true);
  }

  out << " := ";
  outputFormula(out, formula, &conclSorts);
  out << "\n" << indent << "have "<< stepIdent << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by\n";
  if(concl->getFormula()->connective()==Kernel::FORALL){
    out << indent << indent << "intros ";
    auto fDomainIter = fDomain->iter();
    //This outputs the variable sorted, which relies on the rectification to be sorted
    outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 1, false);
    out << "\n";
  }
  out << indent << indent << "have s : ";
  outputFormula(out, formula);
  out << " ↔ " << PredicateName(pred) << " ";
  if(concl->getFormula()->connective()==Kernel::FORALL){
    auto fDomainIter = fDomain ->iter();
    outputVariablesGen<VList::RefIterator>(out, fDomainIter, conclSorts, conclSorts, Identity{}, 0, false);
  }
  out << " := Iff.rfl\n" << indent << indent;
  out << "(first | exact s | exact or_comm.mp (imp_iff_not_or.mp s.mpr) | have res := (or_comm.mp (imp_iff_not_or.mp s.mpr)); simp only[or_assoc] at res; trivial | exact imp_iff_not_or.mp s.mp)\n\n";
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
  //auto [parent] = getParents<1>(concl);
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  //auto introducedFunctionSymbols = _is->getIntroducedSymbols(concl);
  //outputUnit(out, concl);
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
    out << "not_imp_not.mpr h.mpr ";
  }
  varDomain = conclSorts.domain();
  outputVariables(out, varDomain, conclSorts, conclSorts);
  out << "\n" << indent << "(first | trivial | grind [cases Or])\n\n";
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
    auto iter = extras->iter();
    std::map<unsigned, bool, std::less<unsigned>> seen;
    while(iter.hasNext()){
      SATLiteral l = iter.next();
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
  out << "' (";
  std::set<unsigned> seen;
  for(Unit *u : iterTraits(concl->getParents()))
    for(SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(u).clause->iter())
      seen.insert(l.var());
  
  std::set<Unit *, CompareUnits> sortedParents;
  for(Unit *u : iterTraits(concl->getParents())){
    sortedParents.insert(u);
  }
  for(unsigned var : seen){
    out << "sA" << var << "' ";
  }
  out << ": Bool) : ";
  outputSatFormula(out, sortedParents, "'", true, true);
  out << " → ";
  outputUnit(out, concl);
  out << " := by\n" << indent << "intro h\n" <<
  indent << "bv_decide\n\n";


  out << "set_option maxHeartbeats 200000000 in\n-- this is probably due to a suboptimal encoding\n";
  //Convert the SAT bool refuation proof to prop
  out << "theorem inf_s" << concl->number() << " : ";
  outputSatFormula(out, sortedParents, "", false, true);
  out << " → ";
  outputUnit(out, concl);
  out << " := by\n" 
      << indent << "classical\n" 
      << indent << "intro h\n" 
      << indent << "have satProof := inf_s" << concl->number() << "' ";
  for(unsigned var : seen){
    out << "(decide sA" << var << ") ";
  }
  out << "\n" << indent << "simp (config := {maxSteps := 2000000}) only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,\n"
      << indent << indent << "Bool.not_true, decide_eq_false_iff_not, or_assoc, and_assoc] at satProof\n"
      << indent << "exact satProof h\n\n";

  //out << "\n" << indent << "simp only [decide_eq_true_iff, decide_eq_false_iff_not] at satProof\n" 
  //    << indent << "exact satProof h\n";
  out << "\n\n";  
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
    auto splits = parent->splits()->iter();
    while(splits.hasNext()){
      unsigned split = splits.next();
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

  std::unordered_map<unsigned, Clause *> components;
  std::vector<unsigned> parentsThatRewrite;
  std::map<unsigned, std::pair<unsigned,Clause*>> splitToParentMap;
  unsigned instanceCount = 1;
  while(parents.hasNext()) {
    Unit *parent = parents.next();
    auto dex = env.proofExtra.get<SplitDefinitionExtra>(parent);
    ASS(dex.component->isComponent())
    unsigned component = dex.component->splits()->sval();
    components.insert({component, dex.component});
    if(previousSplits.find(Splitter::getLiteralFromName(component).var()) == previousSplits.end()){
      splitToParentMap.insert({Splitter::getLiteralFromName(component).var(), {instanceCount,dex.component}});
      parentsThatRewrite.push_back(instanceCount);
    }
    instanceCount++;
  }
  

  auto parentsIter = concl->getParents();
  unsigned parentNo = 0;
  out << " := by\n" << indent << "intros ";
  while(parentsIter.hasNext()){
    parentsIter.next();
    out << "h" << parentNo << " ";
    parentNo++;
  }
  out << "\n";
  
  for(auto parentNo : parentsThatRewrite){
    out << indent << "try rw[h" << parentNo << "]\n";
  }
  out << indent << "try simp only [imp_iff_not_or] at h0\n"
      << indent << "prenexify\n"
      << indent << "prenexify at h0\n";


  // Copied from dedukti implementation, trying to reconstruct the components of the split, 
  // so that we can correctly instantiate the variables in the conclusion to match the variables
  // in the parent splits.
  Stack<LiteralStack> disjointLiterals;
  if(!Splitter::getComponents(parent, disjointLiterals)) {
    disjointLiterals.reset();
    LiteralStack component;
    for(Literal *l : parent->iterLits())
      component.push(l);
    disjointLiterals.push(std::move(component));
  }
  decltype(disjointLiterals)::Iterator classes(disjointLiterals);
  // map variables in the parent to corresponding variables in the child splits
  Substitution fullSubst;
  std::map<unsigned, unsigned> varToSplitMap;
  while(classes.hasNext()) {
    LiteralStack klass = classes.next();
    Substitution subst;
    for(auto [name, component] : components) {
      if(klass.size() == component->length()) {
        subst.reset();
        if(klass.size() == 1 && klass[0]->ground() && Literal::positiveLiteral(klass[0]) == Literal::positiveLiteral((*component)[0])) {
          SortMap map;
          SortHelper::collectVariableSorts(klass[0], map);
          auto varDomain = map.domain();
          while(varDomain.hasNext()){
            unsigned var = varDomain.next();
            varToSplitMap.insert({var, Splitter::getLiteralFromName(name).var()});
          }
          break;
        }
        if(Kernel::MLVariant::isVariant(klass.begin(), component, /*complementary=*/false, &subst)) {
          auto iter = subst.items();
          while(iter.hasNext()) {
            auto [var, term] = iter.next();
            fullSubst.bind(term.var(), TermList::var(var));
            varToSplitMap.insert({term.var(), Splitter::getLiteralFromName(name).var()});
          }
          break;
        }
      }
    }
  }

  //TODO make this include the variant substitution.
  out << indent << "intros ";
  for(auto iter = currentSplits.begin(); iter != currentSplits.end(); ++iter){
    auto parentWithNumbering = splitToParentMap.find(iter->first);
    if(parentWithNumbering != splitToParentMap.end()){
      auto [parNo, parent] = parentWithNumbering->second;
      SortMap map;
      SortHelper::collectVariableSorts(parent,map);
      auto parentVariables = map.domain();
      std::set <unsigned> sortedVars;
      while(parentVariables.hasNext()){
        unsigned var = parentVariables.next();
        sortedVars.insert(var);
      }
      out << " ";
      for(unsigned var : sortedVars){
        out << "x" << parentWithNumbering->first << "a" << var << " ";
      }
    }
  }
  out << "\n" << indent << "have newForm := h0 ";
  auto varDomain = mainParentMap.domain();
  std::set<unsigned> sortedVars;
  while(varDomain.hasNext()){
    unsigned var = varDomain.next();
    sortedVars.insert(var);
  }

  for(unsigned var : sortedVars){
    unsigned substVar = fullSubst.apply(var).var();
    out << "x" << varToSplitMap[var] << "a" << substVar << " ";

  }
  out << "\n" << indent << "grind only [cases Or]\n\n";
}


void LeanChecker::definitionFoldingTwee(std::ostream &out, SortMap &conclSorts, Clause *concl){
  genericNPremiseInferenceNoSubs(out, conclSorts, concl);
}

void LeanChecker::definitionFoldingPred(std::ostream &out, SortMap &conclSorts, Unit *concl){
  auto parents = concl->getParents();
  auto firstParent = parents.next();
  out << indent << "-- step" << concl->number() << " " << concl->inference().name() << "\n";
  out << indent << "have " << stepIdent << concl->number() << " := " << stepIdent << firstParent->number() << "\n";
  out << indent << "change ";
  outputUnit(out, concl);
  out << " at " << stepIdent << concl->number() << "\n";
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
        << indent << "ennf_transformation at h\n"
        << indent << "try simp only [not_true]\n"
        << indent << "exact h\n";
  }
  else if (rule == InferenceRule::FLATTEN) {
    out << indent << "intro h\n"
        << indent << "flattening at h\n"
        << indent << "try simp only [not_true]\n"
        << indent << "first | exact h | grind | duper[h]\n";
  }
  else if (rule == InferenceRule::NNF) {
    out << indent << "intro h\n"
        << indent << "nnf_transformation at h\n"
        << indent << "try simp only [not_true]\n"
        << indent << "first | exact h | grind | duper[h]\n";
  }
  else if (rule == Kernel::InferenceRule::RECTIFY) {
    out << indent << "first | exact fun x => x | duper [*]\n";
  }
  else if (rule == Kernel::InferenceRule::REDUCE_FALSE_TRUE) {
    out << indent << "intro h\n";
    out << indent << "remove_tauto at h\n";
    out << indent << "first | exact h | grind | duper[*]\n";
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
  out << indent << "let ⟨";
  for (unsigned var : *tree.determineVariableOrdering()) {
    out << FunctionName(replacedVarMap[var]) << ",";
  }
  out << "step" << concl->number() << "'⟩ := step" << parent->number() << "\n";
  out << indent << "have step" << concl->number() << " : ";
  outputUnit(out, concl);
  out << " := by symm_match using " << stepIdent << concl->number() << "'\n";
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
      out << "(";
      outputCumulativeSplits({cl}, "∧");
      out << ")→";
    }
    outputClause(out, cl, conclSorts, Identity{});
    if (outputSplits && !cl->noSplits()) {
      out << ")"; // close the one opened before
    }
  }
  else {
    outputFormula(out, u->getFormula(), conclSorts, Identity{});
  }
}

void LeanChecker::outputUnitBeginning(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts)
{
  auto parents = u->getParents();
  while (parents.hasNext()) {
    auto parent = parents.next();
    if (this->alreadyPrintedFormulas.find(parent->number()) == this->alreadyPrintedFormulas.end()) {
      out << "def φ" << parent->number() << " :=";
      outputUnit(out, parent);
      out << "\n";
    }
    alreadyPrintedFormulas.insert(parent->number());
  }
  // if(this->alreadyPrintedFormulas.find(u->number()) == this->alreadyPrintedFormulas.end()){
  //   out << "def φ" << u->number() << " :=";
  //   outputUnit(out, u);
  //   out << "\n";
  //   alreadyPrintedFormulas.insert(u->number());
  // }
}
} // namespace Shell
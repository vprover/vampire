#include "InferenceRecorder.hpp"

#include "Debug/Assertion.hpp"
#include "Indexing/DemodulationIndex.hpp"

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "SAT/SATLiteral.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/ClausificationRecording.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceReplay.hpp"
#include <algorithm>
#include <cstddef>
#include <map>
#include <set>
#include <sstream>
#include <utility>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Indexing;
namespace Shell {

InferenceRecorder *InferenceRecorder::_inst = nullptr;

InferenceRecorder *InferenceRecorder::instance()
{
  if (_inst != nullptr) {
    return _inst;
  }
  _inst = new InferenceRecorder();
  return _inst;
}

Substitution InferenceRecorder::conclusionRenaming(const std::unordered_map<unsigned, unsigned>& varMap)
{
  Substitution renaming;
  for (auto [source, target] : varMap) { renaming.bind(source, TermList::var(target)); }
  if (varMap.empty()) {
    // The identity fast path produces no explicit map. Reserve the surviving
    // variable names before freshening variables present only in the parents.
    auto variables = _currentGoal->getVariableIterator();
    while (variables.hasNext()) {
      unsigned variable = variables.next();
      renaming.bind(variable, TermList::var(variable));
    }
  }
  return renaming;
}

TermList InferenceRecorder::renameCertificateTerm(TermList term, Substitution& renaming,
                                                 unsigned& freshVariable)
{
  VariableIterator variables(term);
  while (variables.hasNext()) {
    unsigned variable = variables.next().var();
    TermList target;
    if (!renaming.findBinding(variable, target)) {
      // Eliminated variables must not alias a renamed conclusion variable,
      // which may even have a different sort. Share fresh names across banks.
      renaming.bind(variable, TermList::var(freshVariable++));
    }
  }
  return SubstHelper::apply(term, renaming);
}

void InferenceRecorder::recordRewrite(InferenceInformation::LiteralPosition equality,
    TermList from, unsigned fromBank, TermList to, unsigned toBank)
{
  ASS(_hasLastInference);
  auto& info = *_inferences.at(_lastInferenceId);
  info.hasRewrite = true;
  info.rewriteEquality = equality;
  info.rewriteFrom = SubstHelper::apply(from, info.substitutionForBanksSub.at(fromBank));
  info.rewriteTo = SubstHelper::apply(to, info.substitutionForBanksSub.at(toBank));
}

void InferenceRecorder::startRectifyRecording()
{
  _currentRectifyInference = std::make_unique<RectifyInferenceInformation>();
}

void InferenceRecorder::recordRectification(VSList* sourceBinders, VSList* targetBinders,
                                            const Substitution& rawRenaming,
                                            const std::set<unsigned>& removed)
{
  if (!_currentRectifyInference) { return; }
  RectifyInferenceInformation::Scope scope;
  scope.removed = removed;
  std::vector<unsigned> liveSource;
  VSList::Iterator source(sourceBinders);
  while (source.hasNext()) {
    unsigned variable = source.next().first;
    scope.sourceBinders.push_back(variable);
    if (!removed.contains(variable)) { liveSource.push_back(variable); }
  }
  VSList::Iterator target(targetBinders);
  while (target.hasNext()) { scope.targetBinders.push_back(target.next().first); }

  // As in leancheck's InferenceRecorder::rectify, compose the raw fresh-name
  // map with the binder order used by Lean's printer. This recovers occurrence
  // permutations inside terms; raw alpha-renaming alone is insufficient.
  std::sort(liveSource.begin(), liveSource.end());
  auto sortedTarget = scope.targetBinders;
  std::sort(sortedTarget.begin(), sortedTarget.end());
  ASS_EQ(liveSource.size(), sortedTarget.size());
  Substitution canonicalTarget;
  for (unsigned i = 0; i < liveSource.size(); ++i) {
    canonicalTarget.bind(sortedTarget[i], TermList::var(liveSource[i]));
  }
  for (unsigned variable : scope.sourceBinders) {
    TermList rectified = rawRenaming.apply(variable);
    ASS(rectified.isVar());
    scope.renaming.bind(variable, canonicalTarget.apply(rectified.var()));
  }
  _currentRectifyInference->scopes.push_back(std::move(scope));
}


void InferenceRecorder::endRectifyRecording(unsigned id)
{
  if (_currentRectifyInference) {
    _rectifyInferences[id] = std::move(_currentRectifyInference);
  }
}

const InferenceRecorder::RectifyInferenceInformation*
InferenceRecorder::getRectificationReplayInformation(unsigned id) const
{
  auto entry = _rectifyInferences.find(id);
  return entry == _rectifyInferences.end() ? nullptr : entry->second.get();
}

void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *>& premises,
                                              const RobSubstitution &recordedSubst)
{

  return populateSubstitutionsGen<RobSubstitution>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      [](const RobSubstitution &subst, const TermList &term, size_t bank) {
        return subst.apply(term, bank);
      });
}

void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *>& premises,
                                              const ResultSubstitutionSP &recordedSubst)
{

  return populateSubstitutionsGen<ResultSubstitutionSP>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      [](ResultSubstitutionSP subst, const TermList &term, size_t bank) {
        return subst->applyTo(term, bank);
      });
}

TermList applyFunc(const SubstApplicator &subst, const TermList &term, size_t bank)
{
  return SubstHelper::apply(term, subst);
}
void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *>& premises,
                                              const SubstApplicator &recordedSubst)
{
  return populateSubstitutionsGen<SubstApplicator>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      &applyFunc);
}

namespace {
unsigned literalPosition(Clause *clause, Literal *literal)
{
  for (unsigned i = 0; i < clause->length(); ++i) {
    if ((*clause)[i] == literal) {
      return i;
    }
  }
  ASS(false);
  return 0;
}
}

void InferenceRecorder::resolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst,
                                   Literal *queryLit, Literal *resultLit, unsigned constraintCount)
{
  ASS_EQ(premises.size(), 2);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst,
      InferenceInformation::LiteralPositionKind::RESOLVED,
      {{0, literalPosition(premises[0], queryLit)}, {1, literalPosition(premises[1], resultLit)}});
  const auto* info = getLastRecordedInferenceInformation();
  if (!info || info->conclusion != conclusion) { return; }
  auto& recorded = *_inferences.at(id);
  ASS_LE(constraintCount, recorded.naturalLiterals.size());
  recorded.constraints.assign(recorded.naturalLiterals.begin(),
                              recorded.naturalLiterals.begin() + constraintCount);
}

void InferenceRecorder::superposition(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst,
                                      bool eqIsResult, Literal *rewrittenLit,
                                      Literal* equality, TermList from, TermList to, unsigned constraintCount)
{
  ASS_EQ(premises.size(), 2);
  recordGenericSubstitutionInference<ResultSubstitutionSP>(id, conclusion, premises, recordedSubst,
                                                                     [eqIsResult](ResultSubstitutionSP subst, const TermList &term, size_t bank) {
                                                                       if (bank == 1) {
                                                                         return subst->apply(term, eqIsResult);
                                                                       }
                                                                       else {
                                                                         return subst->apply(term, !eqIsResult);
                                                                       }
                                                                     },
                                                                     InferenceInformation::LiteralPositionKind::REWRITTEN,
                                                                     {{0, literalPosition(premises[0], rewrittenLit)}});
  const auto* info = getLastRecordedInferenceInformation();
  if (!info || info->conclusion != conclusion) { return; }
  recordRewrite({1, literalPosition(premises[1], equality)}, from, 0, to, 1);
  auto& recorded = *_inferences.at(id);
  ASS_LE(constraintCount, recorded.naturalLiterals.size());
  recorded.constraints.assign(recorded.naturalLiterals.end() - constraintCount,
                              recorded.naturalLiterals.end());
}

void InferenceRecorder::populateNaturalLiterals(InferenceInformation& info,
    const std::unordered_map<unsigned, unsigned>& varMap)
{
  Substitution renaming;
  for (auto [var, target] : varMap) { renaming.bind(var, TermList::var(target)); }
  for (Literal* literal : info.conclusion->iterLits()) {
    info.naturalLiterals.push_back(SubstHelper::apply(literal, renaming));
  }
}

void InferenceRecorder::factoring(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst,
                                  Literal *removedLit)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst,
      InferenceInformation::LiteralPositionKind::REMOVED,
      {{0, literalPosition(premises[0], removedLit)}});
}

void InferenceRecorder::equalityFactoring(unsigned id, Clause *conclusion, const std::vector<Clause *> &premises,
                                          const RobSubstitution &recordedSubst)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

bool InferenceRecorder::condensation(Clause *conclusion, Clause *premise,
                                    const RobSubstitution &subst, unsigned removedIndex)
{
  recordGenericSubstitutionInference(conclusion->number(), conclusion, {premise}, subst,
      InferenceInformation::LiteralPositionKind::REMOVED, {{0, removedIndex}});
  const auto* info = getLastRecordedInferenceInformation();
  return info && info->conclusion == conclusion;
}

bool InferenceRecorder::condensation(Clause *conclusion, Clause *premise,
                                    const Substitution &subst, unsigned removedIndex)
{
  recordGenericSubstitutionInference<Substitution>(conclusion->number(), conclusion, {premise}, subst,
      [](const Substitution &substitution, const TermList &term, size_t) {
        return SubstHelper::apply(term, substitution);
      }, InferenceInformation::LiteralPositionKind::REMOVED, {{0, removedIndex}});
  const auto* info = getLastRecordedInferenceInformation();
  return info && info->conclusion == conclusion;
}

bool InferenceRecorder::recordReplayedInferenceCandidate(Clause* conclusion,
    const std::vector<Clause*>& premises, const RobSubstitution& subst,
    InferenceInformation::LiteralPositionKind kind,
    std::vector<InferenceInformation::LiteralPosition> positions,
    const std::vector<Literal*>& constraints)
{
  std::unordered_map<unsigned, unsigned> varMap;
  if (!isSameAsProofStep(conclusion, _currentGoal, varMap)) { return false; }
  auto info = std::make_unique<InferenceInformation>();
  info->conclusion = conclusion;
  info->premises = premises;
  populateSubstitutions(info->substitutionForBanksSub, varMap, premises, subst);
  info->literalPositionKind = kind;
  info->literalPositions = std::move(positions);
  Substitution renaming;
  for (auto [var, target] : varMap) { renaming.bind(var, TermList::var(target)); }
  for (Literal* literal : constraints) {
    info->constraints.push_back(SubstHelper::apply(literal, renaming));
  }
  populateNaturalLiterals(*info, varMap);
  _lastInferenceId = conclusion->number();
  _inferences[_lastInferenceId] = std::move(info);
  _hasLastInference = true;
  return true;
}

bool InferenceRecorder::recordReplayedInferenceCandidate(Clause* conclusion,
    const std::vector<Clause*>& premises, const std::vector<Substitution>& substitutions,
    InferenceInformation::LiteralPositionKind kind,
    std::vector<InferenceInformation::LiteralPosition> positions)
{
  return recordSubstitutionCandidate(conclusion, premises, substitutions, kind, std::move(positions));
}

bool InferenceRecorder::recordSubstitutionCandidate(Clause* conclusion,
    const std::vector<Clause*>& premises, const std::vector<Substitution>& substitutions,
    InferenceInformation::LiteralPositionKind kind,
    std::vector<InferenceInformation::LiteralPosition> positions,
    Substitution* renaming, unsigned* freshVariable)
{
  ASS_EQ(premises.size(), substitutions.size());
  std::unordered_map<unsigned, unsigned> varMap;
  if (!isSameAsProofStep(conclusion, _currentGoal, varMap)) { return false; }
  auto info = std::make_unique<InferenceInformation>();
  info->conclusion = conclusion;
  info->premises = premises;
  populateSubstitutionsGen<std::vector<Substitution>>(
      info->substitutionForBanksSub, varMap, premises, substitutions,
      [](const std::vector<Substitution>& banks, const TermList& term, size_t bank) {
        return SubstHelper::apply(term, banks[bank]);
      }, renaming, freshVariable);
  info->literalPositionKind = kind;
  info->literalPositions = std::move(positions);
  populateNaturalLiterals(*info, varMap);
  _lastInferenceId = conclusion->number();
  _inferences[_lastInferenceId] = std::move(info);
  _hasLastInference = true;
  return true;
}

void InferenceRecorder::instantiation(Clause* conclusion, Clause* parent,
                                    unsigned variable, TermList binding)
{
  if (!env.reconstruction) { return; }
  Substitution subst;
  subst.bind(variable, binding);
  recordReplayedInferenceCandidate(conclusion, {parent}, std::vector<Substitution>{subst},
      InferenceInformation::LiteralPositionKind::NONE, {});
}

namespace {
Substitution bankSubstitution(Clause* parent, const RobSubstitution& subst, int bank)
{
  Substitution result;
  auto variables = parent->getVariableIterator();
  while (variables.hasNext()) {
    unsigned variable = variables.next();
    result.bind(variable, subst.apply(TermList::var(variable), bank));
  }
  return result;
}
}

void InferenceRecorder::unifier(Clause* conclusion, Clause* parent,
                               const RobSubstitution& subst, int bank)
{
  if (!env.reconstruction) { return; }
  recordReplayedInferenceCandidate(conclusion, {parent},
      std::vector<Substitution>{bankSubstitution(parent, subst, bank)},
      InferenceInformation::LiteralPositionKind::NONE, {});
}

void InferenceRecorder::witness(InferenceInformation::WitnessKind kind, Clause* conclusion,
                               Clause* parent, Literal* literal, TermList term)
{
  if (!env.reconstruction) { return; }
  Substitution renaming;
  unsigned fresh;
  if (!recordSubstitutionCandidate(conclusion, {parent}, std::vector<Substitution>(1),
        InferenceInformation::LiteralPositionKind::NONE, {}, &renaming, &fresh)) { return; }
  auto [head, args] = HOL::getHeadAndArgs(renameCertificateTerm(term, renaming, fresh));
  ASS(head.isTerm());
  std::vector<TermList> dependencies(args.begin(), args.end());
  std::reverse(dependencies.begin(), dependencies.end());
  _inferences.at(_lastInferenceId)->witness = InferenceInformation::Witness{
      kind, literalPosition(parent, literal), head.term()->functor(), std::move(dependencies)};
}

void InferenceRecorder::booleanCase(Clause* conclusion, Clause* parent, Literal* literal,
                                   TermList term, bool value)
{
  if (!env.reconstruction) { return; }
  Substitution renaming;
  unsigned fresh;
  if (recordSubstitutionCandidate(conclusion, {parent}, std::vector<Substitution>(1),
        InferenceInformation::LiteralPositionKind::NONE, {}, &renaming, &fresh)) {
    _inferences.at(_lastInferenceId)->booleanCase = InferenceInformation::BooleanCase{
        literalPosition(parent, literal), renameCertificateTerm(term, renaming, fresh), value};
  }
}

void InferenceRecorder::quantifierInstance(Clause* conclusion, Clause* parent,
    const RobSubstitution& subst, int bank, Literal* literal, TermList term)
{
  if (!env.reconstruction) { return; }
  Substitution renaming;
  unsigned fresh;
  if (recordSubstitutionCandidate(conclusion, {parent},
        std::vector<Substitution>{bankSubstitution(parent, subst, bank)},
        InferenceInformation::LiteralPositionKind::NONE, {}, &renaming, &fresh)) {
    _inferences.at(_lastInferenceId)->quantifierInstance = InferenceInformation::QuantifierInstance{
        literalPosition(parent, literal), renameCertificateTerm(term, renaming, fresh)};
  }
}

void InferenceRecorder::choiceAxiom(Clause* axiom, TermList op,
                                  TermList predicate, TermList variable)
{
  if (!env.reconstruction || !op.isTerm()) { return; }
  Substitution renaming;
  unsigned fresh;
  if (recordSubstitutionCandidate(axiom, {}, {}, InferenceInformation::LiteralPositionKind::NONE,
        {}, &renaming, &fresh)) {
    _inferences.at(_lastInferenceId)->axiom = InferenceInformation::Axiom{
        InferenceInformation::AxiomKind::CHOICE, op.term()->functor(),
        {renameCertificateTerm(predicate, renaming, fresh), renameCertificateTerm(variable, renaming, fresh)}};
  }
}

void InferenceRecorder::extensionalityAxiom(Clause* axiom, TermList diff,
                                          TermList left, TermList right)
{
  if (!env.reconstruction || !diff.isTerm()) { return; }
  Substitution renaming;
  unsigned fresh;
  if (recordSubstitutionCandidate(axiom, {}, {}, InferenceInformation::LiteralPositionKind::NONE,
        {}, &renaming, &fresh)) {
    _inferences.at(_lastInferenceId)->axiom = InferenceInformation::Axiom{
        InferenceInformation::AxiomKind::EXTENSIONALITY, diff.term()->functor(),
        {renameCertificateTerm(left, renaming, fresh), renameCertificateTerm(right, renaming, fresh)}};
  }
}

TermList InferenceRecorder::replayWitness(Literal* literal, InferenceInformation::WitnessKind kind)
{
  if (!env.reconstruction || !_currentGoal || _replayWitness.isEmpty()) { return {}; }
  // Match the retained body of the transformed literal to recover the inverse
  // variable renaming. This also handles a Skolem-index witness whose
  // dependencies are terms or a proper subset of the parent's variables.
  for (Literal* target : _currentGoal->iterLits()) {
    if (!target->isEquality() || target->polarity() != literal->polarity()) { continue; }
    for (bool reversed : {false, true}) {
      TermList left = target->termArg(reversed ? 1 : 0);
      TermList right = target->termArg(reversed ? 0 : 1);
      Substitution forward;
      bool matched = false;
      if (kind == InferenceInformation::WitnessKind::EXTENSIONALITY) {
        matched = left.isApplication() && right.isApplication() &&
          left.rhs() == _replayWitness && right.rhs() == _replayWitness &&
          MatchingUtils::matchTerms(literal->eqArgSort().result(), target->eqArgSort(), forward) &&
          MatchingUtils::matchTerms(literal->termArg(0), left.lhs(), forward) &&
          MatchingUtils::matchTerms(literal->termArg(1), right.lhs(), forward);
      } else {
        TermList source = HOL::isBool(literal->termArg(0)) ? literal->termArg(1) : literal->termArg(0);
        auto [head, args] = HOL::getHeadAndArgs(source);
        if (head.isTerm() && args.size() == 1 && left.isApplication() &&
            left.rhs() == _replayWitness && HOL::isBool(right)) {
          matched = MatchingUtils::matchTerms(SortHelper::getResultSort(head.term()).domain(),
                                             HOL::lhsSort(left), forward) &&
            MatchingUtils::matchTerms(args[0], left.lhs(), forward);
        }
      }
      if (!matched) { continue; }
      Substitution inverse;
      bool renaming = true;
      for (auto [variable, value] : iterTraits(forward.items())) {
        if (!value.isVar() || !inverse.bind(value.var(), TermList::var(variable))) {
          renaming = false;
          break;
        }
      }
      VariableIterator variables(_replayWitness);
      while (renaming && variables.hasNext()) {
        TermList value;
        renaming = inverse.findBinding(variables.next().var(), value);
      }
      if (renaming) { return SubstHelper::apply(_replayWitness, inverse); }
    }
  }
  return {};
}

void InferenceRecorder::flexFlexClosure(Clause* conclusion, Clause* parent)
{
  if (!env.reconstruction) { return; }
  DHMap<unsigned, TermList, FnvHash, IdentityHash> sorts;
  SortHelper::collectVariableSorts(parent, sorts);

  Substitution subst;
  std::map<uint64_t, TermList> commonValues; // final result sort -> fresh variable
  unsigned freshVariable = parent->maxVar() + 1;
  for (Literal* literal : parent->iterLits()) {
    for (TermList side : {literal->termArg(0), literal->termArg(1)}) {
      TermList head = side.head();
      TermList bound;
      if (!head.isVar() || subst.findBinding(head.var(), bound)) { continue; }
      TermList sort;
      if (!sorts.find(head.var(), sort)) { return; }
      std::vector<TermList> domains;
      while (sort.isArrowSort()) {
        domains.push_back(sort.domain());
        sort = sort.result();
      }
      auto [entry, fresh] = commonValues.emplace(sort.content(), TermList());
      if (fresh) { entry->second = TermList::var(freshVariable++); }
      TermList value = entry->second;
      TermList valueSort = sort;
      for (auto domain = domains.rbegin(); domain != domains.rend(); ++domain) {
        value = HOL::create::namelessLambda(*domain, valueSort, value);
        valueSort = AtomicSort::arrowSort(*domain, valueSort);
      }
      subst.bindUnbound(head.var(), value);
    }
  }
  // Never assume that a flexible constraint is solvable: check the instance.
  for (Literal* literal : parent->iterLits()) {
    Literal* instance = SubstHelper::apply(literal, subst);
    if (!instance->isEquality() || instance->isPositive() ||
        HOL::reduce::betaNF(instance->termArg(0)) != HOL::reduce::betaNF(instance->termArg(1))) {
      return;
    }
  }
  recordReplayedInferenceCandidate(conclusion, {parent}, std::vector<Substitution>{subst},
      InferenceInformation::LiteralPositionKind::NONE, {});
}


bool InferenceRecorder::subsumptionEqualityResolution(Clause* conclusion, Clause* premise,
    const RobSubstitution& subst, unsigned removedIndex)
{
  // This simplification retains the original survivor names. Compose the
  // unifier with the inverse of its renaming on those surviving variables.
  Substitution inverse;
  auto variables = conclusion->getVariableIterator();
  while (variables.hasNext()) {
    unsigned variable = variables.next();
    TermList unified = subst.apply(TermList::var(variable), 0);
    ASS(unified.isVar());
    inverse.bind(unified.var(), TermList::var(variable));
  }
  Substitution substitution;
  variables = premise->getVariableIterator();
  while (variables.hasNext()) {
    unsigned variable = variables.next();
    substitution.bind(variable, SubstHelper::apply(subst.apply(TermList::var(variable), 0), inverse));
  }
  return recordReplayedInferenceCandidate(conclusion, {premise}, std::vector<Substitution>{substitution},
      InferenceInformation::LiteralPositionKind::REMOVED, {{0, removedIndex}});
}

bool InferenceRecorder::unitResultingResolution(Clause* conclusion,
    const std::vector<Clause*>& premises, const std::vector<Substitution>& substitutions,
    std::vector<InferenceInformation::LiteralPosition> positions)
{
  if (!_currentGoal) { return false; }
  ASS_EQ(premises.size(), substitutions.size());
  ASS_EQ(positions.size() % 2, 0);
  // URR records its parents in resolution order. Present the banks in
  // the original proof's order, consuming repeated parent occurrences once.
  std::vector<Clause*> orderedPremises;
  std::vector<Substitution> orderedSubstitutions;
  std::vector<unsigned> bankMap(premises.size());
  std::vector<bool> used(premises.size(), false);
  auto parents = _currentGoal->getParents();
  while (parents.hasNext()) {
    Unit* parent = parents.next();
    unsigned bank = 0;
    while (bank < premises.size() && (used[bank] || premises[bank] != parent)) { ++bank; }
    if (bank == premises.size()) { return false; }
    used[bank] = true;
    bankMap[bank] = orderedPremises.size();
    orderedPremises.push_back(premises[bank]);
    orderedSubstitutions.push_back(substitutions[bank]);
  }
  if (orderedPremises.size() != premises.size()) { return false; }
  for (auto& position : positions) { position.premiseIndex = bankMap[position.premiseIndex]; }
  // Pair order follows the side-parent banks in the printed certificate.
  for (unsigned pair = 0; pair < positions.size(); pair += 2) {
    for (unsigned other = pair + 2; other < positions.size(); other += 2) {
      if (positions[other + 1].premiseIndex < positions[pair + 1].premiseIndex) {
        std::swap(positions[pair], positions[other]);
        std::swap(positions[pair + 1], positions[other + 1]);
      }
    }
  }
  return recordReplayedInferenceCandidate(conclusion, orderedPremises, orderedSubstitutions,
      InferenceInformation::LiteralPositionKind::RESOLVED, std::move(positions));
}

void InferenceRecorder::equalityResolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolutionDeletion(unsigned int id, Clause *conclusion, Clause *premise, EqResWithDeletion *appl)
{
  recordGenericSubstitutionInference<EqResWithDeletion*>(id, conclusion, {premise}, appl,
    [](EqResWithDeletion *subst, const TermList &term, size_t bank) {
    return subst->apply(term.var());
  });
}

void InferenceRecorder::forwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator *appl, const DemodulatorData *data,
                                            Literal *rewrittenLit)
{
  ASS_EQ(premises.size(), 2);
  std::unordered_map<unsigned int, unsigned int> varMap;
  if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
    std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
    info->conclusion = conclusion;
    info->premises = premises;
    info->literalPositionKind = InferenceInformation::LiteralPositionKind::REWRITTEN;
    info->literalPositions = {{0, literalPosition(premises[0], rewrittenLit)}};
    populateNaturalLiterals(*info, varMap);
    // The matcher bindings below are for the indexed demodulator (the
    // second parent), not for the clause being rewritten.
    info->substitutionForBanksSub.resize(premises.size());

    // The replayed conclusion can be an alpha-variant of the original proof
    // step.  Values produced by `appl` use the replayed names, so translate
    // them back to the names of the printed conclusion.
    Substitution certificateRenaming = conclusionRenaming(varMap);
    unsigned freshVariable = _currentGoal->maxVar() + 1;
    auto mainVariables = premises[0]->getVariableIterator();
    while (mainVariables.hasNext()) {
      unsigned variable = mainVariables.next();
      TermList renamed = renameCertificateTerm(TermList::var(variable), certificateRenaming, freshVariable);
      if (renamed != TermList::var(variable)) { info->substitutionForBanksSub[0].bind(variable, renamed); }
    }
    // DemodulatorData stores the left-hand side and right-hand side after
    // normalizing variables in the left-hand side. Recreate that normalization
    // from the source equality, rather than trying to recover it from the RHS:
    // the RHS need not contain all variables of the demodulator.
    Literal* demodulator = data->clause->literals()[0];
    auto [left, right] = demodulator->eqArgs();
    TermList sort = demodulator->eqArgSort();
    Renaming normalization;
    auto matchesIndexedOrientation = [&](TermList lhs, TermList rhs) {
      normalization.reset();
      normalization.normalizeVariables(TypedTermList(lhs, sort));
      return normalization.apply(lhs) == data->term.untyped()
          && normalization.apply(rhs) == data->rhs
          && normalization.apply(sort) == data->term.sort();
    };
    bool foundOrientation = matchesIndexedOrientation(left, right)
      || matchesIndexedOrientation(right, left);
    if (!foundOrientation) {
      return;
    }

    // we create a custom substitution to apply the substitution only to variables coming from the demodulator
    // otherwise the substitution we get faults
    auto iter = data->clause->getVariableIterator();
    while (iter.hasNext()) {
      auto var = iter.next();
      TermList mappedVar = normalization.apply(TermList::var(var));
      ASS(mappedVar.isVar());
      TermList value = renameCertificateTerm(appl->apply(mappedVar.var()), certificateRenaming, freshVariable);
      info->substitutionForBanksSub[1].bind(var, value);
    }

    _inferences[id] = std::move(info);
    _lastInferenceId = id;
    _hasLastInference = true;
  }
}

bool InferenceRecorder::backwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator& appl,
                                             Literal* rewrittenLit, TermList lhs, TermList rhs)
{
  recordGenericSubstitutionInference<SubstApplicator>(id, conclusion, premises, appl,
    [](const SubstApplicator &subst, const TermList &term, size_t bank) {
      return bank == 0 ? term : SubstHelper::apply(term, subst);
    }, InferenceInformation::LiteralPositionKind::REWRITTEN,
    {{0, literalPosition(premises[0], rewrittenLit)}});
  const auto* info = getLastRecordedInferenceInformation();
  if (!info || info->conclusion != conclusion) { return false; }
  recordRewrite({1, 0}, lhs, 1, rhs, 1);
  return true;
}

bool InferenceRecorder::subsumptionDemodulation(Clause* conclusion, Clause* main,
    Clause* side, const Substitution& subst, Literal* equality, Literal* rewrittenLit,
    TermList lhs, TermList rhs)
{
  recordGenericSubstitutionInference<Substitution>(conclusion->number(), conclusion, {main, side}, subst,
      [](const Substitution& subst, const TermList& term, size_t bank) {
        return bank == 0 ? term : SubstHelper::apply(term, subst);
      }, InferenceInformation::LiteralPositionKind::REWRITTEN,
      {{0, literalPosition(main, rewrittenLit)}});
  const auto* info = getLastRecordedInferenceInformation();
  if (!info || info->conclusion != conclusion) { return false; }
  recordRewrite({1, literalPosition(side, equality)}, lhs, 1, rhs, 1);
  return true;
}

bool InferenceRecorder::innerRewriting(Clause* conclusion, Clause* parent,
    Literal* equality, TermList lhs, TermList rhs)
{
  std::vector<InferenceInformation::LiteralPosition> positions;
  for (unsigned i = 0; i < parent->length(); ++i) {
    if ((*parent)[i] != (*conclusion)[i]) { positions.push_back({0, i}); }
  }
  if (!recordReplayedInferenceCandidate(conclusion, {parent}, std::vector<Substitution>(1),
        InferenceInformation::LiteralPositionKind::REWRITTEN, std::move(positions))) { return false; }
  recordRewrite({0, literalPosition(parent, equality)}, lhs, 0, rhs, 0);
  return true;
}

bool InferenceRecorder::isSameAsProofStep(Clause *clause, Clause *goal, std::unordered_map<unsigned int, unsigned int> &outVarMap)
{
  outVarMap.clear();

  if (!goal || clause->inference().rule() != goal->inference().rule() ||
      clause->length() != goal->length()) {
    return false;
  }
  // An engine can find the same conclusion using a different active parent.
  // Accept only the recorded proof's parent occurrences, including repeats.
  std::unordered_map<Unit*, unsigned> parentOccurrences;
  auto parents = goal->getParents();
  unsigned remainingParents = 0;
  while (parents.hasNext()) { ++parentOccurrences[parents.next()]; ++remainingParents; }
  parents = clause->getParents();
  while (parents.hasNext()) {
    auto found = parentOccurrences.find(parents.next());
    if (found == parentOccurrences.end() || !found->second) { return false; }
    --found->second;
    --remainingParents;
  }
  if (remainingParents) { return false; }

  std::vector<bool> matchedGoalLiterals(goal->length(), false);
  for (unsigned i = 0; i < clause->length(); ++i) {
    bool found = false;
    for (unsigned j = 0; j < goal->length(); ++j) {
      if (!matchedGoalLiterals[j] && (*clause)[i] == (*goal)[j]) {
        matchedGoalLiterals[j] = true;
        found = true;
        break;
      }
    }
    if (!found) {
      break;
    }
  }
  if (std::all_of(matchedGoalLiterals.begin(), matchedGoalLiterals.end(), [](bool matched) { return matched; })) {
    return true;
  }

  if (clause->length() == 0) {
    return true;
  }

  //TODO do some simpler preprocessing here to save on runtime,
  //For now it works
  Clause *c = Clause::fromClause(clause);
  Clause *g = Clause::fromClause(goal);

  Inferences::DuplicateLiteralRemovalISE dlr;
  c = dlr.simplify(c);
  auto simpGoal = dlr.simplify(Clause::fromClause(g));

  if (c->length() != simpGoal->length()) {
    return false;
  }
  if (!MLVariant::isVariant(c, simpGoal)) {
    return false;
  }

  auto variables = [](Clause* cl) {
    std::unordered_set<unsigned> result;
    auto it = cl->getVariableIterator();
    while (it.hasNext()) {
      result.insert(it.next());
    }
    return result;
  };
  if (variables(c).size() != variables(simpGoal).size()) {
    return false;
  }

  static std::vector<LiteralList *> alts;

  alts.clear();
  alts.resize(c->length(), LiteralList::empty());

  //This can probably be optimized with an index
  for (unsigned bi = 0; bi < c->length(); ++bi) {
    Literal *baseLit = (*c)[bi];
    for (unsigned ii = 0; ii < simpGoal->length(); ++ii) {
      Literal *instLit = (*simpGoal)[ii];
      if (MatchingUtils::match(baseLit, instLit, false)) {
        LiteralList::push(instLit, alts[bi]);
      }
    }
    if (LiteralList::isEmpty(alts[bi])) {
      return false;
    }
  }

  MLMatcher matcher;
  // Both clauses have the same length and have already been checked as variants.
  // Preserve the literal-to-literal correspondence while extracting the variable
  // renaming; set matching could reuse one goal literal for multiple replayed ones.
  matcher.init(c, simpGoal, alts.data(), /*multiset=*/true);
  while (matcher.nextMatch()) {
    std::unordered_map<unsigned int, TermList> varToTermMap;
    matcher.getBindings(varToTermMap);
    bool isVariableRenaming = true;
    for (auto [var, term] : varToTermMap) {
      if(!term.isVar()){
        isVariableRenaming = false;
        break;
      }
    }
    if (!isVariableRenaming) {
      continue;
    }
    std::unordered_set<unsigned int> image;
    for (auto [var, term] : varToTermMap) {
      if (!image.insert(term.var()).second) {
        isVariableRenaming = false;
        break;
      }
    }
    if (!isVariableRenaming) {
      continue;
    }
    // The matcher above operates on duplicate-free clauses. Condensation can
    // introduce duplicates, so set equivalence alone is not enough: different
    // substitutions may produce the same set with different multiplicities.
    // Validate the candidate renaming against the original occurrences before
    // accepting it as the recorded proof step.
    Substitution renaming;
    for (auto [var, term] : varToTermMap) {
      renaming.bind(var, term);
    }
    std::vector<bool> consumed(goal->length(), false);
    bool sameOccurrences = true;
    for (Literal* literal : clause->iterLits()) {
      Literal* renamed = SubstHelper::apply(literal, renaming);
      bool found = false;
      for (unsigned j = 0; j < goal->length(); ++j) {
        if (consumed[j]) { continue; }
        Literal* target = (*goal)[j];
        bool same = renamed == target;
        if (!same && renamed->isEquality() && target->isEquality() &&
            renamed->header() == target->header() &&
            renamed->eqArgSort() == target->eqArgSort()) {
          same = renamed->termArg(0) == target->termArg(1) &&
                 renamed->termArg(1) == target->termArg(0);
        }
        if (same) {
          consumed[j] = true;
          found = true;
          break;
        }
      }
      if (!found) {
        sameOccurrences = false;
        break;
      }
    }
    if (!sameOccurrences) { continue; }
    for (auto [var, term] : varToTermMap) {
      outVarMap[var] = term.var();
    }
    return true;
  }
  return false;
}

static InferenceRecorder::InferenceReplayAnnotation subsumptionResolutionReplayAnnotation(Unit* us)
{
  if (us->inference().rule() != InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION) {
    return {};
  }

  auto parents = us->getParents();
  if (!parents.hasNext()) {
    return {};
  }
  Unit* simplifiedUnit = parents.next();
  if (!simplifiedUnit->isClause() || !parents.hasNext()) {
    return {};
  }
  Clause* simplified = simplifiedUnit->asClause();
  Unit* sideUnit = parents.next();
  if (!sideUnit->isClause()) {
    return {};
  }
  Clause* side = sideUnit->asClause();
  Clause* conclusion = us->asClause();

  // Consume occurrences, rather than testing set membership: removing one
  // of several equal literals still has a concrete position in the parent.
  std::unordered_map<Literal*, unsigned> survivingOccurrences;
  for (Literal* literal : conclusion->iterLits()) {
    ++survivingOccurrences[literal];
  }

  for (unsigned i = 0; i < simplified->length(); ++i) {
    Literal* candidate = (*simplified)[i];
    unsigned& occurrences = survivingOccurrences[candidate];
    bool survives = occurrences != 0;
    if (survives) {
      --occurrences;
    }
    if (!survives) {
      std::vector<Literal*> naturalLiterals;
      for (unsigned j = 0; j < simplified->length(); ++j) {
        if (j != i) {
          naturalLiterals.push_back((*simplified)[j]);
        }
      }
      //Reconstruct with SATSubsumption
      SATSubsumption::SATSubsumptionAndResolution satSR;
      InferenceRecorder::InferenceReplayAnnotation result;
      result.removedLiteralParent = simplified;
      result.removedLiteralIndex = i;
      result.naturalLiterals = std::move(naturalLiterals);
      if (!satSR.checkSubsumptionResolutionWithLiteral(side, simplified, i)) {
        return result;
      }
      auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();
      for (auto [var, term] : iterTraits(subst.items())) {
        result.subsumptionBindings.push_back({var, term});
      }
      result.subsumptionUnifierParent = side;
      return result;
    }
  }
  return {};
}

InferenceRecorder::InferenceReplayAnnotation InferenceRecorder::inferenceReplayAnnotation(Unit* us, InferenceReplayer& replayer, bool replay)
{
  if (!replay || !us->isClause()) {
    return {};
  }

  // Subsumption resolution is a simplifying inference. Replaying it
  // mutates the replay algorithm's active index, whereas its certificate can
  // be recovered directly from the original clauses.
  InferenceReplayAnnotation subsumptionInfo = subsumptionResolutionReplayAnnotation(us);
  if (subsumptionInfo.removedLiteralParent) {
    return subsumptionInfo;
  }

  replayer.replayInference(us);
  const auto* info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
  if (!info) {
    return {};
  }

  InferenceReplayAnnotation result;
  result.information = info;
  return result;
}


InferenceRecorder::InferenceRecorder()
{
}

InferenceRecorder::~InferenceRecorder()
{
}
} // namespace Shell

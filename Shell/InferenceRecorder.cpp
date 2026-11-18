/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InferenceRecorder.hpp"

#include "Debug/Assertion.hpp"
#include "Indexing/DemodulationIndex.hpp"

#include "Kernel/MLMatcher.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include <algorithm>
#include <functional>
#include <utility>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Indexing;
namespace Shell {

namespace { unsigned literalPosition(Clause* clause, Literal* literal); }

InferenceRecorder* InferenceRecorder::_active = nullptr;

InferenceRecorder::InferenceRecorder(Clause* goal)
  : _activation(_active, this), _currentGoal(goal)
{}

InferenceRecorder* InferenceRecorder::instance()
{
  ASS(_active);
  return _active;
}

Substitution InferenceRecorder::goalAlphaRenaming(const std::unordered_map<unsigned, unsigned>& varMap)
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

TermList InferenceRecorder::alphaRenameToGoal(TermList term, Substitution& renaming,
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

std::optional<InferenceRecorder::InferenceInformation> InferenceRecorder::record(Clause* conclusion, std::vector<Clause*> premises,
                               Substitutions substitutions, Substitution* outputRenaming)
{
  ASS_EQ(substitutions.size(), premises.size());
  VariableMap varMap;
  if (!isSameAsProofStep(conclusion, _currentGoal, varMap)) { return std::nullopt; }
  auto info = std::make_optional<InferenceInformation>();
  info->conclusion = _currentGoal;
  info->premises = std::move(premises);
  info->substitutionForBanksSub.resize(info->premises.size());
  Substitution renaming = goalAlphaRenaming(varMap);
  unsigned freshVariable = _currentGoal->maxVar() + 1;
  for (unsigned bank = 0; bank < info->premises.size(); ++bank) {
    ASS(substitutions.begin()[bank]);
    auto variables = info->premises[bank]->getVariableIterator();
    while (variables.hasNext()) {
      unsigned variable = variables.next();
      TermList value = alphaRenameToGoal(substitutions.begin()[bank]->apply(variable),
                                            renaming, freshVariable);
      if (value != TermList::var(variable)) {
        info->substitutionForBanksSub[bank].bind(variable, value);
      }
    }
  }
  if (outputRenaming) { *outputRenaming = std::move(renaming); }
  return info;
}

void InferenceRecorder::superposition(Clause* conclusion, Clause* main,
    Clause* equality, Substitutions substitutions,
    Literal* rewrittenLiteral, Literal* equalityLiteral, TermList lhs, TermList target,
    unsigned constraintCount)
{
  Substitution renaming;
  auto info = record(conclusion, {main, equality}, substitutions, &renaming);
  if (!info) { return; }
  using Extra = Inferences::CompositeInferenceExtra<
      Inferences::LiteralRewriteExtra,
      InferenceInformation, ConstraintInformation>;
  const auto mainPosition = literalPosition(main, rewrittenLiteral);
  const auto equalityPosition = literalPosition(equality, equalityLiteral);
  auto extra = std::make_unique<Extra>(
      Inferences::LiteralRewriteExtra(
          Inferences::twoLiteralExtra(rewrittenLiteral, equalityLiteral, mainPosition, equalityPosition),
          Inferences::rewriteExtra(lhs, target, equalityPosition, mainPosition)),
      std::move(*info), ConstraintInformation{});
  ASS_LE(constraintCount, conclusion->length());
  recordConstraints(conclusion, extra->get<ConstraintInformation>(), renaming, conclusion->length() - constraintCount, constraintCount);
  _information = std::move(extra);
}

void InferenceRecorder::resolution(Clause* conclusion, Clause* left, Clause* right,
    Substitutions substitutions, Literal* resolvedLeft, Literal* resolvedRight,
    unsigned constraintCount)
{
  Substitution renaming;
  auto info = record(conclusion, {left, right},
      substitutions, &renaming);
  if (!info) { return; }
  using Extra = Inferences::CompositeInferenceExtra<
      Inferences::TwoLiteralInferenceExtra, InferenceInformation, ConstraintInformation>;
  auto extra = std::make_unique<Extra>(
      Inferences::twoLiteralExtra(resolvedLeft, resolvedRight,
          literalPosition(left, resolvedLeft),
          literalPosition(right, resolvedRight)),
      std::move(*info), ConstraintInformation{});
  recordConstraints(conclusion, extra->get<ConstraintInformation>(), renaming, 0, constraintCount);
  _information = std::move(extra);
}

void InferenceRecorder::recordConstraints(Clause* candidate,
    ConstraintInformation& constraints, const Substitution& renaming,
    unsigned first, unsigned count)
{
  ASS_LE(first + count, candidate->length());
  for (unsigned i = first; i < first + count; ++i) {
    constraints.literals.push_back(SubstHelper::apply((*candidate)[i], renaming));
  }
}

void InferenceRecorder::factoring(Clause* conclusion, Clause* premise,
                                 Substitutions substitutions, Literal* selectedLiteral, Literal* removedLiteral)
{
  auto info = record(conclusion, {premise}, substitutions);
  if (info) {
    using Extra = Inferences::CompositeInferenceExtra<
        Inferences::TwoLiteralInferenceExtra, InferenceInformation>;
    auto extra = std::make_unique<Extra>(
        Inferences::twoLiteralExtra(selectedLiteral, removedLiteral,
            literalPosition(premise, selectedLiteral),
            literalPosition(premise, removedLiteral)),
        std::move(*info));
    _information = std::move(extra);
  }
}

void InferenceRecorder::forwardDemodulation(Clause* conclusion, Clause* premise,
    Clause* equality, Substitutions substitutions, Literal* rewrittenLiteral,
    TermList lhs, TermList target)
{
  auto info = record(conclusion, {premise, equality}, substitutions);
  if (info) {
    using Extra = Inferences::CompositeInferenceExtra<
        Inferences::RewriteInferenceExtra, InferenceInformation>;
    auto extra = std::make_unique<Extra>(
        Inferences::rewriteExtra(lhs, target, 0,
            literalPosition(premise, rewrittenLiteral)),
        std::move(*info));
    _information = std::move(extra);
  }
}

InferenceRecorder::DemodulationApplicator::DemodulationApplicator(
    const SubstApplicator& subst, const DemodulatorData& data) : subst(subst)
{
  Literal* equality = (*data.clause)[0];
  auto [left, right] = equality->eqArgs();
  TermList sort = equality->eqArgSort();
  auto matches = [&](TermList from, TermList to) {
    normalization.reset();
    normalization.normalizeVariables(TypedTermList(from, sort));
    return normalization.apply(from) == data.term.untyped()
        && normalization.apply(to) == data.rhs
        && normalization.apply(sort) == data.term.sort();
  };
  _valid = matches(left, right);
  if (!_valid) {
    _valid = matches(right, left);
    std::swap(left, right);
  }
  lhs = left;
  rhs = right;
}

TermList InferenceRecorder::DemodulationApplicator::apply(unsigned variable) const
{
  ASS(_valid);
  return subst.apply(normalization.get(variable));
}

namespace {
unsigned literalPosition(Clause* clause, Literal* literal)
{
  for (unsigned i = 0; i < clause->length(); ++i) {
    if ((*clause)[i] == literal) { return i; }
  }
  ASSERTION_VIOLATION;
}

// Compare multisets, retaining duplicate occurrences and equality symmetry.
bool sameLiteralOccurrences(Clause* clause, Clause* goal, const Substitution& renaming)
{
  std::vector<bool> consumed(goal->length(), false);
  for (Literal* literal : clause->iterLits()) {
    Literal* renamed = SubstHelper::apply(literal, renaming);
    bool found = false;
    for (unsigned j = 0; j < goal->length(); ++j) {
      if (consumed[j]) { continue; }
      Literal* target = (*goal)[j];
      bool same = renamed == target;
      if (!same && renamed->isEquality() && target->isEquality() &&
          renamed->header() == target->header() && renamed->eqArgSort() == target->eqArgSort()) {
        same = renamed->termArg(0) == target->termArg(1) && renamed->termArg(1) == target->termArg(0);
      }
      if (same) { consumed[j] = true; found = true; break; }
    }
    if (!found) { return false; }
  }
  return true;
}
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

  if (sameLiteralOccurrences(clause, goal, Substitution())) { return true; }

  // MLMatcher requires a duplicate-free base. Deduplicate pointers only;
  // keep both proof clauses intact and check multiplicities after matching.
  std::vector<Literal*> base(clause->begin(), clause->end());
  std::sort(base.begin(), base.end(), std::less<Literal*>{});
  base.erase(std::unique(base.begin(), base.end()), base.end());

  struct Alternatives {
    std::vector<LiteralList*> lists;
    ~Alternatives() { for (auto list : lists) { LiteralList::destroy(list); } }
  } alternatives{std::vector<LiteralList*>(base.size(), nullptr)};
  for (unsigned i = 0; i < base.size(); ++i) {
    for (Literal* target : goal->iterLits()) {
      if (MatchingUtils::match(base[i], target, false)) {
        LiteralList::push(target, alternatives.lists[i]);
      }
    }
    if (!alternatives.lists[i]) { return false; }
  }

  MLMatcher matcher;
  matcher.init(base.data(), base.size(), goal, alternatives.lists.data(), /*multiset=*/false);
  while (matcher.nextMatch()) {
    std::unordered_map<unsigned int, TermList> varToTermMap;
    matcher.getBindings(varToTermMap);
    bool isVariableRenaming = true;
    std::unordered_set<unsigned> image;
    for (auto [var, term] : varToTermMap) {
      if (!term.isVar() || !image.insert(term.var()).second) {
        isVariableRenaming = false;
        break;
      }
    }
    if (!isVariableRenaming) { continue; }
    Substitution renaming;
    for (auto [var, term] : varToTermMap) {
      renaming.bind(var, term);
    }
    if (!sameLiteralOccurrences(clause, goal, renaming)) { continue; }
    for (auto [var, term] : varToTermMap) {
      outVarMap[var] = term.var();
    }
    return true;
  }
  return false;
}

} // namespace Shell

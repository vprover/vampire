/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "TPTPReplayAnnotations.hpp"

#include "Debug/Assertion.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/InferenceReplay.hpp"

#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <unordered_map>
#include <utility>

namespace Shell::TPTPReplayAnnotations {

using namespace Kernel;
using namespace Lib;

static std::string tptpUnitId(Unit* unit)
{
  return "f" + Int::toString(unit->number());
}

static ReplayAnnotation subsumptionResolutionInfo(Unit* us)
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
      if (!satSR.checkSubsumptionResolutionWithLiteral(side, simplified, i)) {
        return {"removed_literals(literal(" + tptpUnitId(simplified) + ',' + Int::toString(i) + "))",
                nullptr, std::move(naturalLiterals)};
      }
      auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();

      std::ostringstream res;
      res << "unifier([subs(" << tptpUnitId(side) << ",[";
      bool first = true;
      for (auto [var, term] : iterTraits(subst.items())) {
        if (!first) {
          res << ',';
        }
        first = false;
        res << "b(X" << var << ',' << term.toString() << ')';
      }
      res << "])])";
      res << ",removed_literals(literal(" << tptpUnitId(simplified) << ',' << i << "))";
      return {res.str(), nullptr, std::move(naturalLiterals)};
    }
  }
  return {};
}

ReplayAnnotation replayedUnifier(Unit* us, InferenceReplayer& replayer, bool replay)
{
  if (!replay || !us->isClause()) {
    return {};
  }

  // Subsumption resolution is a simplifying inference. Replaying it
  // mutates the replay algorithm's active index, whereas its certificate can
  // be recovered directly from the original clauses.
  ReplayAnnotation subsumptionInfo = subsumptionResolutionInfo(us);
  if (!subsumptionInfo.text.empty()) {
    return subsumptionInfo;
  }

  InferenceRecorder::instance()->setCurrentGoal(us->asClause());
  replayer.replayInference(us);
  const auto* info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
  if (!info) {
    return {};
  }

  std::ostringstream res;
  res << "unifier([";
  for (unsigned bank = 0; bank < info->substitutionForBanksSub.size(); bank++) {
    if (bank) {
      res << ',';
    }
    res << "subs(";
    if (bank < info->premises.size()) {
      res << tptpUnitId(info->premises[bank]);
    } else {
      res << bank;
    }
    res << ",[";
    auto subst = info->substitutionForBanksSub[bank];
    bool first = true;
    for (auto [var, term] : iterTraits(subst.items())) {
      if (!first) {
        res << ',';
      }
      first = false;
      res << "b(X" << var << "," << term.toString() << ")";
    }
    res << "])";
  }
  res << "])";

  if (!info->constraints.empty()) {
    res << ",constraints([";
    bool first = true;
    for (Literal* literal : info->constraints) {
      ASS(literal->isEquality() && literal->isNegative());
      if (!first) { res << ','; }
      first = false;
      auto [left, right] = literal->eqArgs();
      res << "disequality(" << literal->eqArgSort().toString() << ','
          << left.toString() << ',' << right.toString() << ')';
    }
    res << "])";
  }
  auto printPosition = [&](const auto& position) {
    res << "literal(" << tptpUnitId(info->premises[position.premiseIndex])
        << ',' << position.literalIndex << ')';
  };
  if (info->hasRewrite) {
    res << ",rewrite([equality(";
    printPosition(info->rewriteEquality);
    res << "),from(" << info->rewriteFrom.toString()
        << "),to(" << info->rewriteTo.toString() << ")])";
  }
  if (us->inference().rule() == InferenceRule::FORWARD_LITERAL_REWRITING &&
      !info->literalPositions.empty()) {
    const auto& position = info->literalPositions[0];
    res << ",rewritten_literal(literal(" << tptpUnitId(info->premises[position.premiseIndex])
        << ',' << position.literalIndex << "))";
  }

  if (!info->literalPositions.empty()) {
    using PositionKind = InferenceRecorder::InferenceInformation::LiteralPositionKind;
    switch (info->literalPositionKind) {
    case PositionKind::REWRITTEN:
      res << (info->literalPositions.size() == 1 ? ",rewritten_literal(" : ",rewritten_literals([");
      break;
    case PositionKind::RESOLVED:
      res << ",resolved_literals([";
      break;
    case PositionKind::REMOVED:
      res << ",removed_literals(";
      break;
    case PositionKind::NONE:
      ASSERTION_VIOLATION;
    }

    bool first = true;
    for (const auto &position : info->literalPositions) {
      if (!first) {
        res << ',';
      }
      first = false;
      printPosition(position);
    }
    bool list = info->literalPositionKind == PositionKind::RESOLVED ||
                (info->literalPositionKind == PositionKind::REWRITTEN && info->literalPositions.size() != 1);
    res << (list ? "])" : ")");
  }
  return {res.str(), info};
}

std::string rectificationInfo(Unit* us, bool replay)
{
  if (!replay || us->inference().rule() != InferenceRule::RECTIFY) {
    return "";
  }
  const auto* info = InferenceRecorder::instance()->getRectifyInferenceInformation(us->number());
  if (!info || info->scopes.empty()) {
    return "";
  }

  std::ostringstream result;
  // `postorder` makes scope association unambiguous for nested and sibling
  // quantifiers. `before`/`after` retain their declared binder order;
  // `substitution` is LeanChecker's combined occurrence map, not merely a
  // fresh-name map, so it captures permutations inside terms as well.
  result << "rectify([postorder([";
  bool firstScope = true;
  for (const auto& scope : info->scopes) {
    std::vector<std::string> entries;
    auto printBinders = [](const char* name, const std::vector<unsigned>& binders) {
      std::ostringstream result;
      result << name << "([";
      for (unsigned i = 0; i < binders.size(); ++i) {
        if (i) {
          result << ',';
        }
        result << "X" << binders[i];
      }
      result << "])";
      return result.str();
    };
    Substitution renaming = scope.renaming;
    std::vector<std::pair<unsigned, std::string>> bindings;
    for (auto [source, target] : iterTraits(renaming.items())) {
      if (scope.removed.find(source) != scope.removed.end() ||
          target == TermList::var(source)) {
        continue;
      }
      bindings.emplace_back(source,
        "b(X" + Int::toString(source) + "," + target.toString() + ")");
    }
    std::sort(bindings.begin(), bindings.end(),
      [](const auto& left, const auto& right) { return left.first < right.first; });
    // A fresh one-variable binder is alpha-equivalent and needs no proof
    // step. Retain a scope only if LeanChecker's combined substitution
    // records a genuine variable permutation or a binder was removed.
    if (bindings.empty() && scope.removed.empty()) {
      continue;
    }
    entries.push_back(printBinders("before", scope.sourceBinders));
    entries.push_back(printBinders("after", scope.targetBinders));
    if (!bindings.empty()) {
      std::ostringstream substitution;
      substitution << "substitution([";
      for (unsigned i = 0; i < bindings.size(); ++i) {
        if (i) {
          substitution << ',';
        }
        substitution << bindings[i].second;
      }
      substitution << "])";
      entries.push_back(substitution.str());
    }
    if (!scope.removed.empty()) {
      std::ostringstream removed;
      removed << "removed([";
      bool firstRemoved = true;
      for (unsigned variable : scope.removed) {
        if (!firstRemoved) {
          removed << ',';
        }
        firstRemoved = false;
        removed << "X" << variable;
      }
      removed << "])";
      entries.push_back(removed.str());
    }
    if (!firstScope) {
      result << ',';
    }
    firstScope = false;
    result << "scope([";
    for (unsigned i = 0; i < entries.size(); ++i) {
      if (i) {
        result << ',';
      }
      result << entries[i];
    }
    result << "])";
  }
  result << "])])";
  return firstScope ? "" : result.str();
}

struct AvatarSplitComponent {
  Unit* definition;
  Clause* clause;
};

struct AvatarSplitVariableTarget {
  Unit* definition;
  unsigned variable;
};

/**
 * Return the variable-disjoint literal components used by AVATAR splitting.
 * This is the part of Splitter::getComponents needed by the proof printer,
 * deliberately without its statistics side effects.
 */
static std::vector<std::vector<Literal*>> avatarSplitComponents(Clause* clause)
{
  std::vector<std::vector<Literal*>> result;
  if (clause->length() == 0) {
    return result;
  }

  std::vector<unsigned> parents(clause->length());
  for (unsigned i = 0; i < parents.size(); ++i) {
    parents[i] = i;
  }
  auto findRoot = [&parents](unsigned index) {
    while (parents[index] != index) {
      parents[index] = parents[parents[index]];
      index = parents[index];
    }
    return index;
  };
  auto merge = [&findRoot, &parents](unsigned first, unsigned second) {
    first = findRoot(first);
    second = findRoot(second);
    if (first != second) {
      parents[second] = first;
    }
  };

  std::map<unsigned, unsigned> masters;
  for (unsigned literalIndex = 0; literalIndex < clause->length(); ++literalIndex) {
    VariableIterator variables((*clause)[literalIndex]);
    while (variables.hasNext()) {
      unsigned variable = variables.next().var();
      auto [master, inserted] = masters.emplace(variable, literalIndex);
      if (!inserted) {
        merge(master->second, literalIndex);
      }
    }
  }

  std::map<unsigned, std::vector<Literal*>> components;
  for (unsigned literalIndex = 0; literalIndex < clause->length(); ++literalIndex) {
    components[findRoot(literalIndex)].push_back((*clause)[literalIndex]);
  }
  for (auto& [_, component] : components) {
    result.push_back(std::move(component));
  }
  return result;
}

/**
 * Recover the argument order used after the AVATAR-definition rewrites.
 *
 * The first premise is the original clause.  Each newly introduced
 * definition premise is a variant of one variable-disjoint component of
 * that clause.  Consequently the variant renaming tells us exactly which
 * definition variable is passed for each original-clause variable.  Unlike
 * LeanChecker, this does not need SATClauseExtra: the original clause's
 * split set already distinguishes old definitions from definitions added by
 * this split.  SplitDefinitionExtra remains necessary to get the component
 * clause behind a definition formula.
 */
std::string avatarSplitInstantiationInfo(Unit* conclusion)
{
  if (conclusion->inference().rule() != InferenceRule::AVATAR_SPLIT_CLAUSE) {
    return "";
  }

  UnitIterator parents = conclusion->getParents();
  if (!parents.hasNext()) {
    return "";
  }
  Unit* originalUnit = parents.next();
  if (!originalUnit->isClause()) {
    return "";
  }
  Clause* original = originalUnit->asClause();

  std::set<unsigned> oldSplitVariables;
  if (!original->noSplits()) {
    for (SplitLevel split : iterTraits(original->splits()->iter())) {
      oldSplitVariables.insert(Saturation::Splitter::getLiteralFromName(split).var());
    }
  }

  std::vector<AvatarSplitComponent> newComponents;
  while (parents.hasNext()) {
    Unit* definition = parents.next();
    if (definition->inference().rule() != InferenceRule::AVATAR_DEFINITION) {
      return "";
    }
    const auto* extra = env.proofExtra.find(definition);
    if (!extra) {
      return "";
    }
    const auto* splitDefinition = static_cast<const Saturation::SplitDefinitionExtra*>(extra);
    Clause* component = splitDefinition->component;
    if (!component || !component->isComponent() || component->noSplits()) {
      return "";
    }
    unsigned splitVariable =
      Saturation::Splitter::getLiteralFromName(component->splits()->sval()).var();
    if (!oldSplitVariables.contains(splitVariable)) {
      newComponents.push_back({definition, component});
    }
  }
  if (newComponents.empty()) {
    return "";
  }

  std::map<unsigned, AvatarSplitVariableTarget> instantiation;
  for (const auto& sourceComponent : avatarSplitComponents(original)) {
    bool matched = false;
    for (const auto& targetComponent : newComponents) {
      if (sourceComponent.size() != targetComponent.clause->length()) {
        continue;
      }
      Substitution componentToOriginal;
      if (!MLVariant::isVariant(sourceComponent.data(), targetComponent.clause,
                                /* complementary */ false, &componentToOriginal)) {
        continue;
      }
      // MLVariant records component-variable -> original-variable.  Reverse
      // it to obtain the arguments supplied to the original clause after
      // rewriting by a component definition, as LeanChecker does.
      for (const auto& [targetVariable, sourceTerm] : iterTraits(componentToOriginal.items())) {
        if (!sourceTerm.isVar()) {
          return "";
        }
        unsigned sourceVariable = sourceTerm.var();
        auto [entry, inserted] = instantiation.emplace(
          sourceVariable, AvatarSplitVariableTarget{targetComponent.definition, targetVariable});
        if (!inserted &&
            (entry->second.definition != targetComponent.definition ||
             entry->second.variable != targetVariable)) {
          return "";
        }
      }
      matched = true;
      break;
    }
    if (!matched) {
      return "";
    }
  }
  if (instantiation.empty()) {
    return "";
  }

  std::ostringstream result;
  result << "post_rewrite_instantiation([";
  bool first = true;
  for (const auto& [sourceVariable, target] : instantiation) {
    if (!first) {
      result << ',';
    }
    first = false;
    // The bindings are ordered by the source variable, exactly as the
    // corresponding application of the first premise is built in
    // LeanChecker::avatarSplitClause.  `arg(fN,XM)` locates the
    // variable in the rewritten definition premise fN.
    result << "b(X" << sourceVariable << ",arg("
           << tptpUnitId(target.definition) << ",X" << target.variable << "))";
  }
  result << "])";
  return result.str();
}

} // namespace Shell::TPTPReplayAnnotations

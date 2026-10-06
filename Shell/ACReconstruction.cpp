/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ACReconstruction.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Unit.hpp"

#include <algorithm>
#include <sstream>
#include <unordered_map>
#include <unordered_set>

namespace Shell::ACReconstruction {

using namespace Kernel;

namespace {

/**
 * The TSTP printer works with the final, selected form of a clause.  A
 * replayed inference, on the other hand, returns the clause in the order in
 * which the calculus rule constructed it.  Keep that order visible in a
 * separate node and make any subsequent presentation change explicit.
 *
 * Pointer identity covers the normal shared-literal path. The replay result
 * can be an alpha-variant of the displayed clause, in which case the slow
 * fallback recognizes the same literal (or a symmetric equality).
 * Equality reversals are left for the later proof-reconstruction pass.
 */
static bool sameLiteralOrSymmetry(Literal* source, Literal* target)
{
  if (source == target) {
    return true;
  }
  if (source->header() != target->header() || source->arity() != target->arity()) {
    return false;
  }
  if (!source->isEquality()) {
    return MatchingUtils::isVariant(source, target);
  }
  if (MatchingUtils::haveVariantArgs(source, target)) {
    return true;
  }
  return MatchingUtils::haveReversedVariantArgs(source, target);
}

} // namespace

/**
 * Build the core literal order and the occurrence permutation from that core
 * to the printed conclusion.  Every source occurrence is consumed exactly
 * once, which is essential for clauses containing duplicate literals.
 */
bool clauseOrderBridge(Unit* conclusion, InferenceRule rule,
                       const InferenceRecorder::InferenceInformation* information,
                       std::vector<Literal*>& core,
                       std::vector<unsigned>& permutation)
{
  if (!conclusion->isClause()) {
    return false;
  }

  if (rule == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION) {
    // The direct certificate recovery supplied the main parent with its
    // selected occurrence deleted, preserving all other parent positions.
    if (core.empty()) {
      return false;
    }
  } else if (rule == InferenceRule::TRIVIAL_INEQUALITY_REMOVAL ||
             rule == InferenceRule::REMOVE_DUPLICATE_LITERALS) {
    auto parents = conclusion->getParents();
    if (!parents.hasNext()) {
      return false;
    }
    Unit* parent = parents.next();
    if (!parent->isClause() || parents.hasNext()) {
      return false;
    }
    std::unordered_set<Literal*> seen;
    for (Literal* literal : parent->asClause()->iterLits()) {
      if (rule == InferenceRule::REMOVE_DUPLICATE_LITERALS) {
        // Shared literal identity is the duplicate-removal rule's test.
        // Keep each first occurrence in parent order; any presentation
        // permutation belongs to the following AC node.
        if (!seen.insert(literal).second) {
          continue;
        }
      } else if (literal->isEquality()) {
        auto [left, right] = literal->eqArgs();
        if ((!literal->polarity() && left.sameContent(right)) ||
            (literal->polarity() &&
             ((HOL::isTrue(left) && HOL::isFalse(right)) ||
              (HOL::isTrue(right) && HOL::isFalse(left))))) {
          continue;
        }
      }
      core.push_back(literal);
    }
  } else if (rule == InferenceRule::CONDENSATION ||
             rule == InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION ||
             rule == InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION) {
    unsigned parentCount = rule == InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION ? 2 : 1;
    if (!information || information->premises.size() != parentCount ||
        information->substitutionForBanksSub.size() != parentCount ||
        information->literalPositionKind !=
          InferenceRecorder::InferenceInformation::LiteralPositionKind::REMOVED ||
        information->literalPositions.size() != 1 ||
        information->literalPositions[0].premiseIndex != 0) {
      return false;
    }
    Clause* parent = information->premises[0];
    unsigned removed = information->literalPositions[0].literalIndex;
    if (removed >= parent->length()) { return false; }
    // General condensation moves its retained unified literal to the front.
    // The proof rule instead instantiates the parent and removes one duplicate
    // occurrence in place, preserving all other literal positions.
    const auto& subst = information->substitutionForBanksSub[0];
    for (unsigned i = 0; i < parent->length(); ++i) {
      if (i != removed) { core.push_back(SubstHelper::apply((*parent)[i], subst)); }
    }
  } else if (rule == InferenceRule::EXTENSIONALITY_RESOLUTION ||
             rule == InferenceRule::UNIT_RESULTING_RESOLUTION ||
             rule == InferenceRule::CONSTRAINED_RESOLUTION ||
             rule == InferenceRule::FORWARD_LITERAL_REWRITING) {
    if (!information || information->literalPositionKind !=
          InferenceRecorder::InferenceInformation::LiteralPositionKind::RESOLVED ||
        information->premises.size() != information->substitutionForBanksSub.size()) { return false; }
    core = information->constraints;
    bool rewrite = rule == InferenceRule::FORWARD_LITERAL_REWRITING;
    if (rewrite && (information->premises.size() != 2 ||
                    information->literalPositions.size() != 2)) { return false; }
    for (unsigned bank = 0; bank < information->premises.size(); ++bank) {
      Clause* parent = information->premises[bank];
      const auto& subst = information->substitutionForBanksSub[bank];
      for (unsigned i = 0; i < parent->length(); ++i) {
        bool removed = false;
        for (const auto& position : information->literalPositions) {
          if (position.premiseIndex == bank && position.literalIndex == i) { removed = true; break; }
        }
        if (rewrite && bank == 0 && removed) {
          unsigned sideRemoved = information->literalPositions[1].literalIndex;
          if (information->premises[1]->length() != 2 || sideRemoved >= 2) { return false; }
          core.push_back(SubstHelper::apply((*information->premises[1])[1 - sideRemoved],
                                          information->substitutionForBanksSub[1]));
        } else if (!removed && (!rewrite || bank == 0)) {
          core.push_back(SubstHelper::apply((*parent)[i], subst));
        }
      }
    }
  } else {
    if (!information || !information->conclusion) {
      return false;
    }
    if (!information->naturalLiterals.empty()) {
      core = information->naturalLiterals;
    } else {
      for (Literal* literal : information->conclusion->iterLits()) {
        core.push_back(literal);
      }
    }
  }

  // Superposition constructs its raw result as
  //   rewritten-literal, rewritten-parent-tail, equality-parent-tail.
  // Forward demodulation likewise puts the rewritten literal first.
  // Move the rewritten literal back to its selected source position; the AC
  // node below then records the change back to Vampire's displayed order.
  if (information &&
      (rule == InferenceRule::SUPERPOSITION || rule == InferenceRule::CONSTRAINED_SUPERPOSITION ||
       rule == InferenceRule::FORWARD_DEMODULATION || rule == InferenceRule::BACKWARD_DEMODULATION) &&
      information->literalPositionKind ==
        InferenceRecorder::InferenceInformation::LiteralPositionKind::REWRITTEN &&
      information->literalPositions.size() == 1 &&
      information->literalPositions[0].premiseIndex == 0 &&
      information->premises.size() == 2 &&
      information->literalPositions[0].literalIndex < information->premises[0]->length() &&
      information->premises[0]->length() <= core.size()) {
    unsigned rewrittenPosition = information->literalPositions[0].literalIndex;
    std::rotate(core.begin(), core.begin() + 1,
                core.begin() + rewrittenPosition + 1);
  }

  Clause* printed = conclusion->asClause();
  if (core.size() != printed->length()) {
    return false;
  }

  std::unordered_map<Literal*, std::vector<unsigned>> sourcePositions;
  sourcePositions.reserve(core.size());
  for (unsigned sourcePosition = 0; sourcePosition < core.size(); ++sourcePosition) {
    sourcePositions[core[sourcePosition]].push_back(sourcePosition);
  }
  std::unordered_map<Literal*, unsigned> nextSourcePosition;
  nextSourcePosition.reserve(sourcePositions.size());
  std::vector<bool> consumed(core.size(), false);
  for (unsigned targetPosition = 0; targetPosition < printed->length(); ++targetPosition) {
    bool found = false;
    Literal* target = (*printed)[targetPosition];
    auto occurrences = sourcePositions.find(target);
    if (occurrences != sourcePositions.end()) {
      unsigned& next = nextSourcePosition[target];
      if (next < occurrences->second.size()) {
        unsigned sourcePosition = occurrences->second[next++];
        consumed[sourcePosition] = true;
        permutation.push_back(sourcePosition);
        found = true;
      }
    }
    if (found) {
      continue;
    }

    // Equality terms can be spelled in the opposite orientation. This is
    // rare and deliberately the only non-constant-time lookup.
    for (unsigned sourcePosition = 0; sourcePosition < core.size(); ++sourcePosition) {
      if (consumed[sourcePosition]) {
        continue;
      }
      if (!sameLiteralOrSymmetry(core[sourcePosition], target)) {
        continue;
      }
      consumed[sourcePosition] = true;
      permutation.push_back(sourcePosition);
      found = true;
      break;
    }
    if (!found) {
      return false;
    }
  }

  bool identity = true;
  for (unsigned i = 0; identity && i < permutation.size(); ++i) {
    identity = permutation[i] == i;
  }
  return !identity;
}

std::string acInference(const std::string& parent, const std::vector<unsigned>& permutation)
{
  std::ostringstream result;
  result << "inference(associativity_commutativity,[permutation([";
  for (unsigned i = 0; i < permutation.size(); ++i) {
    if (i) {
      result << ',';
    }
    result << permutation[i];
  }
  result << "])],[" << parent << "])";
  return result.str();
}

} // namespace Shell::ACReconstruction

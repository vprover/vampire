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
  } else {
    if (!information || !information->conclusion) {
      return false;
    }
    for (Literal* literal : information->conclusion->iterLits()) {
      core.push_back(literal);
    }
  }

  // Superposition constructs its raw result as
  //   rewritten-literal, rewritten-parent-tail, equality-parent-tail.
  // Forward demodulation likewise puts the rewritten literal first.
  // Move the rewritten literal back to its selected source position; the AC
  // node below then records the change back to Vampire's displayed order.
  if (information &&
      (rule == InferenceRule::SUPERPOSITION || rule == InferenceRule::FORWARD_DEMODULATION) &&
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

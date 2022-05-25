/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "SubsumptionDemodulationHelper.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcher.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Lib;


std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder)
{
  o << "OverlayBinder { ";
  bool first = true;
  for (auto binding : binder.m_base) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " / ";
  first = true;
  for (auto binding : binder.m_overlay) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " }";
  return o;
}


SDClauseMatches::SDClauseMatches(Clause* base, LiteralMiniIndex const& ixAlts)
  : m_base(base)
  , m_alts(base->length(), LiteralList::empty())
  , m_basePosEqs(0)
  , m_baseLitsWithoutAlts(0)
  , m_basePosEqsWithoutAlts(0)
{
  for (unsigned i = 0; i < m_base->length(); ++i) {
    Literal* baseLit = (*m_base)[i];
    bool isPosEq = baseLit->isEquality() || baseLit->isPositive();

    if (isPosEq) {
      m_basePosEqs += 1;
    }

    LiteralMiniIndex::InstanceIterator instIt(ixAlts, baseLit, false);

    if (!instIt.hasNext()) {
      // baseLit does not have any suitable alternative at all!
      m_baseLitsWithoutAlts += 1;
      if (isPosEq) {
        m_basePosEqsWithoutAlts += 1;
      }
    }

    ASS(LiteralList::isEmpty(m_alts[i]));
    while (instIt.hasNext()) {
      Literal* matched = instIt.next();
      LiteralList::push(matched, m_alts[i]);
    }
  }
}


SDClauseMatches::~SDClauseMatches()
{
  for (LiteralList* ll : m_alts) {
    LiteralList::destroy(ll);
  }
}


/**
 * Check whether there is a subsumption resolution inference with main premise 'cl'
 * using resolved literal 'resLit' (from 'cl'), and side premise represented by 'cm'.
 */
bool SDHelper::checkForSubsumptionResolution(Clause* cl, SDClauseMatches const& cm, Literal* resLit)
{
  Clause* mcl = cm.base();

  if (cm.baseLitsWithoutAlts() > 0) {
    // Got base literals without alts?
    // Then subsumption resolution is possible,
    // but only if we can resolve ALL of them away
    // (i.e., complementary-match with resLit)
    //
    // NOTE: if there is more than one base literal without alts,
    // subsumption resolution might still be possible
    // (if we can unify them and resolve them all away)
    for (unsigned i = 0; i < mcl->length(); ++i) {
      if (LiteralList::isEmpty(cm.alts()[i])) {
        if (!MatchingUtils::match((*mcl)[i], resLit, /* complementary = */ true)) {
          return false;
        }
      }
    }

  } else {
    // No base literal without alts?
    // Subsumption resolution is possible if at least one base lit can be resolved with resLit

    bool anyResolvable = false;
    for (unsigned i = 0; i < mcl->length(); ++i) {
      if (MatchingUtils::match((*mcl)[i], resLit, /* complementary = */ true)) {
        anyResolvable = true;
        break;
      }
    }
    if (!anyResolvable) {
      return false;
    }
  }

  // NOTE: we use MLMatcher here because we want *subset* inclusion (as opposed to submultiset)
  return MLMatcher::canBeMatched(mcl, cl, cm.alts(), resLit);
}
/**
 * Build clause that results from subsumption resolution with main premise 'cl' and side premise 'mcl'.
 * The literal 'resLit' is the resolved literal from 'cl'.
 */
Clause* SDHelper::generateSubsumptionResolutionClause(Clause* cl, Literal* resLit, Clause* mcl)
{
  CALL("generateSubsumptionResolutionClause");

  unsigned newLen = cl->length() - 1;
  Clause* newCl = new(newLen) Clause(newLen,
      SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, cl, mcl));

  unsigned j = 0;
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* curLit = (*cl)[i];

    if (curLit != resLit) {
      (*newCl)[j] = curLit;
      j += 1;
    }
  }
  // We should have skipped exactly one literal, namely resLit.
  // (it should never appear twice because we apply duplicate literal removal before subsumption resolution)
  ASS_EQ(j, newLen);

  return newCl;
}


#if VDEBUG
/// Returns true iff clause with literal lits1 is smaller than clause with literals lits2
/// in the multiset extension of the given ordering.
///
/// This implementation is justified by Lemma 2.5.6 on page 24 of [BN98].
/// [BN98] Franz Baader and Tobias Nipkow. Term Rewriting and All That. Cambridge University Press, 1998.
SDHelper::ClauseComparisonResult SDHelper::clauseCompare(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering)
{
  // "-lcm reverse" messes up the ordering
  ASS(env.options->literalComparisonMode() != Options::LiteralComparisonMode::REVERSE);

  // Copy given literals so we can sort them
  vvector<Literal*> c1(lits1, lits1+n1);
  vvector<Literal*> c2(lits2, lits2+n2);

  // These will contain literals from c1/c2 with equal occurrences removed
  vvector<Literal*> v1;
  vvector<Literal*> v2;

  // The equality tests below only make sense for shared literals
  std::for_each(c1.begin(), c1.end(), [](Literal* lit) { ASS(lit->shared()); });
  std::for_each(c2.begin(), c2.end(), [](Literal* lit) { ASS(lit->shared()); });

  // Sort input by pointer value
  // NOTE: we use std::less<> because the C++ standard guarantees it is a total order on pointer types.
  //       (the built-in operator< is not required to be a total order for pointer types.)
  std::less<Literal*> const lit_ptr_less {};
  std::sort(c1.begin(), c1.end(), lit_ptr_less);
  std::sort(c2.begin(), c2.end(), lit_ptr_less);

  // Skip occurrences of equal literals
  unsigned i1 = 0;
  unsigned i2 = 0;
  while (i1 < n1 && i2 < n2) {
    if (c1[i1] == c2[i2]) {
      // skip this occurrence
      ++i1;
      ++i2;
    }
    else if (lit_ptr_less(c1[i1], c2[i2])) {
      v1.push_back(c1[i1]);
      ++i1;
    }
    else if (lit_ptr_less(c2[i2], c1[i1])) {
      v2.push_back(c2[i2]);
      ++i2;
    }
    else {
      ASSERTION_VIOLATION;
    }
  }
  while (i1 < n1) {
    ASS_GE(i2, n2);
    v1.push_back(c1[i1]);
    ++i1;
  }
  while (i2 < n2) {
    ASS_GE(i1, n1);
    v2.push_back(c2[i2]);
    ++i2;
  }

  if (v1.empty() && v2.empty()) {
    // Both clauses are the same
    ASS(c1 == c2);
    return ClauseComparisonResult::Equal;
  }

  // For each remaining literal from c1,
  // we have to find a greater one in the remaining ones from c2.
  for (Literal* l1 : v1) {
    bool isCovered = false;
    for (Literal* l2 : v2) {
      switch (ordering.compare(l1, l2)) {
        case Ordering::LESS:
          // yay
          isCovered = true;
          break;
        case Ordering::INCOMPARABLE:
        case Ordering::GREATER:
          // doesn't work
          break;
        case Ordering::EQUAL:
          // should not happen due to first part where we remove equal literals
          ASSERTION_VIOLATION;
        case Ordering::LESS_EQ:
        case Ordering::GREATER_EQ:
          // those don't appear
          ASSERTION_VIOLATION;
        default:
          ASSERTION_VIOLATION;
      }
      if (isCovered) {
        break;
      }
    }
    if (!isCovered) {
      return ClauseComparisonResult::GreaterOrIncomparable;
    }
  }

  return ClauseComparisonResult::Smaller;
}
#endif  // VDEBUG


}  // namespace Inferences

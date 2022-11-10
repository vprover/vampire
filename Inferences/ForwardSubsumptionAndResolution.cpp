/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.htmlmatch2.
 * and in the source directory
 */
/**
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution. The oracle is used to ensure consistent
 * branching in the forward subsumption and resolution inference.
 */

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "Inferences/ForwardSubsumptionAndResolution.hpp"

namespace Inferences {
using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution(bool subsumptionResolution)
    : _subsumptionResolution(subsumptionResolution)
{
  CALL("ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution");
}

ForwardSubsumptionAndResolution::~ForwardSubsumptionAndResolution()
{
}

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  CALL("ForwardSubsumptionAndResolution::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("ForwardSubsumptionAndResolution::detach");
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

/**
 * @brief Creates a clause that is the subsumption resolution of @b cl and @b baseClause on @b lit.
 * L V L' /\ M V m'
 * @param cl The clause to be subsumed.
 * @param lit The literal on which the subsumption resolution is performed.
 * @param baseClause The.
 */
Clause *ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(Clause *cl, Literal *lit, Clause *baseClause)
{
  CALL("ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause");
  int clen = cl->length();
  int nlen = clen - 1;

  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, cl, baseClause));

  int next = 0;
  bool found = false;
  for (int i = 0; i < clen; i++) {
    Literal *curr = (*cl)[i];
    // As we will apply subsumption resolution after duplicate literal
    // deletion, the same literal should never occur twice.
    ASS(curr != lit || !found);
    if (curr != lit || found) {
      (*res)[next++] = curr;
    }
    else {
      found = true;
    }
  }
  ASS_EQ(next, nlen)

  return res;
}

/**
 * Creates a clause whose literals are the literals of @b cl except for the literal in @b litToExclude
 * @param cl the clause whose literals are to be copied
 * @param litToExclude the literal to exclude
 * @return the new clause
 *
 * @pre Assumes that the literals in @b litToExclude are in the same order as in cl
 */
static Clause *generateNSimplificationClause(Clause *cl, vvector<Literal *> litToExclude, Stack<Unit *> premises)
{
  CALL("generateNSimplificationClause");
  unsigned nlen = cl->length() - litToExclude.size();
  // convert premises into a list of units
  UnitList *premList = UnitList::singleton(cl);
  UnitList::pushFromIterator(Stack<Unit *>::Iterator(premises), premList);
  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInferenceMany(InferenceRule::SUBSUMPTION_RESOLUTION, premList));
  unsigned j = 0;
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    if (j < litToExclude.size() && lit == litToExclude[j]) {
      j++;
      continue;
    }
    (*res)[i - j] = lit;
  }
  return res;
}

/**
 * Checks whether the clause @b cl can be subsumed or resolved and subsumed by any clause is @b premises .
 * If the clause is subsumed, returns true
 * If the clause is resolved and subsumed, returns true and sets @b replacement to the conclusion clause
 * If the clause is not subsumed or resolved and subsumed, returns false
 *
 * @param cl the clause to check
 * @param replacement the replacement clause if the clause is resolved and subsumed
 * @param premises the premise that successfully subsumed or resolved and subsumed @b cl
 * @return true if the clause is subsumed or resolved and subsumed, false otherwise
 */
bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");
  TIME_TRACE("forward subsumption");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  /// @brief Set to true if the clause is subsumed by one of the clauses in the unit or forward index
  bool subsumes = false;
  /// @brief Conclusion of the subsumption resolution if successful
  Clause *conclusion = nullptr;
  /// @brief Premise of either subsumption or subsumption resolution
  Clause *premise = nullptr;

  /// @brief Set of clauses that were already checked
  static DHSet<Clause *> checkedClauses;
  checkedClauses.reset();

  Clause *mcl;

  /// @brief List of premises involved in a chained subsumption resolution
  static Stack<Unit *> premiseStack;
  /// @brief List of literals that will be removed after a chained subsumption resolution
  static vvector<Literal *> litToExclude;

  /*******************************************************/
  /*              SUBSUMPTION UNIT CLAUSE                */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption since
  // L = a where a is a single literal
  // M = b v C where sigma(a) = b is a given from the index
  // Therefore L subsumes M
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, false, false);
    if (it.hasNext()) {
      mcl = it.next().clause;
      subsumes = true;
      premise = mcl;
      goto end_forward;
    }
  }

  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  // For each clauses mcl, first check for subsumption, then for subsumption resolution
  // During subsumption, setup the subsumption resolution solver. This is an overhead
  // largely compensated because the success rate of subsumption is fairly low, and
  // in case of failure, having the solver ready is a great saving on subsumption resolution
  //
  // Since subsumption is stronger than subsumption, if a subsumption resolution check is found,
  // keep it until the end of the loop to make sure no subsumption is possible.
  // Only when it has been checked that subsumption is not possible does the conclusion of
  // subsumption resolution become relevant
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!checkedClauses.insert(mcl)) {
        continue;
      }

      bool checkSR = _subsumptionResolution && !conclusion;
      // if mcl is longer than cl, then it cannot subsume cl but still could be resolved
      bool checkS = mcl->length() <= clen;
      if (checkS) {
        if (satSubs.checkSubsumption(mcl, cl, checkSR)) {
          subsumes = true;
          premise = mcl;
          goto end_forward;
        }
      }
      if (checkSR) {
        // In this case, the literals come from the non complementary list, and there is therefore
        // a low chance of it being resolved. However, in the case where there is no negative match,
        // checkSubsumption resolution is very fast after subsumption, since filling the match set
        // for subsumption will have already detected that subsumption resolution is impossible
        conclusion = satSubs.checkSubsumptionResolution(mcl, cl, checkS);
        if (conclusion) {
          ASS(premise == nullptr);
          // cannot override the premise since the loop would have ended otherwise
          // the premise will be overriden if a subsumption is found
          premise = mcl;
        }
      }
    }
  }

  if (conclusion || !_subsumptionResolution) {
    goto end_forward;
  }

  /*******************************************************/
  /*         SUBSUMPTION RESOLUTION UNIT CLAUSE          */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption resolution since
  // L = a where a is a single literal
  // M = ~b v C where sigma(a) = ~b is a given from the index
  // Therefore M can be replaced by C
  //
  // This behavior can be chained and several resolution can happen at the same time
  // The negatively matching literals are stacked and removed at the same time
  premiseStack.reset();
  litToExclude.clear();
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, true, false);
    if (it.hasNext()) {
      mcl = it.next().clause;
      premiseStack.push(mcl);
      litToExclude.push_back(lit);
      // No need to loop because it is known that the literal lit will be simplified
    }
  }
  if (premiseStack.size() == 1) {
    // Single simplification, nothing fancy about it
    premise = (Clause *)premiseStack.pop();
    conclusion = generateSubsumptionResolutionClause(cl, litToExclude[0], premise);
    goto end_forward;
  }
  else if (premiseStack.size() > 1) {
    // Simplify several literals at the same time
    conclusion = generateNSimplificationClause(cl, litToExclude, premiseStack);
    // Setting premise to null is used to check whether the conclusion has several premises
    premise = nullptr;
    goto end_forward;
  }

  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  // Check for the last clauses that are negatively matched in th index.
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!checkedClauses.insert(mcl)) {
        continue;
      }

      conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      if (conclusion) {
        ASS(premise == nullptr);
        premise = mcl;
        goto end_forward;
      }
    }
  }

/*******************************************************/
/*                   ANALYZE RESULT                    */
/*******************************************************/
end_forward:
  if (subsumes) {
    premises = pvi(getSingletonIterator(premise));
    return true;
  }
  if (conclusion) {
    replacement = conclusion;
    if (!premise) {
      ASS(premiseStack.size() > 1);
      ClauseList *premiseList = ClauseList::empty();
      for (unsigned i = 0; i < premiseStack.size(); i++) {
        ClauseList::push((Clause *)premiseStack[i], premiseList);
      }
      premises = pvi(ClauseList::Iterator(premiseList));
      return true;
    }
    premises = pvi(getSingletonIterator(premise));
    return true;
  }
  return false;
}

} // namespace Inferences
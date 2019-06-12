
/*
 * File HintsForAvatarFakeSimplifier.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file HintsForAvatarFakeSimplifier.cpp
 * Implements class HintsForAvatarFakeSimplifier.
 */

#include "HintsForAvatarFakeSimplifier.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/Clause.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

namespace Inferences
{

HintsForAvatarFakeSimplifier::HintsForAvatarFakeSimplifier() : _impl(false)
{
  CALL("HintsForAvatarFakeSimplifier::HintsForAvatarFakeSimplifier");

  // create indices for _impl and connect them with container!

  UnitClauseLiteralIndex* unitIdx =
      new UnitClauseLiteralIndex(new LiteralSubstitutionTree());

  FwSubsSimplifyingLiteralIndex* fwIdx =
      new FwSubsSimplifyingLiteralIndex(new LiteralSubstitutionTree());

  unitIdx->attachContainer(&_hintClauseContainer);
  fwIdx->attachContainer(&_hintClauseContainer);

  _impl.setIndices(unitIdx,fwIdx);
}

Clause* HintsForAvatarFakeSimplifier::simplify(Clause* cl)
{
  CALL("HintsForAvatarFakeSimplifier::simplify");

  Clause* rDummy;
  Clause* pDummy;
  // never consider redundant, just mark as "hint-heeding"
  if (_impl.genericPerform(cl,rDummy,pDummy,TC_FORWARD_SUBSUMPTION_HINT_CHECK,TC_FORWARD_SUBSUMPTION_HINT_CHECK)) {
    cl->heedHint();
  }
  return cl;
}

}

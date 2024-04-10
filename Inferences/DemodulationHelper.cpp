/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Indexing/ResultSubstitution.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Options.hpp"

#include "DemodulationHelper.hpp"

namespace Inferences {

using namespace Kernel;

DemodulationHelper::DemodulationHelper(const Options& opts, const Ordering* ord)
: _redundancyCheck(opts.demodulationRedundancyCheck() != Options::DemodulationRedundancyCheck::OFF),
  _encompassing(opts.demodulationRedundancyCheck() == Options::DemodulationRedundancyCheck::ENCOMPASS),
  _ord(ord)
{
}

bool DemodulationHelper::redundancyCheckNeededForPremise(Clause* rwCl, Literal* rwLit, TermList rwTerm) const
{
  if (!rwLit->isEquality() || (rwTerm!=*rwLit->nthArgument(0) && rwTerm!=*rwLit->nthArgument(1))) {
    return false;
  }

  // check is needed if encompassment demodulation is off or we demodulate a positive unit
  return !_encompassing || (rwLit->isPositive() && (rwCl->length() == 1));
}

bool DemodulationHelper::isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm,
  TermList tgtTerm, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult) const
{
  ASS(redundancyCheckNeededForPremise(rwCl, rwLit, rwTerm));

  TermList other=EqHelper::getOtherEqualitySide(rwLit, rwTerm);
  Ordering::Result tord = _ord->compare(tgtTerm, other);
  if (tord == Ordering::LESS || tord == Ordering::LESS_EQ) {
    return true;
  }

  if (_encompassing) {
    // under _encompassing, we know there are no other literals in rwCl
    return !subst->isRenamingOn(eqLHS,eqIsResult);
  }

  TermList eqSort = SortHelper::getEqualityArgumentSort(rwLit);
  Literal* eqLitS=Literal::createEquality(true, rwTerm, tgtTerm, eqSort);

  // The demodulation which does not preserve completeness:
  // s = t     s = t1 \/ C
  // ---------------------
  //      t = t1 \/ C
  // where t > t1 and s = t > C.
  //
  // Hence we need to check if there are any literals
  // in rwCl greater than eqLitS.
  return rwCl->iterLits().any([rwLit,this,eqLitS](Literal* lit) {
    return lit != rwLit && _ord->compare(eqLitS, lit)==Ordering::LESS;
  });
}

}  // namespace Inferences

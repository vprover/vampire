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
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Ordering.hpp"

#include "Shell/Options.hpp"

#include "DemodulationHelper.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

DemodulationHelper::DemodulationHelper(const Options& opts, const Ordering* ord)
: _redundancyCheck(opts.demodulationRedundancyCheck() != Options::DemodulationRedundancyCheck::OFF),
  _encompassing(opts.demodulationRedundancyCheck() == Options::DemodulationRedundancyCheck::ENCOMPASS),
  _ord(ord)
{
}

bool DemodulationHelper::redundancyCheckNeededForPremise(Clause* rwCl, Literal* rwLit, TermList rwTerm) const
{
  if (!_redundancyCheck) {
    return false;
  }

  if (!rwLit->isEquality() || (rwTerm!=*rwLit->nthArgument(0) && rwTerm!=*rwLit->nthArgument(1))) {
    return false;
  }

  // check is needed if encompassment demodulation is off or we demodulate a positive unit
  return !_encompassing || (rwLit->isPositive() && (rwCl->length() == 1));
}

/**
 * Test whether the @param applicator is a renaming on the variables of @param t.
 */
bool isRenamingOn(const SubstApplicator* applicator, TermList t)
{
  DHSet<TermList> renamingDomain;
  DHSet<TermList> renamingRange;

  VariableIterator it(t);
  while(it.hasNext()) {
    TermList v = it.next();
    ASS(v.isVar());
    if (!renamingDomain.insert(v)) {
      continue;
    }

    TermList vSubst = (*applicator)(v.var());
    if (!vSubst.isVar()) {
      return false;
    }
    if (!renamingRange.insert(vSubst)) {
      return false;
    }
  }
  return true;
}

bool DemodulationHelper::isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm,
  TermList tgtTerm, TermList eqLHS, const SubstApplicator* eqApplicator) const
{
  Ordering::Result temp;
  return isPremiseRedundant(rwCl, rwLit, rwTerm, tgtTerm, eqLHS, eqApplicator, temp);
}

bool DemodulationHelper::isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm,
  TermList tgtTerm, TermList eqLHS, const SubstApplicator* eqApplicator, Ordering::Result& tord) const
{
  ASS(redundancyCheckNeededForPremise(rwCl, rwLit, rwTerm));

  TermList other=EqHelper::getOtherEqualitySide(rwLit, rwTerm);
  tord = _ord->compare(tgtTerm, other);
  if (tord == Ordering::LESS) {
    return true;
  }

  if (_encompassing) {
    // under _encompassing, we know there are no other literals in rwCl
    return !isRenamingOn(eqApplicator,eqLHS);
  }

  // return early to avoid creation of eqLitS
  if (rwCl->length()==1) {
    return false;
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

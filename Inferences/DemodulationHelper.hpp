/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __DemodulationHelper__
#define __DemodulationHelper__

#include "Forwards.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;
using namespace Shell;

class DemodulationHelper {
public:
  DemodulationHelper() = default;
  DemodulationHelper(const Options& opts, const Ordering* ord);

  bool redundancyCheckNeededForPremise(Clause* rwCl, Literal* rwLit, TermList rwTerm) const;
  bool isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm, TermList tgtTerm,
    TermList eqLHS, const SubstApplicator* applicator) const;
  bool isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm, TermList tgtTerm,
    TermList eqLHS, const SubstApplicator* applicator, Ordering::Result& tord) const;

private:
  bool _redundancyCheck;
  bool _encompassing;
  const Ordering* _ord;
};

};

#endif /* !__DemodulationHelper__ */

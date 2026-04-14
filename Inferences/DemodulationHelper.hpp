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
#include "Lib/DHSet.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;
using namespace Shell;

class DemodulationHelper {
public:
  DemodulationHelper() = default;
  DemodulationHelper(const Options& opts, const Ordering* ord);

  template<typename Object>
  static bool isRenamingOn(const SubstApplicator* applicator, Object obj) {
    DHSet<unsigned> domain;
    DHSet<unsigned> range;
    return isRenamingOn(applicator, obj, domain, range);
  }
  template<typename Object>
  static bool isRenamingOn(const SubstApplicator* applicator, Object obj, DHSet<unsigned>& domain, DHSet<unsigned>& range)
  {
    for (const auto& v : iterTraits(VariableIterator(obj))) {
      ASS(v.isVar());
      if (!domain.insert(v.var())) {
        continue;
      }

      TermList vSubst = (*applicator)(v.var());
      if (!vSubst.isVar() || !range.insert(vSubst.var())) {
        return false;
      }
    }
    return true;
  }

  bool redundancyCheckNeededForPremise(Clause* rwCl, Literal* rwLit, TermList rwTerm) const;
  bool isPremiseRedundant(Clause* rwCl, Literal* rwLit, TermList rwTerm, TermList tgtTerm,
    TermList eqLHS, const SubstApplicator* applicator) const;

private:
  bool _redundancyCheck;
  bool _encompassing;
  const Ordering* _ord;
};

};

#endif /* !__DemodulationHelper__ */

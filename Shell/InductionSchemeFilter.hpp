/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InductionSchemeFilter.hpp
 * Defines helper classes for induction and recursive functions
 */

#ifndef __InductionSchemeFilter__
#define __InductionSchemeFilter__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "InductionSchemeGenerator.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

/**
 * This class instantiates the induction templates from a literal
 * we want to induct on. Afterwards, stores these and filters them.
 * Also stores all active occurrences of possible induction terms.
 */
struct InductionSchemeFilter {
  void filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& primary,
    vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& secondary);
  void filterComplex(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes,
    DHMap<Literal*, DHMap<TermList, unsigned>*>* currOccMaps);

private:
  void filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes);

  bool mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res);
  bool checkSubsumption(const InductionScheme& sch1, const InductionScheme& sch2);
};

} // Shell

#endif

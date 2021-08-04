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
  void filter(vvector<InductionScheme>& schemes, const OccurrenceMap& actOccMaps);

private:
  void filterComplex(vvector<InductionScheme>& schemes, const OccurrenceMap& occMap);
  bool checkContainment(const InductionScheme& sch1, const InductionScheme& sch2);
};

} // Shell

#endif

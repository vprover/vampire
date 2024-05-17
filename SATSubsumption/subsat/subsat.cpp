/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "./subsat.hpp"


// TODO: move solver implementation here


std::ostream& subsat::print_config(std::ostream& os)
{
    os << "subsat features:";
    if (SUBSAT_STANDALONE) { os << " STANDALONE"; }
    if (VDEBUG) { os << " DEBUG"; }
    if (SUBSAT_LOGGING_ENABLED) { os << " LOG"; }
    if (SUBSAT_RESTART) { os << " RESTART(" << SUBSAT_RESTART_INTERVAL << ")"; }
    if (SUBSAT_MINIMIZE) { os << " MINIMIZE"; }
    if (SUBSAT_BLOCKING) { os << " BLOCKING"; }
    if (SUBSAT_VIRTUAL) { os << " VIRTUAL"; }
    if (SUBSAT_VDOM) { os << " VDOM"; }
    if (SUBSAT_VMTF) { os << " VMTF"; }
    if (SUBSAT_VMTF_BUMP) { os << " VMTF_BUMP"; }
    if (SUBSAT_PHASE_SAVING) { os << " PHASE_SAVING"; }
    if (SUBSAT_STATISTICS) {
        os << " STATISTICS(level " << SUBSAT_STATISTICS;
#if defined(SUBSAT_STATISTICS_INTERVAL)
        os << ", interval " << SUBSAT_STATISTICS_INTERVAL;
#endif
        os << ")";
    }
    if (SUBSAT_LIMITS) { os << " LIMITS"; }
    if (VDEBUG && SUBSAT_EXPENSIVE_ASSERTIONS) { os << " EXPENSIVE_ASSERTIONS"; }
    os << '\n';
    return os;
}

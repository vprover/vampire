#ifndef SUBSAT_CONFIG_HPP
#define SUBSAT_CONFIG_HPP


// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(VDEBUG == 0, "VDEBUG and NDEBUG are not synchronized");
#else
static_assert(VDEBUG == 1, "VDEBUG and NDEBUG are not synchronized");
#endif

#ifndef SUBSAT_STANDALONE
#define SUBSAT_STANDALONE 0
#endif

// By default, enable logging only in debug mode
#ifndef SUBSAT_LOGGING_ENABLED
#   ifndef NDEBUG
#       define SUBSAT_LOGGING_ENABLED 1
#   else
#       define SUBSAT_LOGGING_ENABLED 0
#   endif
#endif

// Clause learning
// ASSESSMENT: important
// TODO: also try limiting the amount of memory that can be used for learning... once the limit is reached, only learn units and maybe binary clauses.
#ifndef SUBSAT_LEARN
#define SUBSAT_LEARN 1
#endif

// Restarting
// Very simple heuristic: restart every fixed number of conflicts.
// ASSESSMENT: doesn't seem to help with subsumption instances.
#ifndef SUBSAT_RESTART
#define SUBSAT_RESTART 0
#define SUBSAT_RESTART_INTERVAL 100
#endif

// Conflict clause minimization
// ASSESSMENT: doesn't seem to help much with subsumption instances.
#ifndef SUBSAT_MINIMIZE
#define SUBSAT_MINIMIZE 0
#endif

// VDOM (variable domain size) decision heuristic
// ASSESSMENT: extremely valuable for hard subsumption instances!
#ifndef SUBSAT_VDOM
#define SUBSAT_VDOM 1
#endif

// VMTF (variable move to front) decision heuristic
// If both VDOM and VMTF are enabled, then VMTF is used as fallback (only useful if there are variables without an assigned group).
// ASSESSMENT: can be removed for subsumption instances since all variables will be assigned to a group.
#ifndef SUBSAT_VMTF
#if SUBSAT_STANDALONE
#define SUBSAT_VMTF 1
#else
#define SUBSAT_VMTF 0
#endif
#endif

// Variable bumping (to update the decision heuristic)
// Disable this gives us a static variable order
// TODO: implement and test this option (together with restarts)
#ifndef SUBSAT_VMTF_BUMP
#define SUBSAT_VMTF_BUMP 1
#endif

#if !SUBSAT_VDOM && !SUBSAT_VMTF
#error "At least one decision heuristic must be enabled!"
#endif

#if SUBSAT_STANDALONE && !SUBSAT_VMTF
#error "Pure SAT problems need VMTF (or another pure SAT heuristic) as fallback!"
#endif

// Phase saving
// CONJECTURE: probably not very helpful; always choosing true should be fine for our use case.
// TODO: maybe implement and test
#ifndef SUBSAT_PHASE_SAVING
#define SUBSAT_PHASE_SAVING 0
#endif

// By default, statistics are only enabled in standalone mode or if logging is enabled
#if SUBSAT_STANDALONE || SUBSAT_LOGGING_ENABLED
#define SUBSAT_STATISTICS 1
#else
#define SUBSAT_STATISTICS 0
#endif

// If SUBSAT_STATISTICS_INTERVAL is set, print statistics periodically
// (interval is measured in number of loop iterations)
#if SUBSAT_STATISTICS && !defined(SUBSAT_STATISTICS_INTERVAL)
#define SUBSAT_STATISTICS_INTERVAL (VDEBUG ? 500 : 5000)
#endif

// TODO: disable this by default in Vampire mode (to not slow down vampire's debug mode too much),
//       but only when this is ready to merge.
#define SUBSAT_EXPENSIVE_ASSERTIONS 1


#include <ostream>
static void subsat_print_config(std::ostream& os)
{
    os << "Features:";
    if (SUBSAT_STANDALONE) { os << " STANDALONE"; }
    if (VDEBUG) { os << " DEBUG"; }
    if (SUBSAT_LOGGING_ENABLED) { os << " LOG"; }
    if (SUBSAT_LEARN) { os << " LEARN"; }
    if (SUBSAT_RESTART) { os << " RESTART(" << SUBSAT_RESTART_INTERVAL << ")"; }
    if (SUBSAT_MINIMIZE) { os << " MINIMIZE"; }
    if (SUBSAT_VDOM) { os << " VDOM"; }
    if (SUBSAT_VMTF) { os << " VMTF"; }
    if (SUBSAT_PHASE_SAVING) { os << " PHASE_SAVING"; }
    if (SUBSAT_STATISTICS) { os << " STATS"; }
    if (VDEBUG && SUBSAT_EXPENSIVE_ASSERTIONS) { os << " EXPENSIVE_ASSERTIONS"; }
    os << '\n';
}


#endif /* !SUBSAT_CONFIG_HPP */

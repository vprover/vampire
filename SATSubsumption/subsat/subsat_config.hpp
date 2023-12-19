#ifndef SUBSAT_CONFIG_HPP
#define SUBSAT_CONFIG_HPP


// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(VDEBUG == 0, "VDEBUG and NDEBUG are not synchronized");
#else
static_assert(VDEBUG == 1, "VDEBUG and NDEBUG are not synchronized");
#endif


/***********************************************************************
 * Operation mode: stand-alone binary or embedded in Vampire
 ***********************************************************************/

#ifndef SUBSAT_STANDALONE
#define SUBSAT_STANDALONE 0
#endif


/***********************************************************************
 * Debugging features
 ***********************************************************************/

// By default, enable logging only in debug mode
#ifndef SUBSAT_LOGGING_ENABLED
#   ifndef NDEBUG
#       define SUBSAT_LOGGING_ENABLED 0
#   else
#       define SUBSAT_LOGGING_ENABLED 0
#   endif
#endif

// By default, statistics are only enabled in standalone mode or if logging is enabled
#if SUBSAT_STANDALONE || SUBSAT_LOGGING_ENABLED
#define SUBSAT_STATISTICS 2
#else
#define SUBSAT_STATISTICS 1
#endif

// If SUBSAT_STATISTICS_INTERVAL is set, print statistics periodically
// (interval is measured in number of loop iterations)
#if SUBSAT_STATISTICS >= 2 && !defined(SUBSAT_STATISTICS_INTERVAL)
#define SUBSAT_STATISTICS_INTERVAL (VDEBUG ? 500 : 5000)
#endif

// Allow setting resource limits on solving
#ifndef SUBSAT_LIMITS
#define SUBSAT_LIMITS 1
#endif

// TODO: disable this by default in Vampire mode (to not slow down vampire's debug mode too much),
//       but only when this is ready to merge.
#define SUBSAT_EXPENSIVE_ASSERTIONS 1


/***********************************************************************
 * Solving features
 ***********************************************************************/

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

// Blocking literal optimization
// Stores the other watched literal in the watch lists, saves some dereferencing during solving at the cost of increased watch size.
#ifndef SUBSAT_BLOCKING
#define SUBSAT_BLOCKING 0
#endif
#if SUBSAT_BLOCKING
#error "SUBSAT_BLOCKING not yet implemented"
#endif

// Binary clauses are 'virtual', meaning they're embedded in the watchlists and not stored at all outside.
// Requires SUBSAT_BLOCKING.
#ifndef SUBSAT_VIRTUAL
#define SUBSAT_VIRTUAL 0
#endif
#if SUBSAT_VIRTUAL
#error "SUBSAT_VIRTUAL not yet implemented"
#endif

#if SUBSAT_VIRTUAL && !SUBSAT_BLOCKING
#error "SUBSAT_VIRTUAL requires SUBSAT_BLOCKING"
#endif

// VDOM (variable domain size) decision heuristic
// ASSESSMENT: extremely valuable for hard subsumption instances!
#ifndef SUBSAT_VDOM
#define SUBSAT_VDOM 0
#endif

// VMTF (variable move to front) decision heuristic
// If both VDOM and VMTF are enabled, then VMTF is used as fallback (only useful if there are variables without an assigned group).
// ASSESSMENT: can be removed for subsumption instances since all variables will be assigned to a group.
#ifndef SUBSAT_VMTF
#if SUBSAT_STANDALONE
#define SUBSAT_VMTF 1
#else
#define SUBSAT_VMTF 1
#endif
#endif

// Variable bumping (to update the decision heuristic)
// Disabling this gives us a static variable order
// TODO: implement and test this option (together with restarts)
#ifndef SUBSAT_VMTF_BUMP
#define SUBSAT_VMTF_BUMP 1
#endif
#if !SUBSAT_VMTF_BUMP
#error "Disabling SUBSAT_VMTF_BUMP is not yet implemented!"
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

// Simplify clauses before solving
#ifndef SUBSAT_SIMPLIFY_CLAUSES
#define SUBSAT_SIMPLIFY_CLAUSES 1
#endif

// Simplify AtMostOne constraints before solving
#ifndef SUBSAT_SIMPLIFY_AMOS
#define SUBSAT_SIMPLIFY_AMOS 1
#endif


#endif /* !SUBSAT_CONFIG_HPP */

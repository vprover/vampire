/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef SUBSAT_CONFIG_HPP
#define SUBSAT_CONFIG_HPP


// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(VDEBUG == 0, "VDEBUG and NDEBUG are not synchronized");
#else
static_assert(VDEBUG == 1, "VDEBUG and NDEBUG are not synchronized");
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

// By default, statistics are only enabled if logging is enabled
#if SUBSAT_LOGGING_ENABLED
#define SUBSAT_STATISTICS 2
#else
#define SUBSAT_STATISTICS 0
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

// Enables additional (expensive) sanity checks within the SAT solver
#define SUBSAT_EXPENSIVE_ASSERTIONS 0


/***********************************************************************
 * Solving features
 ***********************************************************************/

// Restarting
// Very simple heuristic: restart every fixed number of conflicts.
// ASSESSMENT: doesn't seem to help with subsumption instances.
#ifndef SUBSAT_RESTART
#define SUBSAT_RESTART 0
#define SUBSAT_RESTART_INTERVAL 100
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
#define SUBSAT_VMTF 1
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

#if !SUBSAT_VMTF
#error "Pure SAT problems need VMTF (or another pure SAT heuristic) as fallback!"
#endif


#endif /* !SUBSAT_CONFIG_HPP */

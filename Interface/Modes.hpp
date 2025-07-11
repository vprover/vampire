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
 *  @file Modes.hpp
 *  Defines function dispatchByMode
 *  @since 11/07/2025
 */

#ifndef __Modes__
#define __Modes__

#include <ostream>

#include "Kernel/Problem.hpp"

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interrupted (e.g. SIGINT, SIGHUP), value VAMP_RESULT_STATUS_INTERRUPTED is returned,
 * and in case of other signal we return VAMP_RESULT_STATUS_OTHER_SIGNAL. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case of an unhandled exception or user error, we return value
 * VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION.
 *
 * In case Vampire was terminated by the timer, return value is
 * uncertain (but definitely not zero), probably it will be 134
 * (we terminate by a call to the @b abort() function in this case).
 */
extern int vampireReturnValue;

void dispatchByMode(Kernel::Problem* problem, std::ostream& out);

#endif /* __Modes__ */

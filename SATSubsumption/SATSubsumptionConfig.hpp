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
 * @file SATSubsumptionConfig.hpp
 * Defines a set of options for benchmarking subsumption resolution
 */
#ifndef SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_
#define SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_


/*****************************************************************************/
/*                          SATURATION ALGORITHM                             */
/*****************************************************************************/
/// If 1 then use the new implementation of backward subsumption and resolution
/// instead of the two old separate implementations
#define USE_NEW_SUBSUMPTION_AND_RESOLUTION_BACKWARD 1

/// If 1, then use the wrapped forward subsumption and resolution to measure
/// the time spent in the forward subsumption and resolution
#ifndef USE_WRAPPED_FORWARD_SUBSUMPTION_AND_RESOLUTION
#define USE_WRAPPED_FORWARD_SUBSUMPTION_AND_RESOLUTION 1
#endif

/// If 1, then print in file the time spent in subsumption resolution
/// and the length of the clauses
#ifndef CORRELATE_LENGTH_TIME
#define CORRELATE_LENGTH_TIME 1
#endif

/*****************************************************************************/
/*                          SUBSUMPTION RESOLUTION                           */
/*****************************************************************************/
/// Encoding of the problem
/// 1 : Using c_j <=> (b_0j- V ... V b_nj-)
/// 2 : Without c_j
/// This options should be defined in the cMakeList.txt file
#ifndef SAT_SR_IMPL
#define SAT_SR_IMPL 3
#endif
/// If 1, prints the clauses added to the solver on the standard output
#define PRINT_CLAUSES_SUBS 0
/// If 1, prints some comments about the subsumption resolution process
#define PRINT_CLAUSE_COMMENTS_SUBS 0


/*****************************************************************************/
/*                 FORWARD SUBSUMPTION AND RESOLUTION                        */
/*****************************************************************************/
#if VDEBUG
/// If 1, check the correctness of the forward subsumption by comparing the result
/// with the old implementation
#define CHECK_SAT_SUBSUMPTION 1
/// If 1, check the correctness of the forward subsumption resolution by comparing
/// the result with the old implementation
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 1
#else
/// If 1, check the correctness of the forward subsumption by comparing the result
/// with the old implementation
#define CHECK_SAT_SUBSUMPTION 0
/// If 1, check the correctness of the forward subsumption resolution by comparing
/// the result with the old implementation
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 0
#endif

/// If 1, use the best implementation of the forward subsumption
#ifndef USE_OPTIMIZED_FORWARD
#define USE_OPTIMIZED_FORWARD 1
#endif

/// If 1, then use the optimized forward subsumption
#if USE_OPTIMIZED_FORWARD
#endif

/*****************************************************************************/
/*                 BACKWARD SUBSUMPTION AND RESOLUTION                       */
/*****************************************************************************/
#if VDEBUG
/// If 1, check the correctness of the backward subsumption and resolution by comparing
/// the result with the old implementation
#define CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION 0
#else
/// If 1, check the correctness of the backward subsumption and resolution by comparing
#define CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION 0
#endif

/// If 1, then use the sat subsumption for backward subsumption
/// If 0, then use the old implementation
#define USE_SAT_SUBSUMPTION_BACKWARD 1
/// If 1, then use the sat subsumption for backward subsumption resolution
/// If 0, then use the old implementation
#define USE_SAT_SUBSUMPTION_RESOLUTION_BACKWARD 1

/// If 1, then use the unoptimized loop with sat subsumption for backward subsumption
/// If 0, then use the optimized loop with sat subsumption for backward subsumption
#define SEPARATE_LOOPS_BACKWARD 0


#endif /* SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_ */

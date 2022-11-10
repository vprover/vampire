#ifndef SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_
#define SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_

/*****************************************************************************/
/*                          SUBSUMPTION RESOLUTION                           */
/*****************************************************************************/
/// @todo TODO : remove that when the real VTEST flag is added
#define VTEST
/// Encoding of the problem
/// 1 : Using c_j <=> (b_0j- V ... V b_nj-)
/// 2 : Without c_j
#define SAT_SR_IMPL 2
/// If 1, writes all the matches to a file
#define WRITE_LITERAL_MATCHES_FILE 0
/// If 1, prints the clauses added to the solver on the standard output
#define PRINT_CLAUSES_SUBS 0
/// If 1, prints some comments about the subsumption resolution process
#define PRINT_CLAUSE_COMMENTS_SUBS 0


/*****************************************************************************/
/*                 FORWARD SUBSUMPTION AND RESOLUTION                        */
/*****************************************************************************/
/// If 1, then the unit clauses in the forward subsumption resolution are combined
/// leading to further simplifications
#define CHAIN_RESOLUTION 1
/// If 1, then the forward subsumption will store the instances of subsumption and
/// resolution in the a file
#define LOG_S_AND_R_INSTANCES 0

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

/// If 1, then use the sat subsumption for forward subsumption
/// If 0, then use the old implementation
#define USE_SAT_SUBSUMPTION_FORWARD 1
/// If 1, then use the sat subsumption for forward subsumption resolution
/// If 0, then use the old implementation
#define USE_SAT_SUBSUMPTION_RESOLUTION_BACKWARD 1

/// If 1, then use the unoptimized loop with sat subsumption for forward subsumption
/// If 0, then use the optimized loop with sat subsumption for forward subsumption
#define SEPARATE_LOOPS_FORWARD 0

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

/*****************************************************************************/
/*                          SATURATION ALGORITHM                             */
/*****************************************************************************/
/// If 1 then use the new implementation of backward subsumption and resolution
/// instead of the two old separate implementations
#define USE_NEW_SUBSUMPTION_AND_RESOLUTION_BACKWARD 1

/// If 1, then use the wrapped forward subsumption and resolution to measure
/// the time spent in the forward subsumption and resolution
#define USE_WRAPPED_FORWARD_SUBSUMPTION_AND_RESOLUTION 1

#endif /* SAT_SUBSUMPTION_AND_RESOLUTION_CONFIG_HPP_ */
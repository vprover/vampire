/**
 * @file Config.hpp
 * Defines class Config.
 */


#ifndef __Config__
#define __Config__

/**
 * Determines whether the support of bdd_marking_subsumption
 * is enabled.
 */
#define BDD_MARKING 1


/**
 * Determines, whether COMPIT unification benchmarks are
 * being recorded. If 0, they're not, if 1, rewritable
 * subterm index operations are recorded, if 2,
 * binary resolution index operations are recorder.
 */
#define COMPIT_GENERATOR 0

#if COMPIT_GENERATOR
/**
 * Determines COMPIT version to be used for output.
 * COMPIT version 2 uses binary output and reverse
 * polish notation for terms.
 */
#define COMPIT_VERSION 2

#endif

#endif /* __Config__ */

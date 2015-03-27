/**
 * @file Connective.hpp
 * Defines enum Connective.
 * @since 02/01/2004 Manchester, separated from Formula.hpp to reduce
 *        module dependencies
 */


#ifndef __Connective__
#define __Connective__

namespace Kernel {

/**
 * Names for formula connectives.
 *
 * @warning The order should not be changed. It is essentially used 
 *          in several functions: normalisation and output functions.
 */
enum Connective 
{
  /** atomic formula or literal */
  LITERAL = 0u,
  /** conjunction of any number of formulas */
  AND = 1u,
  /** disjunction of any number of formulas */
  OR = 2u,
  /** implication */
  IMP = 3u,
  /** equivalence */
  IFF = 4u,
  /** excusive or (binary), or negation of equivalence */
  XOR = 5u,
  /** negation */
  NOT = 6u,
  /** quantiffier for all */
  FORALL = 7u,
  /** quantiffier there exists */
  EXISTS = 8u,
  /** let P <- F in G (P is literal, F and G formulas) */
  FORMULA_LET = 9u,
  /** let S <- T in F (S and T are terms, F is formula) */
  TERM_LET = 10u,
  /** constant false */
  FALSE = 11u,
  /** constant true */
  TRUE = 12u,
}; // enum Connective

}

#endif // __Connective__

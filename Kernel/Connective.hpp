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
  /** special case of a formula that is a boolean variable */
  BOOL_TERM = 9u,
  /** constant false */
  FALSE = 10u,
  /** constant true */
  TRUE = 11u,
  /** name for named formula */
  NAME = 12u,
  /** fake connective terminator */
  NOCONN = 13u
}; // enum Connective

}

#endif // __Connective__

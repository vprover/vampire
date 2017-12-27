
/*
 * File PDUtils.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file PDUtils.hpp
 * Defines class PDUtils.
 */

#ifndef __PDUtils__
#define __PDUtils__

#include "Forwards.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Utility functions for handling predicate definitions
 */
class PDUtils {
  /**
   * This is a utility class which should not be instantiated,
   * so we have a private and undefined constructor
   */
  PDUtils() {}
public:

  static bool isDefinitionHead(Literal* l);

  static bool isUnitAtom(FormulaUnit* unit, Formula*& atom);

  static bool isAtomBinaryFormula(FormulaUnit* unit, Connective& con, Formula*& f1, Formula*& f2);
  static bool isAtomEquivalence(FormulaUnit* unit, Formula*& f1, Formula*& f2);
  static bool isAtomEquivalence(FormulaUnit* unit, Literal*& l1, Literal*& l2);

  static bool isPredicateEquivalence(FormulaUnit* u);
  static bool isPredicateEquivalence(FormulaUnit* u, unsigned& pred1, unsigned& pred2);
  static bool isPredicateEquivalence(FormulaUnit* u, Literal*& lit1, Literal*& lit2);
  static bool isPredicateEquivalence(FormulaUnit* u, Formula*& f1, Formula*& f2);

  static void splitDefinition(FormulaUnit* unit, Literal*& lhs, Formula*& rhs);

  static bool hasDefinitionShape(Unit* unit);
  static bool hasDefinitionShape(FormulaUnit* unit);
  static bool hasDefinitionShape(Literal* lhs, Formula* rhs);
};

}

#endif // __PDUtils__

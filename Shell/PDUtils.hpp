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

  static bool isPredicateEquivalence(FormulaUnit* u);
  static bool isPredicateEquivalence(FormulaUnit* u, unsigned& pred1, unsigned& pred2);
  static bool isPredicateEquivalence(FormulaUnit* u, Literal*& lit1, Literal*& lit2);

  static void splitDefinition(FormulaUnit* unit, Literal*& lhs, Formula*& rhs);

  static bool hasDefinitionShape(Unit* unit);
  static bool hasDefinitionShape(FormulaUnit* unit);
  static bool hasDefinitionShape(Literal* lhs, Formula* rhs);
};

}

#endif // __PDUtils__

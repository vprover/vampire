/**
 * @file Rule.hpp
 * Defines class Rule for clauses used as rules
 * @since 13/07/2008 Linz
 */

#ifndef __Rule__
#define __Rule__

#include "Lib/Allocator.hpp"

namespace Kernel {
  class Clause;
  class Literal;
};

using namespace Kernel;

namespace Rule {

/**
 * Class Rule for clauses used as rules.
 * @since 13/07/2008 Linz
 */
class Rule
{
public:
  /** Clause used in this rule */
  const Clause* clause;
  /** Literal in this clause: the head of the rule */
  const Literal* literal;

  CLASS_NAME("Rule");
  USE_ALLOCATOR(Rule);
}; // class Rule

}

#endif

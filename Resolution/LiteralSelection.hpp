/**
 * @file LiteralSelection.hpp
 * Defines class LiteralSelection implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelection__
#define __LiteralSelection__

namespace Kernel {
  class Clause;
  class Literal;
}

using namespace Kernel;

namespace Resolution {

/**
 * Class LiteralSelection implementing literal selection
 * @since 05/01/2008 Torrevieja
 */
class LiteralSelection
{
public:
  static void select(Clause* c);
}; // class LiteralSelection

}

#endif

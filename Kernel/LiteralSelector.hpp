/**
 * @file LiteralSelector.hpp
 * Defines class LiteralSelector and its descendants implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelector__
#define __LiteralSelector__

#include "../Forwards.hpp"

namespace Kernel {

/**
 * Class LiteralSelector is base class for
 * literal selector objects
 */
class LiteralSelector
{
public:
  virtual ~LiteralSelector() {}
  virtual void select(Clause* c) = 0;
};

/**
 * Class EagerLiteralSelection implements literal 
 * selector that selects all literals
 */
class EagerLiteralSelector
: public LiteralSelector
{
public:
  void select(Clause* c);
};


}

#endif /* __LiteralSelector__ */

/**
 * @file OrderingLiteralSelector.hpp
 * Defines class OrderingLiteralSelector.
 */


#ifndef __OrderingLiteralSelector__
#define __OrderingLiteralSelector__

#include "../Forwards.hpp"
#include "../Lib/SmartPtr.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class OrderingLiteralSelector implements literal
 * selector that selects heaviest negative literal, or all
 * maximal literals in specified ordering, if there's no
 * negative one.
 */
class OrderingLiteralSelector
: public LiteralSelector
{
public:
  OrderingLiteralSelector(OrderingSP ord) : _ord(ord) {}
  void select(Clause* c);
private:
  void selectPositive(Clause* c);

  OrderingSP _ord;
};

};

#endif /* __OrderingLiteralSelector__ */

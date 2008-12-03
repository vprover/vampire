/**
 * @file OrderingLiteralSelector.hpp
 * Defines class OrderingLiteralSelector.
 */


#ifndef __OrderingLiteralSelector__
#define __OrderingLiteralSelector__

#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

/**
 * Class OrderingLiteralSelector implements literal
 * selector that selects lightest negative literal, or all
 * literals, if there's no negative one.
 */
class OrderingLiteralSelector
: public LiteralSelector
{
public:
  OrderingLiteralSelector(Ordering* ord) : _ord(ord) {}
  void select(Clause* c);
private:
  void selectPositive(Clause* c);

  Ordering* _ord;
};

};

#endif /* __OrderingLiteralSelector__ */

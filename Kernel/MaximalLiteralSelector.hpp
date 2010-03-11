/**
 * @file MaximalLiteralSelector.hpp
 * Defines class MaximalLiteralSelector.
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
 * selector that selects a maximal negative literal,
 * if there is such. Otherwise it selects all maximal
 * literals.
 */
class MaximalLiteralSelector
: public LiteralSelector
{
public:
  MaximalLiteralSelector() : _ord(Ordering::instance()) {}
protected:
  void doSelection(Clause* c, unsigned eligible);
private:
  Ordering* _ord;
};

};

#endif /* __OrderingLiteralSelector__ */

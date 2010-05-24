/**
 * @file LiteralSelector.hpp
 * Defines class LiteralSelector and its descendants implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelector__
#define __LiteralSelector__

#include "Forwards.hpp"

#include "Term.hpp"

namespace Kernel {

/**
 * Class LiteralSelector is base class for
 * literal selector objects
 */
class LiteralSelector
{
public:
  LiteralSelector()
  {
#if VDEBUG
    _instCtr++;
#endif
  }
  virtual ~LiteralSelector()
  {
#if VDEBUG
    _instCtr--;
#endif
  }
  void select(Clause* c);

  static LiteralSelector* getSelector(int num);

  static void ensureSomeColoredSelected(Clause* c, unsigned eligible);

  static bool isPositiveForSelection(Literal* l)
  {
    if(_reversePolarity) {
      return l->isNegative()^l->isEquality(); //we don't change polarity for equality
    }
    else {
      return l->isPositive();
    }
  }
  static bool isNegativeForSelection(Literal* l)
  {
    return !isPositiveForSelection(l);
  }

  static int getSelectionPriority(Literal* l);

protected:
  /**
   * Perform selection on first @b eligible literals of clause @b c
   *
   * @b eligible has to be greater than 1. (Trivial cases should be taken
   * care of separately.)
   */
  virtual void doSelection(Clause* c, unsigned eligible) = 0;
private:
  static bool _reversePolarity;
#if VDEBUG
  static int _instCtr;
#endif
};

/**
 * Class EagerLiteralSelection implements literal
 * selector that selects all literals
 */
class TotalLiteralSelector
: public LiteralSelector
{
protected:
  void doSelection(Clause* c, unsigned eligible);
};



}

#endif /* __LiteralSelector__ */

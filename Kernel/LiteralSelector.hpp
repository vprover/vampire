/**
 * @file LiteralSelector.hpp
 * Defines class LiteralSelector and its descendants implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelector__
#define __LiteralSelector__

#include "../Forwards.hpp"

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
  virtual void select(Clause* c) = 0;

  static LiteralSelector* getSelector(int num);

  static void ensureSomeColoredSelected(Clause* c);

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

  static bool isSelectable(Literal* l);

  struct IsSelectableFn
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(Literal* l)
    {
      return isSelectable(l);
    }
  };

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
public:
  void select(Clause* c);
};



}

#endif /* __LiteralSelector__ */

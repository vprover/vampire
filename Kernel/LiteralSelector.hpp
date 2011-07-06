/**
 * @file LiteralSelector.hpp
 * Defines class LiteralSelector and its descendants implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelector__
#define __LiteralSelector__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
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

  /**
   * Return true if literal @b l is positive for the purpose of
   * literal selection
   *
   * This function is to allow for easy implementation of
   * selection functions with negative numbers. Those functions
   * consider all literals except for equality to be of
   * opposite polarity.
   */
  static bool isPositiveForSelection(Literal* l);

  static void reversePredicatePolarity(unsigned pred, bool reverse);

  /**
   * Return true if literal @b l is negative for the purpose of
   * literal selection
   *
   * @see isPositiveForSelection
   */
  static bool isNegativeForSelection(Literal* l)
  {
    return !isPositiveForSelection(l);
  }

  static int getSelectionPriority(Literal* l);

protected:
  /**
   * Perform selection on the first @b eligible literals of clause @b c
   *
   * @b eligible has to be greater than 1. (Trivial cases should be taken
   * care of separately.)
   *
   * It is a responsibility of this function to ensure that at least one
   * colored literal is selected if there is some in the clause.
   */
  virtual void doSelection(Clause* c, unsigned eligible) = 0;
private:
  /**
   * If true, the polarity of all literals except for equality ones is
   * considered to be reversed.
   *
   * @see isPositiveForSelection
   */
  static bool _reversePolarity;

  static ZIArray<bool> _reversePredicate;
#if VDEBUG
  /**
   * Counter of instances of LiteralSelector object
   *
   * It is used to ensure that there is at most one LiteralSelector
   * object created at a time. This check is neccessary, because the
   * polarity reversal for literal selectors with negative numbers
   * is controlled through the static variable @b _reversePolarity.
   */
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

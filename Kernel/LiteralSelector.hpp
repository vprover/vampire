/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LiteralSelector.hpp
 * Defines class LiteralSelector and its descendants implementing literal selection
 * @since 05/01/2008 Torrevieja
 */

#ifndef __LiteralSelector__
#define __LiteralSelector__

#include "Forwards.hpp"

#include "Lib/Array.hpp"

#include "Lib/Allocator.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

/**
 * Class LiteralSelector is base class for
 * literal selector objects
 */
class LiteralSelector
{
public:
  CLASS_NAME(LiteralSelector);
  USE_ALLOCATOR(LiteralSelector);

  LiteralSelector(const Ordering& ordering, const Options& options)
  : _ord(ordering), _opt(options), _reversePolarity(false)
  {
  }
  virtual ~LiteralSelector()
  {
  }
  /** if eligible is 0, all literals are eligible */
  void select(Clause* c, unsigned eligible=0);

  static LiteralSelector* getSelector(const Ordering& ordering, const Options& options, int selectorNumber);

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
  bool isPositiveForSelection(Literal* l) const;

  static void reversePredicatePolarity(unsigned pred, bool reverse);

  /**
   * Return true if literal @b l is negative for the purpose of
   * literal selection
   *
   * @see isPositiveForSelection
   */
  bool isNegativeForSelection(Literal* l) const
  {
    return !isPositiveForSelection(l);
  }

  int getSelectionPriority(Literal* l) const;

  /**
   * Does the selection maintain completeness in the Bachmair-Ganzinger sense?
   */
  virtual bool isBGComplete() const = 0;

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

  const Ordering& _ord;
  const Options& _opt;
private:
  /**
   * If true, the polarity of all literals except for equality ones is
   * considered to be reversed for the purposes of literal selection.
   *
   * @see isPositiveForSelection
   */
  bool _reversePolarity;

  static ZIArray<bool> _reversePredicate;
};

/**
 * Class EagerLiteralSelection implements literal
 * selector that selects all literals
 */
class TotalLiteralSelector
: public LiteralSelector
{
public:
  CLASS_NAME(TotalLiteralSelector);
  USE_ALLOCATOR(TotalLiteralSelector);

  TotalLiteralSelector(const Ordering& ordering, const Options& options)
  : LiteralSelector(ordering, options) {}

  bool isBGComplete() const override {
    // this is on purpose; we don't want any extra checks with total selection
    return false;
  }
protected:
  void doSelection(Clause* c, unsigned eligible) override;
};



}

#endif /* __LiteralSelector__ */

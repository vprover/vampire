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
 * @file MismatchHandler.hpp
 * Defines class MismatchHandler.
 *
 */

#ifndef __MismatchHandler__
#define __MismatchHandler__

#include "Forwards.hpp"
#include "Term.hpp"

namespace Kernel
{

class MismatchHandler
{
public:
  virtual ~MismatchHandler() {}
  struct ConstraintSet 
  { virtual void addConstraint(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2) = 0; };

  struct StackConstraintSet final : public ConstraintSet
  { 
    Stack<UnificationConstraint>& constr;

    StackConstraintSet(Stack<UnificationConstraint>& constr) 
      : constr(constr) {}

    virtual void addConstraint(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2) final override 
    { constr.push(make_pair(make_pair(t1, i1), make_pair(t2, i2))); } 
  };

  struct BacktrackableStackConstraintSet final : public ConstraintSet
  { 
    Stack<UnificationConstraint> &constr;
    BacktrackData& bd;

    BacktrackableStackConstraintSet(Stack<UnificationConstraint>& constr, BacktrackData& bd) 
      : constr(constr)
      , bd(bd) {}

    virtual void addConstraint(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2) final override 
    { constr.backtrackablePush(make_pair(make_pair(t1, i1), make_pair(t2, i2)), bd); } 
  };

  /** TODO document */
  virtual bool tryAbstract(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2,
      RobSubstitution& subs,
      ConstraintSet& constr) const = 0;
};

class UWAMismatchHandler final : public MismatchHandler
{
public:
  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);

  virtual bool tryAbstract(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2,
      RobSubstitution& subs,
      ConstraintSet& constr) const final override;

  bool canAbstract(
      TermList t1, 
      TermList t2) const;
};

class HOMismatchHandler : public MismatchHandler
{
public:
  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);

  virtual bool tryAbstract(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2,
      RobSubstitution& subs,
      ConstraintSet& constr) const final override;
};


}
#endif /*__MismatchHandler__*/

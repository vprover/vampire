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
#include "Lib/Metaiterators.hpp"
#include "Lib/Option.hpp"

namespace Kernel
{
class MismatchHandler;

struct UnificationConstraint
{
  CLASS_NAME(UnificationConstraint)
  USE_ALLOCATOR(UnificationConstraint)

  TermList term1;
  unsigned index1;
  TermList term2;
  unsigned index2;

  UnificationConstraint(TermList term1, unsigned index1, TermList term2, unsigned index2)
  : term1(term1), index1(index1)
  , term2(term2), index2(index2)
  {}

  Option<Literal*> toLiteral(RobSubstitution& s) const;
  // { 
  //   auto t1 = s.apply(term1, index1);
  //   auto t2 = s.apply(term2, index2);
  //   return Literal::createEquality(false, t1, t2, t1.isTerm() ? SortHelper::get); 
  // }
  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint const& self)
  { return out << self.term1 << "/" << self.index1 << " != " << self.term2 << "/" << self.index2; }

};

class UnificationConstraintStack
{
  Stack<UnificationConstraint> _cont;
public:
  CLASS_NAME(UnificationConstraintStack)
  USE_ALLOCATOR(UnificationConstraintStack)

  void addConstraint(UnificationConstraint c);

  auto iter() const
  { return iterTraits(_cont.iter()); }

  auto literalIter(RobSubstitution& s) const
  { return iterTraits(_cont.iter())
        .filterMap([&s](auto const& c) { return c.toLiteral(s); }); }

  auto toLiteralStack(RobSubstitution& s) const
  { 
    // TODO keep your out inside of this object and only hand out references
    Stack<Literal*> out(_cont.size());
    out.loadFromIterator(literalIter(s));
    return out;
  }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset()
  { _cont.reset(); }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(UnificationConstraint c)
  { _cont.push(std::move(c)); }

  void add(UnificationConstraint c, BacktrackData& bd)
  { _cont.backtrackablePush(std::move(c), bd); }
};


using UnificationConstraintStackSP = Lib::SmartPtr<UnificationConstraintStack> ;


class MismatchHandler
{
public:
  virtual ~MismatchHandler() {}
  struct ConstraintSet 
  { virtual void addConstraint(UnificationConstraint) = 0; };

  struct StackConstraintSet final : public ConstraintSet
  { 
    UnificationConstraintStack& constr;

    StackConstraintSet(UnificationConstraintStack& constr) 
      : constr(constr) {}

    virtual void addConstraint(UnificationConstraint c) final override 
    { constr.add(std::move(c)); } 
  };

  struct BacktrackableStackConstraintSet final : public ConstraintSet
  { 
    UnificationConstraintStack &constr;
    BacktrackData& bd;

    BacktrackableStackConstraintSet(UnificationConstraintStack& constr, BacktrackData& bd) 
      : constr(constr)
      , bd(bd) {}

    virtual void addConstraint(UnificationConstraint c) final override 
    { constr.add(std::move(c), bd); } 
  };

  /** TODO document */
  virtual bool tryAbstract(
      TermList t1, unsigned i1, 
      TermList t2, unsigned i2,
      RobSubstitution& subs,
      ConstraintSet& constr) const = 0;

  /** TODO document */
  virtual bool recheck(UnificationConstraint const&, RobSubstitution& s) const = 0;

  static unique_ptr<MismatchHandler> create();
  static unique_ptr<MismatchHandler> createOnlyHigherOrder();
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

  virtual bool recheck(UnificationConstraint const& c, RobSubstitution& s) const final override;
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

  virtual bool recheck(UnificationConstraint const& c, RobSubstitution& s) const final override
  { return true;  }
};


}
#endif /*__MismatchHandler__*/

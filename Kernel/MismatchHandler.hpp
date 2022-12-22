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
class RobSubstitution;

class MismatchHandlerTerm
{
  RobSubstitution& _subs;
  TermList _term; int _index;
  Option<pair<TermList, int>> _deref;
  friend class UnificationConstraint;
  friend class RobSubstitution;

  pair<TermList, int>& deref();
  TermList derefTerm() { return deref().first; }
  int derefIndex() { return deref().second; }
public:
  friend std::ostream& operator<<(std::ostream& out, MismatchHandlerTerm const& self);
  MismatchHandlerTerm(RobSubstitution& subs, TermList self, int index);

  bool isNormalVar();
  unsigned normalVarNumber();

  bool isSpecialVar();
  bool isTerm();
  bool isSort();

  unsigned functor();
  unsigned nTypeArgs();
  unsigned nTermArgs();
  bool isNumeral();
  bool isGround();
  MismatchHandlerTerm termArg(unsigned i);
  MismatchHandlerTerm typeArg(unsigned i);
  auto typeArgs() { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
};

class UnificationConstraint
{
  TermList _term1; int _index1;
  TermList _term2; int _index2;
public:
  CLASS_NAME(UnificationConstraint)
  USE_ALLOCATOR(UnificationConstraint)

  UnificationConstraint(MismatchHandlerTerm& t1, MismatchHandlerTerm& t2)
  : _term1(t1._term), _index1(t1._index)
  , _term2(t2._term), _index2(t2._index)
  { ASS(&t1._subs == &t2._subs) }

  Option<Literal*> toLiteral(RobSubstitution& s) const;

  MismatchHandlerTerm lhs(RobSubstitution& s) const { return MismatchHandlerTerm(s, _term1, _index1); }
  MismatchHandlerTerm rhs(RobSubstitution& s) const { return MismatchHandlerTerm(s, _term2, _index2); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint const& self)
  { return out << self._term1 << "/" << self._index1 << " != " << self._term2 << "/" << self._index2; }

};

class UnificationConstraintStack
{
  Stack<UnificationConstraint> _cont;
public:
  CLASS_NAME(UnificationConstraintStack)
  USE_ALLOCATOR(UnificationConstraintStack)
  UnificationConstraintStack() : _cont() {}
  UnificationConstraintStack(UnificationConstraintStack&&) = default;
  UnificationConstraintStack& operator=(UnificationConstraintStack&&) = default;

  void addConstraint(UnificationConstraint c);

  auto iter() const
  { return iterTraits(_cont.iter()); }

  RecycledPointer<Stack<Literal*>> literals(RobSubstitution& s);

  auto literalIter(RobSubstitution& s)
  { return iterTraits(_cont.iter())
              .filterMap([&s](auto const& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset()
  { _cont.reset(); }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(UnificationConstraint c);
  void add(UnificationConstraint c, BacktrackData& bd);
};


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
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2,
      ConstraintSet& constr) const = 0;

  /** TODO document */
  virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const = 0;

  static unique_ptr<MismatchHandler> create();
  static unique_ptr<MismatchHandler> createOnlyHigherOrder();
};

class UWAMismatchHandler final : public MismatchHandler
{
public:
  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);
  bool isInterpreted(unsigned f) const;

  virtual bool tryAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2,
      ConstraintSet& constr) const final override;

  bool canAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2) const;

  virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const final override;
};

class HOMismatchHandler : public MismatchHandler
{
public:
  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);

  virtual bool tryAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2,
      ConstraintSet& constr) const final override;


  virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const final override
  { return true;  }
};


}
#endif /*__MismatchHandler__*/

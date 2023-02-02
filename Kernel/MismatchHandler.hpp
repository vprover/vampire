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
#include "RobSubstitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Reflection.hpp"

namespace Kernel
{


class MismatchHandlerTerm
{
  RobSubstitution* _subs;
  TermList _term; int _index;
  Option<pair<TermList, int>> _deref;
  friend class UnificationConstraint;
  friend class RobSubstitution;

  pair<TermList, int>& deref();
  TermList derefTerm() { return deref().first; }
  int derefIndex() { return deref().second; }
public:
  auto asTuple() const -> pair<TermList, int> const& { ASS(_deref.isSome()); return *_deref; }
  IMPL_COMPARISONS_FROM_TUPLE(MismatchHandlerTerm)
  friend std::ostream& operator<<(std::ostream& out, MismatchHandlerTerm const& self);
  MismatchHandlerTerm(RobSubstitution& subs, TermList self, int index);
  MismatchHandlerTerm(unsigned functor, std::initializer_list<MismatchHandlerTerm> args);

  unsigned normalVarNumber() { return derefTerm().var(); }

  bool isNormalVar()   { return derefTerm().isVar() && !derefTerm().isSpecialVar(); }
  bool isSpecialVar()  { return derefTerm().isSpecialVar(); }
  bool isAnyVar()      { return derefTerm().isVar(); }
  bool isTerm()        { return derefTerm().isTerm(); }
  bool isSort()        { return derefTerm().term()->isSort(); }

  unsigned functor()   { return derefTerm().term()->functor(); }
  unsigned nTypeArgs() { return derefTerm().term()->numTypeArguments(); }
  unsigned nTermArgs() { return derefTerm().term()->numTermArguments(); }
  bool isNumeral()     { return derefTerm().isTerm() && env.signature->getFunction(functor())->numericConstant(); }
  bool isGround()      { return _subs->apply(_term, _index).ground(); }
  MismatchHandlerTerm termArg(unsigned i);
  MismatchHandlerTerm typeArg(unsigned i);
  auto typeArgs() { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
};

class UnificationConstraint
{
  TermList _term1; int _index1;
  TermList _term2; int _index2;
  friend class RobSubstitution;
public:
  CLASS_NAME(UnificationConstraint)
  USE_ALLOCATOR(UnificationConstraint)

  UnificationConstraint(MismatchHandlerTerm const& t1, MismatchHandlerTerm const& t2)
  : _term1(t1._term), _index1(t1._index)
  , _term2(t2._term), _index2(t2._index)
  { ASS(t1._subs == t2._subs) }

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

  auto iter() const
  { return iterTraits(_cont.iter()); }

  Recycled<Stack<Literal*>> literals(RobSubstitution& s);

  auto literalIter(RobSubstitution& s)
  { return iterTraits(_cont.iter())
              .filterMap([&s](auto const& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset()
  { _cont.reset(); }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(UnificationConstraint c, Option<BacktrackData&> bd);
};

class AbstractingUnifier {
  Recycled<RobSubstitution> _subs;
  Recycled<UnificationConstraintStack> _constr;
  Option<BacktrackData&> _bd;
  MismatchHandler* _uwa;
  friend class RobSubstitution;
public:
  // DEFAULT_CONSTRUCTORS(AbstractingUnifier)
  AbstractingUnifier(MismatchHandler* uwa) : _subs(), _constr(), _bd(), _uwa(uwa) 
  { }

  bool isRecording() { return _subs->bdIsRecording(); }

  void add(UnificationConstraint c) 
  { _constr->add(std::move(c), _subs->bdIsRecording() ? Option<BacktrackData&>(_subs->bdGet())
                                                      : Option<BacktrackData&>()              ); }

  bool unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2)
  { 
    return _subs->unify(t1, bank1, t2, bank2, _uwa, this); 
  }


  UnificationConstraintStack& constr() { return *_constr; }
  Recycled<Stack<Literal*>> constraintLiterals() { return _constr->literals(*_subs); }

  RobSubstitution& subs() { return *_subs; }
  void bdRecord(BacktrackData& bd) { _subs->bdRecord(bd); }
  void bdDone() { _subs->bdDone(); }
  bool usesUwa() const { return _uwa != nullptr; }
};

using Action = std::function<bool(unsigned, MismatchHandlerTerm)>;
using SpecialVar = unsigned;
using WaitingMap = DHMap<SpecialVar, Action>;

class MismatchHandler
{
public:
  virtual ~MismatchHandler() {}

  struct EqualIf { 
    Recycled<Stack<UnificationConstraint>> unify; 
    Recycled<Stack<UnificationConstraint>> constraints; 

    EqualIf( std::initializer_list<UnificationConstraint> unify,
             std::initializer_list<UnificationConstraint> constraints
        ) : unify(unify)
          , constraints(constraints) {  }
  };
  struct NeverEqual { };

  using AbstractionResult = Coproduct<NeverEqual, EqualIf>;


  /** TODO document */
  virtual Option<AbstractionResult> tryAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2) const = 0;

  // /** TODO document */
  // virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const = 0;

  static unique_ptr<MismatchHandler> create();
  static unique_ptr<MismatchHandler> createOnlyHigherOrder();
};

class UWAMismatchHandler final : public MismatchHandler
{
public:
  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);
  bool isInterpreted(unsigned f) const;

  // virtual bool tryAbstract(
  //     MismatchHandlerTerm t1,
  //     MismatchHandlerTerm t2,
  //     AbstractingUnifier& constr) const final override;

  virtual Option<AbstractionResult> tryAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2) const final override;

  bool canAbstract(
      Shell::Options::UnificationWithAbstraction opt,
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2) const;

  // virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const final override;
};

class HOMismatchHandler : public MismatchHandler
{
public:
  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);

  virtual Option<AbstractionResult> tryAbstract(
      MismatchHandlerTerm t1,
      MismatchHandlerTerm t2) const final override;


  // virtual bool recheck(MismatchHandlerTerm l, MismatchHandlerTerm r) const final override
  // { return true;  }
};


}
#endif /*__MismatchHandler__*/

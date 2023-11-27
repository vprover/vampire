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
#include "Shell/Options.hpp"

namespace Kernel
{


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
  { return arrayIter(_cont).filterMap([&](auto& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset() { _cont.reset(); }
  bool keepRecycled() const { return _cont.keepRecycled() > 0; }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(UnificationConstraint c, Option<BacktrackData&> bd);
  UnificationConstraint pop(Option<BacktrackData&> bd);
};

using Action = std::function<bool(unsigned, TermSpec)>;
using SpecialVar = unsigned;
using WaitingMap = DHMap<SpecialVar, Action>;

class MismatchHandler final
{
  Shell::Options::UnificationWithAbstraction _mode;
  friend class AbstractingUnifier;
public:
  MismatchHandler(Shell::Options::UnificationWithAbstraction mode) : _mode(mode) {}

  struct EqualIf { 
    Recycled<Stack<UnificationConstraint>> _unify; 
    Recycled<Stack<UnificationConstraint>> _constr; 

    EqualIf() : _unify(), _constr() {}


    auto unify()  -> decltype(auto) { return *_unify; }
    auto constr() -> decltype(auto) { return *_constr; }

    EqualIf constr(decltype(_constr) constr) &&
    { _constr = std::move(constr); return std::move(*this); }

    EqualIf unify(decltype(_unify) unify) &&
    { _unify = std::move(unify); return std::move(*this); }


    template<class... As>
    EqualIf constr(UnificationConstraint constr, As... constrs) &&
    { 
      unsigned constexpr len = TypeList::Size<TypeList::List<UnificationConstraint, As...>>::val;
      _constr->reserve(len);
      __push(*_constr, std::move(constr), std::move(constrs)...);
      return std::move(*this); 
    }


    template<class... As>
    EqualIf unify(UnificationConstraint unify, As... unifys) &&
    { 
      unsigned constexpr len = TypeList::Size<TypeList::List<UnificationConstraint, As...>>::val;
      _unify->reserve(len);
      __push(*_unify, std::move(unify), std::move(unifys)...);
      return std::move(*this); 
    }

    friend std::ostream& operator<<(std::ostream& out, EqualIf const& self)
    { return out << "EqualIf(unify: " << self._unify << ", constr: " << self._constr <<  ")"; }
   private:
    void __push(Stack<UnificationConstraint>& s)
    {  }
    template<class... As>
    void __push(Stack<UnificationConstraint>& s, UnificationConstraint c, As... as)
    { s.push(std::move(c)); __push(s, std::move(as)...); }
  };

  struct NeverEqual {
    friend std::ostream& operator<<(std::ostream& out, NeverEqual const&)
    { return out << "NeverEqual"; } 
  };

  using AbstractionResult = Coproduct<NeverEqual, EqualIf>;

  /** TODO document */
  Option<AbstractionResult> tryAbstract(
      AbstractingUnifier* au,
      TermSpec const& t1,
      TermSpec const& t2) const;

  // /** TODO document */
  // virtual bool recheck(TermSpec l, TermSpec r) const = 0;

  static Shell::Options::UnificationWithAbstraction create();
  static Shell::Options::UnificationWithAbstraction createOnlyHigherOrder();

private:
  // for old non-alasca uwa modes
  bool isInterpreted(unsigned f) const;
  bool canAbstract(
      AbstractingUnifier* au,
      TermSpec const& t1,
      TermSpec const& t2) const;
};

class AbstractingUnifier {
  Recycled<RobSubstitution> _subs;
  Recycled<UnificationConstraintStack> _constr;
  Option<BacktrackData&> _bd;
  MismatchHandler _uwa;
  friend class RobSubstitution;
  AbstractingUnifier(MismatchHandler uwa) : _subs(), _constr(), _bd(), _uwa(uwa) { }
public:
  // DEFAULT_CONSTRUCTORS(AbstractingUnifier)
  static AbstractingUnifier empty(MismatchHandler uwa) 
  { return AbstractingUnifier(uwa); }

  bool isRecording() { return _subs->bdIsRecording(); }

  bool unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2);
  bool unify(TermSpec l, TermSpec r, bool& progress);
  bool fixedPointIteration();


  static Option<AbstractingUnifier> unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2, MismatchHandler uwa, bool fixedPointIteration)
  {
    auto au = AbstractingUnifier::empty(uwa);
    if (!au.unify(t1, bank1, t2, bank2)) return {};
    if (!fixedPointIteration || au.fixedPointIteration()) return some(std::move(au));
    else return {};
  }


  UnificationConstraintStack& constr() { return *_constr; }
  Recycled<Stack<Literal*>> constraintLiterals() { return _constr->literals(*_subs); }

  RobSubstitution      & subs()       { return *_subs; }
  RobSubstitution const& subs() const { return *_subs; }
  Option<BacktrackData&> bd() { return someIf(_subs->bdIsRecording(), [&]() -> decltype(auto) { return _subs->bdGet(); }); }
  BacktrackData& bdGet() { return _subs->bdGet(); }
  void bdRecord(BacktrackData& bd) { _subs->bdRecord(bd); }
  void bdDone() { _subs->bdDone(); }
  bool usesUwa() const { return _uwa._mode != Options::UnificationWithAbstraction::OFF; }

  friend std::ostream& operator<<(std::ostream& out, AbstractingUnifier const& self)
  { return out << "(" << self._subs << ", " << self._constr << ")"; }
};

} // namespace Kernel
#endif /*__MismatchHandler__*/

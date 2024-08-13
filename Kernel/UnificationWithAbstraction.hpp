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
 * @file UnificationWithAbstraction.hpp
 * Defines class AbstractionOracle.
 *
 */

#ifndef __AbstractionOracle__
#define __AbstractionOracle__

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
  Lib::Stack<UnificationConstraint> _cont;
public:
  USE_ALLOCATOR(UnificationConstraintStack)
  UnificationConstraintStack() : _cont() {}
  UnificationConstraintStack(UnificationConstraintStack&&) = default;
  UnificationConstraintStack& operator=(UnificationConstraintStack&&) = default;

  auto iter() const
  { return iterTraits(_cont.iter()); }

  Lib::Recycled<Lib::Stack<Literal*>> literals(RobSubstitution& s);

  // returns the maximum number of constraints of this stack. this is not equal to the actual number of constraints it will hold, as constraints 
  // might become trivial (i.e. of the form t != t) after applying the substitution, so they will be filtered out when calling literals(RobSubstitution&)
  unsigned maxNumberOfConstraints() { return _cont.size(); }

  auto literalIter(RobSubstitution& s)
  { return iterTraits(_cont.iter())
              .filterMap([&](auto& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset() { _cont.reset(); }
  bool keepRecycled() const { return _cont.keepRecycled() > 0; }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(UnificationConstraint c, Lib::Option<Lib::BacktrackData&> bd);
  UnificationConstraint pop(Lib::Option<Lib::BacktrackData&> bd);
};

class AbstractionOracle final
{
  Shell::Options::UnificationWithAbstraction _mode;
  friend class AbstractingUnifier;
public:
  AbstractionOracle(Shell::Options::UnificationWithAbstraction mode) : _mode(mode) {}

  struct EqualIf { 
    Lib::Recycled<Lib::Stack<UnificationConstraint>> _unify; 
    Lib::Recycled<Lib::Stack<UnificationConstraint>> _constr; 

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
      _constr->pushMany(std::move(constr), std::move(constrs)...);
      return std::move(*this); 
    }

    template<class... As>
    EqualIf unify(UnificationConstraint unify, As... unifys) &&
    { 
      _unify->pushMany(std::move(unify), std::move(unifys)...);
      return std::move(*this); 
    }

    friend std::ostream& operator<<(std::ostream& out, EqualIf const& self)
    { return out << "EqualIf(unify: " << self._unify << ", constr: " << self._constr <<  ")"; }
  };

  struct NeverEqual {
    friend std::ostream& operator<<(std::ostream& out, NeverEqual const&)
    { return out << "NeverEqual"; } 
  };

  using AbstractionResult = Lib::Coproduct<NeverEqual, EqualIf>;

  /** main function that either returns nothing, which means that unification with abstraction will 
   * shall not be applied for the given terms, or an AbstractionResult, which tells wether the given 
   * terms can be unified in the background theory or not, and under which conditions. 
   *
   * If the `AbstractionResult` is `NeverEqual` this means that the two terms are never equal in 
   * the background theory, hence the unification algorithm using this `AbstractionOracle` will fail 
   * immediately. 
   * If the `AbstractionResult` is `EqualIf e` the unification algorithm will introduce constraints `e.constr()` and continue unifying `e.unify(y)`.
   *
   * For details check out the paper "Refining Unification with Absraction" from LPAR 2023.
   */
  Lib::Option<AbstractionResult> tryAbstract(
      AbstractingUnifier* au,
      TermSpec const& t1,
      TermSpec const& t2) const;

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

class AbstractingUnifier 
{
  Lib::Recycled<RobSubstitution> _subs;
  Lib::Recycled<UnificationConstraintStack> _constr;
  Lib::Option<Lib::BacktrackData&> _bd;
  AbstractionOracle _uwa;

  friend class RobSubstitution;
  AbstractingUnifier(AbstractionOracle uwa) : _subs(), _constr(), _bd(), _uwa(uwa) { }
public:
  void init(AbstractionOracle uwa) 
  { 
    _subs->reset();
    _constr->reset();
    _bd = {};
    _uwa = std::move(uwa);
  }

  static AbstractingUnifier empty(AbstractionOracle uwa) { return AbstractingUnifier(uwa); }

  bool isRecording() { return _subs->bdIsRecording(); }

  bool unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2);
  bool unify(TermSpec l, TermSpec r, bool& progress);
  bool fixedPointIteration();

  // TODO document
  Lib::Option<Lib::Recycled<Lib::Stack<unsigned>>> unifiableSymbols(SymbolId f);


  static Lib::Option<AbstractingUnifier> unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2, AbstractionOracle uwa, bool fixedPointIteration)
  {
    auto au = AbstractingUnifier::empty(uwa);
    if (!au.unify(t1, bank1, t2, bank2)) return {};
    if (!fixedPointIteration || au.fixedPointIteration()) return Lib::some(std::move(au));
    else return {};
  }

  UnificationConstraintStack& constr() { return *_constr; }
  Lib::Recycled<Lib::Stack<Literal*>> computeConstraintLiterals() { return _constr->literals(*_subs); }
  unsigned maxNumberOfConstraints() { return _constr->maxNumberOfConstraints(); }

  RobSubstitution      & subs()       { return *_subs; }
  RobSubstitution const& subs() const { return *_subs; }
  Lib::Option<Lib::BacktrackData&> bd() { return Lib::someIf(_subs->bdIsRecording(), [&]() -> decltype(auto) { return _subs->bdGet(); }); }
  Lib::BacktrackData& bdGet() { return _subs->bdGet(); }
  void bdRecord(Lib::BacktrackData& bd) { _subs->bdRecord(bd); }
  void bdDone() { _subs->bdDone(); }
  bool usesUwa() const { return _uwa._mode != Options::UnificationWithAbstraction::OFF; }

  friend std::ostream& operator<<(std::ostream& out, AbstractingUnifier const& self)
  { return out << "(" << self._subs << ", " << self._constr << ")"; }
};

} // namespace Kernel
#endif /*__AbstractionOracle__*/

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
#include "Shell/Options.hpp"
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

class MismatchHandler final
{
  Shell::Options::UnificationWithAbstraction _mode;
  friend class UnificationAlgorithms::AbstractingUnification;

  using AbstractingAlgo = UnificationAlgorithms::AbstractingUnification;
public:

  MismatchHandler(Shell::Options::UnificationWithAbstraction mode) : _mode(mode) {}

  using UnifConstraint = UnificationConstraint<TermList,VarBank>;

  struct EqualIf { 
    Recycled<Stack<UnifConstraint>> _unify; 
    Recycled<Stack<UnifConstraint>> _constr; 

    EqualIf() : _unify(), _constr() {}

    auto unify()  -> decltype(auto) { return *_unify; }
    auto constr() -> decltype(auto) { return *_constr; }

    EqualIf constr(decltype(_constr) constr) &&
    { _constr = std::move(constr); return std::move(*this); }

    EqualIf unify(decltype(_unify) unify) &&
    { _unify = std::move(unify); return std::move(*this); }


    template<class... As>
    EqualIf constr(UnifConstraint constr, As... constrs) &&
    { 
      unsigned constexpr len = TypeList::Size<TypeList::List<UnifConstraint, As...>>::val;
      _constr->reserve(len);
      __push(*_constr, std::move(constr), std::move(constrs)...);
      return std::move(*this); 
    }


    template<class... As>
    EqualIf unify(UnifConstraint unify, As... unifys) &&
    { 
      unsigned constexpr len = TypeList::Size<TypeList::List<UnifConstraint, As...>>::val;
      _unify->reserve(len);
      __push(*_unify, std::move(unify), std::move(unifys)...);
      return std::move(*this); 
    }

    friend std::ostream& operator<<(std::ostream& out, EqualIf const& self)
    { return out << "EqualIf(unify: " << self._unify << ", constr: " << self._constr <<  ")"; }
   private:
    void __push(Stack<UnifConstraint>& s)
    {  }
    template<class... As>
    void __push(Stack<UnifConstraint>& s, UnifConstraint c, As... as)
    { s.push(std::move(c)); __push(s, std::move(as)...); }
  };

  struct NeverEqual {
    friend std::ostream& operator<<(std::ostream& out, NeverEqual const&)
    { return out << "NeverEqual"; } 
  };

  using AbstractionResult = Coproduct<NeverEqual, EqualIf>;

  /** TODO document */
  Option<AbstractionResult> tryAbstract(
      RobSubstitutionTL* rob,
      TermList const& t1,
      TermList const& t2) const;

  auto mode() const { return _mode; }

  // /** TODO document */
  // virtual bool recheck(TermSpec l, TermSpec r) const = 0;

  static Shell::Options::UnificationWithAbstraction create();

private:
  // for old non-alasca uwa modes
  bool isInterpreted(unsigned f) const;
  bool canAbstract(
      TermList const& t1,
      TermList const& t2) const;
};

namespace UnificationAlgorithms {

// TODO moce somewhere more suitable
class RobUnification { 
public:

  // to be used for tree calls
  bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub)
  {
    CALL("RobUnification::associate");
    TermList query(specialVar, /* special */ true);
    return sub->unify(query, node);
  }

  // To be used for non-tree calls. Return an iterator instead of bool
  // to fit HOL interface
  SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false){
    CALL("RobUnification::unifiers");

    if(sub->unify(t1, t2)){
      return pvi(getSingletonIterator(sub));
    }
    return SubstIterator::getEmpty();
  }

  // function is called when in the leaf of a substitution tree 
  // during unification. t is the term stored in the leaf, sort is its sort
  SubstIterator postprocess(RobSubstitutionTL* sub, TermList t, TermList sort){
    CALL("RobUnification::postprocess");     
    
    // sub is a unifier of query and leaf term t, return it
    return pvi(getSingletonIterator(sub));
  }

  void initSub(RobSubstitutionTL* sub) const { }

  bool usesUwa() const { return false; }
};

class AbstractingUnification {
  MismatchHandler _uwa;
  bool _fpi;

public:
  // DEFAULT_CONSTRUCTORS(AbstractingUnifier)
  AbstractingUnification(MismatchHandler uwa, bool fixedPointIter) : 
   _uwa(uwa), _fpi(fixedPointIter) {  }

  bool unify(TermList t1, TermList t2, RobSubstitutionTL* sub);
  bool unify(TermList l,  TermList r, bool& progress, RobSubstitutionTL* sub);
  bool fixedPointIteration(RobSubstitutionTL* sub);
  SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitutionTL* sub, TermList t, TermList sort);

  bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub)
  {
    CALL("AbstractingUnification::associate");
    
    TermList query(specialVar, /* special */ true);
    return unify(query, node, sub);
  }

  void initSub(RobSubstitutionTL* sub) const { }

  bool usesUwa() const { return _uwa.mode() != Options::UnificationWithAbstraction::OFF; }
};

}

} // namespace Kernel
#endif /*__MismatchHandler__*/

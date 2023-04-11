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
      RobSubstitution* rob,
      TermSpec const& t1,
      TermSpec const& t2) const;

  auto mode() const { return _mode; }

  // /** TODO document */
  // virtual bool recheck(TermSpec l, TermSpec r) const = 0;

  static Shell::Options::UnificationWithAbstraction create();

private:
  // for old non-alasca uwa modes
  bool isInterpreted(unsigned f) const;
  bool canAbstract(
      TermSpec const& t1,
      TermSpec const& t2) const;
};

namespace UnificationAlgorithms {

// TODO moce somewhere more suitable
class RobUnification { 
public:

  // to be used for tree calls
  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitution* sub)
  {
    CALL("RobUnification::associate");
    TermList query(specialVar, /* special */ true);
    return sub->unify(query, Indexing::QUERY_BANK, node, Indexing::NORM_RESULT_BANK);
  }

  // To be used for non-tree calls. Return an iterator instead of bool
  // to fit HOL interface
  SubstIterator unifiers(TermList t1, int index1, TermList t2, int index2, RobSubstitution* sub, bool topLevelCheck = false){
    CALL("RobUnification::unifiers");

    if(sub->unify(t1, index1, t2, index2)){
      return pvi(getSingletonIterator(sub));
    }
    return SubstIterator::getEmpty();
  }

  // function is called when in the leaf of a substitution tree 
  // during unification. t is the term stored in the leaf
  SubstIterator postprocess(RobSubstitution* sub, TermList t){
    CALL("RobUnification::postprocess");     
    
    // sub is a unifier of query and leaf term t, return it
    return pvi(getSingletonIterator(sub));
  }

  bool usesUwa() const { return false; }
};

class AbstractingUnification {
  MismatchHandler _uwa;
  bool _fpi;

public:
  // DEFAULT_CONSTRUCTORS(AbstractingUnifier)
  AbstractingUnification(MismatchHandler uwa, bool fixedPointIter) : 
   _uwa(uwa), _fpi(fixedPointIter) {  }

  bool unify(TermList t1, unsigned bank1, TermList t2, unsigned bank2, RobSubstitution* sub);
  bool unify(TermSpec l, TermSpec r, bool& progress, RobSubstitution* sub);
  bool fixedPointIteration(RobSubstitution* sub);
  SubstIterator unifiers(TermList t1, int index1, TermList t2, int index2, RobSubstitution* sub, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitution* sub, TermList t);

  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitution* sub)
  {
    CALL("AbstractingUnification::associate");
    
    TermList query(specialVar, /* special */ true);
    return unify(query, Indexing::QUERY_BANK, node, Indexing::NORM_RESULT_BANK, sub);
  }

  bool usesUwa() const { return _uwa.mode() != Options::UnificationWithAbstraction::OFF; }
};

}

} // namespace Kernel
#endif /*__MismatchHandler__*/

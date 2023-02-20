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
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __RobSubstitution__
#define __RobSubstitution__

#include "Forwards.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

#if VDEBUG
#include <iostream>
#include "Lib/VString.hpp"
#endif

namespace Kernel
{
struct VarSpec
{
  /** Create a new VarSpec struct */
  VarSpec() {}
  /** Create a new VarSpec struct */
  VarSpec(unsigned var, int index) : var(var), index(index) {}

  bool operator==(const VarSpec& o) const
  { return var==o.var && index==o.index; }
  bool operator!=(const VarSpec& o) const
  { return !(*this==o); }

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self);

  /** number of variable */
  unsigned var;
  /** index of variable bank */
  int index;

  /** struct containing first hash function for DHMap object storing variable banks */
  struct Hash1
  {
   static unsigned hash(VarSpec const& o) {
     return HashUtils::combine(o.var, o.index);
   }
  };
  /** struct containing second hash function for DHMap object storing variable banks */
  struct Hash2
  {
    static unsigned hash(VarSpec const& o) {
      return HashUtils::combine(o.index, o.var);
    }
  };
};

// TODO get rid of this
struct OldTermSpec {
  OldTermSpec() {}
  OldTermSpec(TermList t, int i) : term(t), index(i) {}
  auto asTuple() const -> decltype(auto) { return std::tie(term, index); }
  IMPL_COMPARISONS_FROM_TUPLE(OldTermSpec)
  IMPL_HASH_FROM_TUPLE(OldTermSpec)

  TermList term;
  int index;

  bool sameTermContent(const OldTermSpec& ts)
  {
    bool termSameContent=term.sameContent(&ts.term);
    if(!termSameContent && term.isTerm() && term.term()->isLiteral() &&
      ts.term.isTerm() && ts.term.term()->isLiteral()) {
      const Literal* l1=static_cast<const Literal*>(term.term());
      const Literal* l2=static_cast<const Literal*>(ts.term.term());
      if(l1->functor()==l2->functor() && l1->arity()==0) {
        return true;
      }
    }
    if(!termSameContent) {
      return false;
    }
    return index==ts.index || term.isSpecialVar() ||
      (term.isTerm() && (
  (term.term()->shared() && term.term()->ground()) ||
   term.term()->arity()==0 ));
  }

  OldTermSpec clone() const { return *this; }
};

class TermSpec
{
  // TODO get rid of implicit copying of this
  struct Appl {
    unsigned functor;
    Option<Recycled<Stack<TermSpec>>> args;
    auto asTuple() const -> decltype(auto) { return std::tie(functor, args); }
    IMPL_COMPARISONS_FROM_TUPLE(TermSpec::Appl)
    IMPL_HASH_FROM_TUPLE(TermSpec::Appl)
    bool isSort() const { return false; }

    TermSpec const& arg(unsigned i) const { return (**args)[i]; }
    auto argsIter() const 
    { return iterTraits(args.iter())
                  .flatMap([](auto& args) { return getArrayishObjectIterator<const_ref_t>(*args); }); }
    Appl clone() const 
    { return Appl { .functor = functor, 
                    .args = args.map([](auto& x) { 
                        return x.clone([](auto& to, auto const& from) { 
                            to.loadFromIterator(
                                arrayIter(from)
                                  .map([](auto& c){ return c.clone(); })); 
                            }); 
                        }), 
                  }; }
  };
  using Copro = Coproduct<
    Appl,
    OldTermSpec
    >;
  Copro _self;
  friend class UnificationConstraint;
  friend class RobSubstitution;

  // TermList derefTerm() { return deref().first; }
  // int derefIndex() { return deref().second; }
  TermSpec(TermSpec const&) = delete;
  TermSpec(Copro self) : _self(std::move(self)) {}
public:
  TermSpec(TermSpec&&) = default;
  TermSpec& operator=(TermSpec&&) = default;
  OldTermSpec old() const { return _self.unwrap<OldTermSpec>(); }
  // TODO get rid of default constructor
  TermSpec() : TermSpec(decltype(_self)(OldTermSpec())) {}
  TermSpec(VarSpec v) : TermSpec(TermList::var(v.var), v.index) {}
  // auto asTuple() const -> decltype(auto) { return std::make_tuple(select(
  //       [&](){ return isVar(); }, [&]() { return varSpec(); }
  //                               , [&]() { return std::make_tuple(functor(), iterAsData(allArgs())); }
  //       )); }
  // IMPL_COMPARISONS_FROM_TUPLE(TermSpec)
  // IMPL_HASH_FROM_TUPLE(TermSpec)

  friend bool operator==(TermSpec const& lhs, TermSpec const& rhs);
  friend bool operator<(TermSpec const& lhs, TermSpec const& rhs);
  IMPL_COMPARISONS_FROM_LESS_AND_EQUALS(TermSpec);
  unsigned defaultHash() const;
  unsigned defaultHash2() const;

  TermSpec clone() const { return TermSpec(_self.clone()); }
  
  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self);
  TermSpec(TermList self, int index) : _self(OldTermSpec(self, index)) {}


  template<class... Args>
  TermSpec(unsigned functor, Args... args) 
    : _self(Appl{functor, someIf(sizeof...(args) != 0, []() { return Recycled<Stack<TermSpec>>(); }) }) 
  {
    if (sizeof...(args) != 0) _self.template unwrap<Appl>().args.unwrap()->pushMany(std::move(args)...);
  }

  TermList::Top top() const;
  TermSpec const& deref(RobSubstitution const* s) const;
  bool isOutputVar() const;
  unsigned varNumber() const { return *top().var(); }
  bool definitelyGround() const;// { return t->shared() && t->ground(); }
  // assuming it's ground
  unsigned weight() const;
  bool sameTermContent(TermSpec const& other) const;

  bool isSpecialVar()  const;
  bool isVar()         const;
  bool isNormalVar()   const { return isVar() && !isSpecialVar(); }

  bool isTerm() const;
  bool isLiteral() const;
  TermSpec sort() const;
  bool isSort() const;
  VarSpec varSpec() const;
  unsigned functor()   const;

  unsigned nTypeArgs() const;//{ return derefTerm().term()->numTypeArguments(); }
  unsigned nTermArgs() const;//{ return derefTerm().term()->numTermArguments(); }
  unsigned nAllArgs() const;//{ return derefTerm().term()->numTermArguments(); }
                            //
  bool isNumeral() const { return isTerm() && env.signature->getFunction(functor())->interpretedNumber(); }
  // bool isGround()      { return _subs->apply(_term, _index).ground(); }
  TermSpec termArg(unsigned i) const;
  TermSpec typeArg(unsigned i) const;
  TermSpec anyArg(unsigned i) const;
  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs() const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }

  TermList toTerm(RobSubstitution& s) const;

};

struct AutoDerefTermSpec
{
  TermSpec term;
  RobSubstitution const* subs;
  AutoDerefTermSpec clone() const { return { term.clone(), subs, }; }
  AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s) 
    : term(t.deref(s).clone())
    , subs(s) { }
  explicit AutoDerefTermSpec(AutoDerefTermSpec const& other) : term(other.term.clone()), subs(other.subs) {}
  AutoDerefTermSpec(AutoDerefTermSpec && other) = default;
};

class UnificationConstraint
{
  TermSpec _t1;
  TermSpec _t2;
public:
  // TODO get rid of default constr
  UnificationConstraint() {}
  CLASS_NAME(UnificationConstraint)
  USE_ALLOCATOR(UnificationConstraint)
  // UnificationConstraint(UnificationConstraint&&) = default;
  // UnificationConstraint& operator=(UnificationConstraint&&) = default;
  auto asTuple() const -> decltype(auto) { return std::tie(_t1, _t2); }
  IMPL_COMPARISONS_FROM_TUPLE(UnificationConstraint);
  IMPL_HASH_FROM_TUPLE(UnificationConstraint);

  UnificationConstraint clone() const { return UnificationConstraint(lhs().clone(), rhs().clone()); }

  UnificationConstraint(TermSpec t1, TermSpec t2)
  : _t1(std::move(t1)), _t2(std::move(t2))
  {}

  Option<Literal*> toLiteral(RobSubstitution& s);

  TermSpec const& lhs() const { return _t1; }
  TermSpec const& rhs() const { return _t2; }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint const& self)
  { return out << self._t1 << " != " << self._t2; }

};




using namespace Lib;

class AbstractingUnifier;
class UnificationConstraint;

class RobSubstitution
:public Backtrackable
{
  friend class AbstractingUnifier;
  friend class UnificationConstraint;
public:
  CLASS_NAME(RobSubstitution);
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() : _nextUnboundAvailable(0) {}

  SubstIterator matches(Literal* base, int baseIndex,
	  Literal* instance, int instanceIndex, bool complementary);
  SubstIterator unifiers(Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  bool unify(TermList t1,int index1, TermList t2, int index2);
  bool match(TermList base,int baseIndex, TermList instance, int instanceIndex);

  bool unifyArgs(Term* t1,int index1, Term* t2, int index2);
  bool matchArgs(Term* base,int baseIndex, Term* instance, int instanceIndex);

  void denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex);
  bool isUnbound(unsigned var, int index) const
  {
    return isUnbound(VarSpec(var,index));
  }
  void reset()
  {
    _bank.reset();
    _nextUnboundAvailable=0;
  }
  bool keepRecycled() const { return _bank.keepRecycled(); }

  /**
   * Bind special variable to a specified term
   *
   * Calls to this method must happen before calls to any
   * other methods. Also no special variables can occur in
   * binding term, as no occur-check is performed.
   */
  void bindSpecialVar(unsigned var, TermList t, int index)
  {
    VarSpec vs(var, SPECIAL_INDEX);
    ASS(!_bank.find(vs));
    bind(vs, TermSpec(t,index));
  }
  TermList::Top getSpecialVarTop(unsigned specialVar) const;
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
  Stack<Literal*> apply(Stack<Literal*> cl, int index) const;
  size_t getApplicationResultWeight(TermList t, int index) const;
  size_t getApplicationResultWeight(Literal* lit, int index) const;

#if VDEBUG
  /**
   * Return number of bindings stored in the substitution.
   *
   * - 0 means a fresh substitution.
   * - Without backtracking, this number doesn't decrease.
   */
  size_t size() const {return _bank.size(); }

#endif
  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self);
  std::ostream& output(std::ostream& out, bool deref) const;

  typedef pair<TermSpec,TermSpec> TTPair;
 
  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self)
  {
    if(self.index == SPECIAL_INDEX) {
      return out << "S" << self.var;
    } else {
      return out << "X" << self.var << "/" << self.index;
    }
  }


  RobSubstitution(RobSubstitution&& obj) = default;
  RobSubstitution& operator=(RobSubstitution&& obj) = default;
private:
  TermList apply(TermSpec);
  friend class TermSpec;
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;


  static const int UNBOUND_INDEX;
  static const int SPECIAL_INDEX;

  bool isUnbound(VarSpec v) const;
  TermSpec const& deref(VarSpec v) const;
  TermSpec const& derefBound(TermSpec const& v) const;

  void addToConstraints(const VarSpec& v1, const VarSpec& v2);
  void bind(const VarSpec& v, TermSpec b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v) const;
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2);
  bool occurs(VarSpec const& vs, TermSpec const& ts);

  // VarSpec getVarSpec(TermList tl, int index) const
  // {
  //   CALL("RobSubstitution::getVarSpec");
  //   ASS(tl.isVar());
  //   index = tl.isSpecialVar() ? SPECIAL_INDEX : index;
  //   return VarSpec(tl.var(), index);
  // }

  typedef DHMap<VarSpec,TermSpec,VarSpec::Hash1, VarSpec::Hash2> BankType;

  BankType _bank;
  mutable unsigned _nextUnboundAvailable;

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self)
  { return out << self._bank; }

  class BindingBacktrackObject
  : public BacktrackObject
  {
  public:
    BindingBacktrackObject(RobSubstitution* subst, VarSpec v)
    :_subst(subst), _var(v)
    {
      Option<TermSpec&> t = _subst->_bank.find(_var);
      if(t) {
        _term = some(t->clone());
      }
    }
    void backtrack()
    {
      if(_term.isNone()) {
	      _subst->_bank.remove(_var);
      } else {
	      _subst->_bank.set(_var,std::move(*_term));
      }
    }
    friend std::ostream& operator<<(std::ostream& out, BindingBacktrackObject const& self)
    { return out << "(ROB backtrack object for " << self._var << ")"; }
    CLASS_NAME(RobSubstitution::BindingBacktrackObject);
    USE_ALLOCATOR(BindingBacktrackObject);
  private:
    RobSubstitution* _subst;
    VarSpec _var;
    Option<TermSpec> _term;
  };

  template<class Fn>
  SubstIterator getAssocIterator(RobSubstitution* subst,
    Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  template<class Fn>
  struct AssocContext;
  template<class Fn>
  class AssocIterator;

  struct MatchingFn;
  struct UnificationFn;

};

};

namespace Lib {

  // TODO optimize to use TermList iterator
  template<>
  // struct BottomUpChildIter<pair<Kernel::TermSpec, Kernel::RobSubstitution const*>>
  struct BottomUpChildIter<Kernel::AutoDerefTermSpec>
  {
    using Item = Kernel::AutoDerefTermSpec;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self) : _self(Item(self)), _arg(0) {}
 
    Item self() { return _self.clone(); }

    Item next()
    { return Kernel::AutoDerefTermSpec(_self.term.anyArg(_arg++), _self.subs); }

    bool hasNext()
    { return _self.term.isTerm() && _arg < _self.term.nAllArgs(); }

    unsigned nChildren()
    { return _self.term.isVar() ? 0 : _self.term.nAllArgs(); }
  };

} // namespace Lib

#endif /*__RobSubstitution__*/

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
#include "Kernel/Polynomial.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"

#if VDEBUG
#include <iostream>
#include "Lib/VString.hpp"
#endif


const int SPECIAL_INDEX=-2;
const int UNBOUND_INDEX=-1;
namespace Kernel
{
struct VarSpec
{
  /** Create a new VarSpec struct */
  VarSpec() {}
  /** Create a new VarSpec struct */
  VarSpec(unsigned var, int index) : var(var), index(index) {}

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self);

  /** number of variable */
  unsigned var;
  /** index of variable bank */
  int index;

  auto asTuple() const { return std::tie(var, index); }
  IMPL_COMPARISONS_FROM_TUPLE(VarSpec)
  IMPL_HASH_FROM_TUPLE(VarSpec)

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

struct AtomicTermSpec {
  AtomicTermSpec() {}
  AtomicTermSpec(TermList t, int i) : term(t), index(i) {}
  auto asTuple() const -> decltype(auto) { return std::tie(term, index); }
  IMPL_COMPARISONS_FROM_TUPLE(AtomicTermSpec)
  IMPL_HASH_FROM_TUPLE(AtomicTermSpec)

  TermList term;
  int index;

  bool sameTermContent(const AtomicTermSpec& ts)
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

  friend std::ostream& operator<<(std::ostream& out, AtomicTermSpec const& self);
  AtomicTermSpec clone() const { return *this; }
  bool isVar() const { return term.isVar(); }
  VarSpec varSpec() const { return VarSpec(term.var(), term.isSpecialVar() ? SPECIAL_INDEX : index); }
  bool isTerm() const { return term.isTerm(); }

  unsigned nTypeArgs() const { return term.term()->numTermArguments(); }
  unsigned nTermArgs() const { return term.term()->numTermArguments(); }
  unsigned nAllArgs() const { return term.term()->arity(); }

  AtomicTermSpec termArg(unsigned i) const { return AtomicTermSpec(this->term.term()->termArg(i), this->index); }
  AtomicTermSpec typeArg(unsigned i) const { return AtomicTermSpec(this->term.term()->typeArg(i), this->index); }
  AtomicTermSpec anyArg (unsigned i) const { return AtomicTermSpec(*this->term.term()->nthArgument(i), this->index); }

  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs()  const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }


  unsigned functor() const { return term.term()->functor(); }
};

class TermSpec;

// TODO get rid of implicit copying of this
struct CompositeTermSpec {
  unsigned functor;
  Option<Recycled<Stack<TermSpec>>> args;
  auto asTuple() const -> decltype(auto) { return std::tie(functor, args); }
  IMPL_COMPARISONS_FROM_TUPLE(CompositeTermSpec)
  IMPL_HASH_FROM_TUPLE(CompositeTermSpec)
  bool isSort() const { return false; }

  CompositeTermSpec(CompositeTermSpec&&) = default;
  CompositeTermSpec& operator=(CompositeTermSpec&&) = default;

  TermSpec const& arg(unsigned i) const { return (**args)[i]; }

  auto argsIter() const 
  { return iterTraits(args.iter())
                .flatMap([](auto& args) { return arrayIter(*args); }); }

  CompositeTermSpec clone() const 
  { return CompositeTermSpec { .functor = functor, 
                  .args = args.map([](auto& x) { 
                      return x.clone([](auto& to, auto const& from) { 
                          to.loadFromIterator(
                              arrayIter(from)
                                .map([](auto& c){ return c.clone(); })); 
                          }); 
                      }), 
                }; }
};


class TermSpec
{
  using Copro = Coproduct<
    CompositeTermSpec,
    AtomicTermSpec
    >;
  Copro _self;
  friend class UnificationConstraint;
  friend class RobSubstitution;

  TermSpec(TermSpec const&) = delete;
  TermSpec(Copro self) : _self(std::move(self)) {}
public:
  TermSpec(TermSpec&&) = default;
  TermSpec(AtomicTermSpec self) : TermSpec(Copro(self)) {}
  TermSpec& operator=(TermSpec&&) = default;
  AtomicTermSpec old() const { return _self.unwrap<AtomicTermSpec>(); }
  // TODO get rid of default constructor
  TermSpec() : TermSpec(decltype(_self)(AtomicTermSpec())) {}
  TermSpec(VarSpec v) : TermSpec(TermList::var(v.var), v.index) {}
  TermSpec(TermList self, int index) : _self(AtomicTermSpec(self, index)) {}

  friend bool operator==(TermSpec const& lhs, TermSpec const& rhs);
  friend bool operator<(TermSpec const& lhs, TermSpec const& rhs);
  IMPL_COMPARISONS_FROM_LESS_AND_EQUALS(TermSpec);

  Option<AtomicTermSpec> asAtomic() const { return _self.as<AtomicTermSpec>().toOwned(); }

  TermList unwrapGround() const
  { return _self.match(
      [](CompositeTermSpec const& t) { return TermList(Term::createFromIter(t.functor, t.argsIter().map([](auto& arg) { return arg.unwrapGround(); }))); },
      [](AtomicTermSpec const& t) { ASS(t.term.ground()); return t.term; }); }

  unsigned groundWeight() const
  { return _self.match(
      [](CompositeTermSpec const& t) { return 1 + t.argsIter().map([](auto& arg) { return arg.groundWeight(); }).sum(); },
      [](AtomicTermSpec const& t) { ASS(t.term.ground()); return t.term.weight(); }); }

  template<class Deref>
  static int compare(TermSpec const& lhs, TermSpec const& rhs, Deref deref) {
    Recycled<Stack<std::pair<TermSpec, TermSpec>>> todo;
    todo->push(std::make_pair(lhs.clone(),rhs.clone()));
    // DBG("compare: ", lhs, " <> ", rhs)
    while (todo->isNonEmpty()) {
      auto lhs_ = std::move(todo->top().first);
      auto rhs_ =           todo->pop().second;
      auto& lhs = deref(lhs_);
      auto& rhs = deref(rhs_);

      if (lhs.isTerm() != rhs.isTerm()) {
        return lhs.isVar() ? -1 : 1;

      } else {
        if (lhs.isTerm()) {
          if (lhs.functor() != rhs.functor()) {
            return lhs.functor() < rhs.functor() ? -1 : 1;
          } else {
            todo->loadFromIterator(lhs.allArgs().zip(rhs.allArgs()));
          }
        } else {
          ASS(lhs.isVar() && rhs.isVar())
          auto v1 = lhs.varSpec();
          auto v2 = rhs.varSpec();
          if (v1 != v2) {
            return std::tie(v1.var, v1.index) < std::tie(v2.var, v2.index) ? -1 : 1;
          }
        }
      }
    }
    return 0;
  }


  TermSpec clone() const { return TermSpec(_self.clone()); }
  
  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self);


  template<class... Args>
  TermSpec(unsigned functor, Args... args) 
    : _self(CompositeTermSpec{functor, someIf(sizeof...(args) != 0, []() { return Recycled<Stack<TermSpec>>(); }) }) 
  {
    ASS_EQ(sizeof...(args), env.signature->getFunction(functor)->arity())
    if (sizeof...(args) != 0) {
      _self.template unwrap<CompositeTermSpec>().args.unwrap()->pushMany(std::move(args)...);
    }
  }

  TermList::Top top() const
  { return _self.match([](CompositeTermSpec const& a) { return TermList::Top::functor(a.functor); },
                       [](AtomicTermSpec const& old) { return old.term.top(); }); }
  // TermSpec const& deref(RobSubstitution const* s) const&;
  unsigned varNumber() const { return *top().var(); }
  bool definitelyGround() const
  { return _self.match([](CompositeTermSpec const& a) { return iterTraits(a.argsIter()).all([](auto& x) { return x.definitelyGround(); }); },
                       [](AtomicTermSpec const& t) { return t.term.isTerm() && t.term.term()->shared() && t.term.term()->ground(); }); }
    // assuming it's ground
  unsigned weight() const;
  bool sameTermContent(TermSpec const& other) const;

  bool isSpecialVar()  const;
  bool isVar()         const
  { return _self.match([](CompositeTermSpec const&)   { return false; },
                       [](AtomicTermSpec const& self) { return self.isVar(); }); }

  bool isNormalVar()   const { return isVar() && !isSpecialVar(); }

  bool isTerm() const
  { return _self.match([](CompositeTermSpec const&)   { return true; },
                       [](AtomicTermSpec const& self) { return self.isTerm(); }); }

  bool isLiteral() const;
  // TermSpec sort() const;
  bool sortIsBoolOrVar() const;
  bool isSort() const;
  VarSpec varSpec() const { return _self.as<AtomicTermSpec>()->varSpec(); }

  unsigned functor() const
  { return _self.match([](CompositeTermSpec const& a) { return a.functor; },
                       [](AtomicTermSpec const& self) { return self.functor(); }); }

  unsigned nTypeArgs() const
  { return _self.match([](CompositeTermSpec const& a) { return env.signature->getFunction(a.functor)->numTypeArguments(); },
                       [](AtomicTermSpec const& self) { return self.nTypeArgs(); }); }

  unsigned nTermArgs() const
  { return _self.match([](CompositeTermSpec const& a) { return env.signature->getFunction(a.functor)->numTermArguments(); },
                       [](AtomicTermSpec const& self) { return self.nTermArgs(); }); }

  unsigned nAllArgs() const
  { return _self.match([](CompositeTermSpec const& a) { return a.args.map([](auto& x) { return unsigned(x->size()); }).unwrapOr(0); },
                       [](AtomicTermSpec const& self) { return self.nAllArgs(); }); }

  bool isNumeral() const { return isTerm() && env.signature->getFunction(functor())->interpretedNumber(); }

  TermSpec termArg(unsigned i) const
  { return _self.match([&](CompositeTermSpec const& a) { return a.arg(i + nTypeArgs()).clone(); },
                       [&](AtomicTermSpec const& self) { return TermSpec(self.termArg(i)); }); }

  TermSpec typeArg(unsigned i) const
  { return _self.match([&](CompositeTermSpec const& a) { return a.arg(i).clone(); },
                       [&](AtomicTermSpec const& self) { return TermSpec(self.typeArg(i)); }); }

  TermSpec anyArg(unsigned i) const
  { return _self.match([&](CompositeTermSpec const& a) { return a.arg(i).clone(); },
                       [&](AtomicTermSpec const& self) { return TermSpec(self.anyArg(i)); }); }

  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs() const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }

  TermList toTerm(RobSubstitution& s) const;

private:
  template<class HashFn>
  static unsigned __hash(HashFn hashFn, TermSpec const& t) {
    Recycled<Stack<TermSpec>> todo;
    todo->push(t.clone());
    unsigned hash = 0;
    while (todo->isNonEmpty()) {
      auto t = todo->pop();
      if (t.isTerm()) {
        hash = HashUtils::combine(hash, hashFn(t.functor()));
        todo->loadFromIterator(t.allArgs());
      } else {
        hash = HashUtils::combine(hash, t.varNumber(), t.varSpec().index);
      }
    }
    return 0;
  }
public:


  unsigned defaultHash () const { return __hash([](auto const& x) { return DefaultHash ::hash(x); }, *this); }
  unsigned defaultHash2() const { return __hash([](auto const& x) { return DefaultHash2::hash(x); }, *this); }


};

struct AutoDerefTermSpec
{
  TermSpec term;

  AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s);
  explicit AutoDerefTermSpec(AutoDerefTermSpec const& other) : term(other.term.clone()) {}
  AutoDerefTermSpec clone() const { return AutoDerefTermSpec(*this); }
  AutoDerefTermSpec(AutoDerefTermSpec && other) = default;
  friend std::ostream& operator<<(std::ostream& out, AutoDerefTermSpec const& self);
};

struct AutoDerefTermSpecContext 
{
  RobSubstitution const* subs;
};

// // memo for AutoDerefTermSpec that will only memorize AtomicTermSpec but not CompositeTermSpec 
// template<class Result>
// class OnlyMemorizeAtomic {
//   Map<AtomicTermSpec, Result> _memo;
// public:
//   OnlyMemorizeAtomic(OnlyMemorizeAtomic &&) = default;
//   OnlyMemorizeAtomic& operator=(OnlyMemorizeAtomic &&) = default;
//   OnlyMemorizeAtomic() : _memo() {}
//
//   Option<Result> get(AutoDerefTermSpec const& arg)
//   { return arg.term.asAtomic().isSome() 
//        ? _memo.tryGet(*arg.term.asAtomic()).toOwned()
//        : Option<Result>(); }
//
//   template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
//   { return orig.term.asAtomic().isSome() ? _memo.getOrInit(*orig.term.asAtomic(), init)
//                                            : init(); }
//   void reset() { _memo.reset(); }
// };

template<class Result, unsigned SIZE>
class OnlyMemorizeBigAtomic {
  Map<AtomicTermSpec, Result> _memo;
public:
  OnlyMemorizeBigAtomic(OnlyMemorizeBigAtomic &&) = default;
  OnlyMemorizeBigAtomic& operator=(OnlyMemorizeBigAtomic &&) = default;
  OnlyMemorizeBigAtomic() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<AtomicTermSpec>
  { 
    auto at = arg.term.asAtomic(); 
    if (at.isSome() && at->term.isTerm()) {
      auto term = at->term.term();
      return !term->shared() || term->weight() > SIZE ? at : Option<AtomicTermSpec>{};
    } else {
      return {};
    }
  }

  Option<Result> get(AutoDerefTermSpec const& arg)
  { 
    auto key = memoKey(arg);
    return key.isSome()
       ? _memo.tryGet(*key).toOwned()
       : Option<Result>(); 
  }

  template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
  { 
    auto key = memoKey(orig);
    return key.isSome() ? _memo.getOrInit(*key, init)
                        : init(); 
  }
  void reset() { _memo.reset(); }
};


template<class Result>
class OnlyMemorizeAtomicNonVar {
  Map<AtomicTermSpec, Result> _memo;
public:
  OnlyMemorizeAtomicNonVar(OnlyMemorizeAtomicNonVar &&) = default;
  OnlyMemorizeAtomicNonVar& operator=(OnlyMemorizeAtomicNonVar &&) = default;
  OnlyMemorizeAtomicNonVar() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<AtomicTermSpec>
  { 
    auto at = arg.term.asAtomic(); 
    if (at.isSome() && at->term.isTerm()) {
      return at;
    } else {
      return {};
    }
  }

  Option<Result> get(AutoDerefTermSpec const& arg)
  { 
    auto key = memoKey(arg);
    return key.isSome()
       ? _memo.tryGet(*key).toOwned()
       : Option<Result>(); 
  }

  template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
  { 
    auto key = memoKey(orig);
    return key.isSome() ? _memo.getOrInit(*key, init)
                        : init(); 
  }
  void reset() { _memo.reset(); }
};

// template<class Result>
// class OnlyMemorizeVars {
//   Map<VarSpec, Result> _memo;
// public:
//   OnlyMemorizeVars(OnlyMemorizeVars &&) = default;
//   OnlyMemorizeVars& operator=(OnlyMemorizeVars &&) = default;
//   OnlyMemorizeVars() : _memo() {}
//
//   Option<Result> get(AutoDerefTermSpec const& arg)
//   { return arg.term.isVar()
//        ? _memo.tryGet(arg.term.varSpec()).toOwned()
//        : Option<Result>(); }
//
//   template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
//   { return orig.term.isVar() ? _memo.getOrInit(orig.term.varSpec(), init)
//                              : init(); }
//   void reset() { _memo.reset(); }
// };
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
 
  DHMap<VarSpec, TermSpec, VarSpec::Hash1, VarSpec::Hash2> _bindings;
  mutable DHMap<VarSpec, unsigned , VarSpec::Hash1, VarSpec::Hash2> _outputVarBindings;
  mutable unsigned _nextUnboundAvailable;
  mutable OnlyMemorizeAtomicNonVar<TermList> _applyMemo;
  // mutable OnlyMemorizeAtomic<TermList> _applyMemo;
  // mutable OnlyMemorizeBigAtomic<TermList, 4> _applyMemo;

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
  bool isUnbound(VarSpec v) const;

  void reset()
  {
    _bindings.reset();
    _outputVarBindings.reset();
    _nextUnboundAvailable=0;
    _applyMemo.reset();
  }
  bool keepRecycled() const { return _bindings.keepRecycled() || _outputVarBindings.keepRecycled(); }

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
    ASS(!_bindings.find(vs));
    bind(vs, TermSpec(t,index));
  }

  TermList::Top getSpecialVarTop(unsigned specialVar) const;
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
  TypedTermList apply(TypedTermList t, int index) const { return TypedTermList(apply(TermList(t), index), apply(t.sort(), index)); }
  Stack<Literal*> apply(Stack<Literal*> cl, int index) const;
  size_t getApplicationResultWeight(TermList t, int index) const;
  size_t getApplicationResultWeight(Literal* lit, int index) const;

  bool isEmpty() const { return _bindings.size() == 0 && _outputVarBindings.size() == 0; }

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self);
  std::ostream& output(std::ostream& out, bool deref) const;

  typedef std::pair<TermSpec,TermSpec> TTPair;
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
  TermSpec const& derefBound(TermSpec const& v) const;
  // TermSpec const& derefIntroducingNewVariables(VarSpec v) const;
  unsigned findOrIntroduceOutputVariable(VarSpec v) const;
  VarSpec root(VarSpec v) const;
private:
  TermList apply(TermSpec);
  friend class TermSpec;
  friend struct AtomicTermSpec;
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;


  void addToConstraints(const VarSpec& v1, const VarSpec& v2);
  template<class T, class H1, class H2>
  void bind(DHMap<VarSpec, T, H1, H2>& map, const VarSpec& v, T b);
  void bind(const VarSpec& v, TermSpec b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  bool match(TermSpec base, TermSpec instance);
  bool unify(AtomicTermSpec t1, AtomicTermSpec t2);
  bool occurs(VarSpec const& vs, AtomicTermSpec const& ts);

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self)
  { return out << "(" << self._bindings << ", " << self._outputVarBindings << ")"; }

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


inline AutoDerefTermSpec::AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s) : term(s->derefBound(t).clone()) {}
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

    BottomUpChildIter(Item const& self, Kernel::AutoDerefTermSpecContext c) : _self(Item(self)), _arg(0) {}
 
    Item const& self() { return _self; }

    Item next(Kernel::AutoDerefTermSpecContext c)
    { return Kernel::AutoDerefTermSpec(_self.term.anyArg(_arg++), c.subs); }

    bool hasNext(Kernel::AutoDerefTermSpecContext c)
    { return _self.term.isTerm() && _arg < _self.term.nAllArgs(); }

    unsigned nChildren(Kernel::AutoDerefTermSpecContext c)
    { return _self.term.isTerm() ? _self.term.nAllArgs() : 0; }
  };

} // namespace Lib

#endif /*__RobSubstitution__*/

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
#include "Kernel/TypedTermList.hpp"

#if VDEBUG
#include <iostream>
#endif


const int GLUE_INDEX=-2;
const int UNBOUND_INDEX=-1;

namespace Kernel
{

struct VarSpec
{
  VarSpec() {}
  VarSpec(TermList var, int index) : _self(var), index(index) { ASS(var.isVar()) }

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self);

  TermList _self;
  /** index of variable bank */
  int index;
  bool special() const { return _self.isSpecialVar(); }
  unsigned var() const { return _self.var(); }
  TermList varAsTermlist() const { return TermList::var(var(), special()); }

  auto asTuple() const { return std::tie(_self, index); }
  IMPL_COMPARISONS_FROM_TUPLE(VarSpec)

  unsigned defaultHash () const { return HashUtils::combine(_self.content(), index); }
  unsigned defaultHash2() const { return HashUtils::combine(index, _self.content()); }
};

struct TermSpec {
  TermSpec() {}

  TermSpec(TermList t, int i) : term(t), index(t.isTerm() && t.term()->shared() && t.ground() ? 0 : i) {}
  TermSpec(VarSpec v) : term(v.varAsTermlist()), index(v.index) {}

  auto asTuple() const -> decltype(auto) { return std::tie(term, index); }
  IMPL_COMPARISONS_FROM_TUPLE(TermSpec)
  IMPL_HASH_FROM_TUPLE(TermSpec)

  TermList term;
  int index;
  bool sameTermContent(const TermSpec& ts) const
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

  TermSpec sort() const { return TermSpec(SortHelper::getResultSort(term.term()), index); }

  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self);

  bool isVar() const { return term.isVar(); }
  VarSpec varSpec() const { return VarSpec(term, index); }
  bool isTerm() const { return term.isTerm(); }

  TermSpec termArgSort(unsigned i) const { return TermSpec(SortHelper::getTermArgSort(term.term(), i), index); }
  TermSpec anyArgSort(unsigned i) const { return TermSpec(SortHelper::getArgSort(term.term(), i), index); }

  unsigned nTypeArgs() const { return term.term()->numTypeArguments(); }
  unsigned nTermArgs() const { return term.term()->numTermArguments(); }
  unsigned nAllArgs() const { return term.term()->arity(); }

  // TODO remove unnecessary function call
  TermSpec termArg(unsigned i) const { return TermSpec(this->term.term()->termArg(i), this->index); }
  TermSpec typeArg(unsigned i) const { return TermSpec(this->term.term()->typeArg(i), this->index); }
  TermSpec anyArg (unsigned i) const { return TermSpec(*this->term.term()->nthArgument(i), this->index); }

  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs()  const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }

  bool deepEqCheck(const TermSpec& t2) const {
    TermSpec const& t1 = *this;
    if (t1.term.sameContent(t2.term)) {
      return t1.isVar() ? t1.index == t2.index 
                        : (t1.index == t2.index || t1.term.term()->ground());
    } else {
      if (t1.isTerm() != t2.isTerm()) return false;
      if (t1.isVar()) {
        ASS(t2.isVar() && (t1.term.var() != t2.term.var() || t1.term.isSpecialVar() != t2.term.isSpecialVar()))
        return false;
      }
      return t1.functor() == t2.functor() 
        && t1.allArgs().zip(t2.allArgs()).all([](auto pair) { return pair.first.deepEqCheck(pair.second); });
    }
  }


  TermList::Top top() const { return this->term.top(); }
  unsigned functor() const { return term.term()->functor(); }

  TermList toTerm(Kernel::RobSubstitution& s) const;


  bool isSort() const
  { return this->term.term()->isSort(); }

  bool sortIsBoolOrVar() const
  { 
    if (!isTerm()) return false;
    auto fun = env.signature->getFunction(functor());
    auto op = fun->fnType();
    TermList res = op->result();
    return res.isVar() || res == AtomicSort::boolSort();
  }

  bool isNumeral() const { return theory->isInterpretedNumber(this->term); }

  bool definitelyGround() const 
  { return this->term.isTerm() 
        && this->term.term()->shared() 
        && this->term.term()->ground(); }

  unsigned groundWeight() const 
  {
    ASS(definitelyGround())
    return this->term.weight();
  }

  template<class Deref>
  static int compare(TermSpec const& lhs, TermSpec const& rhs, Deref deref) {
    Recycled<Stack<std::pair<TermSpec, TermSpec>>> todo;
    todo->push(std::make_pair(lhs,rhs));
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
            return v1.asTuple() < v2.asTuple() ? -1 : 1;
          }
        }
      }
    }
    return 0;
  }
};

/** A wrapper around TermSpec that automatically dereferences the TermSpec with respect to some RobSubstition when 
 * used with BottomUpEvaluation.  This means for example if we evaluate some TermSpec * `g(X, Y)` in a context 
 * `{ X -> a, Y -> f(X) }` it behaves as if we would evaluate `g(a,f(a))`.  */
struct AutoDerefTermSpec
{
  TermSpec term;

  AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s);
  explicit AutoDerefTermSpec(AutoDerefTermSpec const& other) : term(other.term) {}
  AutoDerefTermSpec(AutoDerefTermSpec && other) = default;
  friend std::ostream& operator<<(std::ostream& out, AutoDerefTermSpec const& self);

  struct Context 
  { RobSubstitution const* subs; };
};

/* a Memo to be used with BottomUpEvaluation and AutoDerefTermSpec that only memorizes the result for non-variable subterms. */
template<class Result>
class OnlyMemorizeNonVar 
{
  Map<TermSpec, Result> _memo;
public:
  OnlyMemorizeNonVar(OnlyMemorizeNonVar &&) = default;
  OnlyMemorizeNonVar& operator=(OnlyMemorizeNonVar &&) = default;
  OnlyMemorizeNonVar() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<TermSpec>
  { 
    if (arg.term.term.isTerm()) {
      return some(arg.term);
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

class UnificationConstraint
{
  TermSpec _t1;
  TermSpec _t2;
  TermSpec _sort;
public:
  UnificationConstraint() {}
  USE_ALLOCATOR(UnificationConstraint)
  auto asTuple() const -> decltype(auto) { return std::tie(_t1, _t2, _sort); }
  IMPL_COMPARISONS_FROM_TUPLE(UnificationConstraint);
  IMPL_HASH_FROM_TUPLE(UnificationConstraint);

  UnificationConstraint(TermSpec t1, TermSpec t2, TermSpec sort)
  : _t1(std::move(t1)), _t2(std::move(t2)), _sort(std::move(sort))
  {}

  Option<Literal*> toLiteral(RobSubstitution& s);

  TermSpec const& lhs() const { return _t1; }
  TermSpec const& rhs() const { return _t2; }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint const& self)
  { return out << self._t1 << " ?= " << self._t2; }
};

using namespace Lib;

class AbstractingUnifier;
class UnificationConstraint;

class RobSubstitution
:public Backtrackable
{
  friend class AbstractingUnifier;
  friend class UnificationConstraint;
 
  DHMap<VarSpec, TermSpec> _bindings;
  mutable DHMap<VarSpec, unsigned> _outputVarBindings;
  mutable bool _startedBindingOutputVars;
  mutable unsigned _nextUnboundAvailable;
  mutable unsigned _nextGlueAvailable;
  DHMap<TermSpec, unsigned> _gluedTerms;
  mutable OnlyMemorizeNonVar<TermList> _applyMemo;

public:
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() 
    : _startedBindingOutputVars(false)
    , _nextUnboundAvailable(0) 
    , _nextGlueAvailable(0) 
    , _gluedTerms() 
  {}

  SubstIterator matches(Literal* base, int baseIndex,
	  Literal* instance, int instanceIndex, bool complementary);
  SubstIterator unifiers(Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  bool unify(TermList t1,int index1, TermList t2, int index2);
  bool match(TermList base,int baseIndex, TermList instance, int instanceIndex);

  bool unifyArgs(Term* t1,int index1, Term* t2, int index2);
  bool matchArgs(Term* base,int baseIndex, Term* instance, int instanceIndex);

  void denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex);
  bool isUnbound(VarSpec v) const;

  /** introduces a new "glue" variable, and binds it to forTerm. 
   * Glue variables live in their own namespace that is only used within this rob substitution. They are used only to represent subterms of other terms in the substitution.
   * This is useful in cases where we want to create terms that contain two subterms of different variable banks in e.g. Unification with Abstraction:
   *
   * Say we want to unify
   * x + f(y)    <- var bank 0
   * and   
   * f(y)        <- var bank 1
   *
   * Then an mgu is x -> -f(y/0) + f(y/1)
   * This cannot be directly represented in vampire as our TermSpec can only hold 1 variable bank per term, and not multiple per subterm. So what we want to do instead 
   * is introduce two new "glue" variables variables G0, G1
   *
   * G0 -> -f(y)/0
   * G1 ->  f(y)/1
   *
   * and return as mgu
   * {x -> G0 + G1, G0 -> -f(y)/0, G1 -> f(y)/1}
   */
  VarSpec introGlueVar(TermSpec forTerm);

  /* TODO */
  TermSpec createTerm(unsigned functor)
  { return TermSpec(TermList(Term::create(functor, 0, nullptr)), /* index */ 0); }


  /* TODO */
  template<class Iter>
  TermSpec createTermFromIter(unsigned functor, Iter iter)
  {
    TermSpec out;
    if (!iter.hasNext()) {
      return TermSpec(TermList(Term::create(functor, 0, nullptr)), /* index */ 0);
    }
    Recycled<Stack<TermList>> args;
    Option<int> index;
    while (iter.hasNext()) {
      auto arg = iter.next();
      if (// ground term
          (!arg.term.isVar() && arg.term.term()->shared() && arg.term.ground())
          ) {
        args->push(arg.term);

      } else if (index.isNone()) {
        args->push(arg.term);
        index = some(arg.index);

      } else if (*index == GLUE_INDEX) {
        args->push(arg.index == GLUE_INDEX 
                    ? arg.term 
                    : introGlueVar(arg).varAsTermlist());
      } else {
        if (arg.index == *index) {
          args->push(arg.term);
        } else {
          // two different indices present
          for (auto i : range(0, args->size())) {
            (*args)[i] = introGlueVar(TermSpec((*args)[i], *index)).varAsTermlist();
          }
          index = some(GLUE_INDEX);
          args->push(introGlueVar(arg).varAsTermlist());
        }
      }
    }
    return TermSpec(TermList(Term::create(functor, args->size(), args->begin())), index.unwrapOr(0));
  }

  /* creates a new TermSpec with the given arguments `args` which all need to be of type `TermSpec`. If any of the arguments have different variable banks "glue" variable are introduced. See the function `introGlueVar` for that. */
  template<class... Args>
  TermSpec createTerm(unsigned functor, Args... args)
  {
    return createTermFromIter(functor, iterItems(args...));
  }

  void reset()
  {
    _bindings.reset();
    _outputVarBindings.reset();
    _startedBindingOutputVars = false;
    _nextUnboundAvailable=0;
    _nextGlueAvailable=0;
    _gluedTerms.reset();
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
  void bindSpecialVar(unsigned var, unsigned internalBank, TermList t, int index)
  {
    VarSpec vs(TermList::var(var, /* special */ true), internalBank);
    ASS(!_bindings.find(vs));
    bind(vs, TermSpec(t,index));
  }

  TermList::Top getSpecialVarTop(unsigned specialVar, unsigned index) const;
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
  TypedTermList apply(TypedTermList t, int index) const { return TypedTermList(apply(TermList(t), index), apply(t.sort(), index)); }
  Stack<Literal*> apply(Stack<Literal*> cl, int index) const;
  size_t getApplicationResultWeight(TermList t, int index) const;
  size_t getApplicationResultWeight(Literal* lit, int index) const;

  bool isEmpty() const { return _bindings.size() == 0 && _outputVarBindings.size() == 0; }

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self);
  std::ostream& output(std::ostream& out, bool deref) const;

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self)
  {
    if(self.index == GLUE_INDEX) {
      return out << "G" << (self.special() ? "S" : "") << self.var();

    } else if(self.index == UNBOUND_INDEX) {
      return out << "U" << (self.special() ? "S" : "") << self.var();

    } else {
      return out << (self.special() ? "S" : "X") << self.var() << "/" << self.index;
    }
  }


  RobSubstitution(RobSubstitution&& obj) = default;
  RobSubstitution& operator=(RobSubstitution&& obj) = default;
  TermSpec const& derefBound(TermSpec const& v) const;
  unsigned findOrIntroduceOutputVariable(VarSpec v) const;
private:
  TermList apply(TermSpec);
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;

  template<class T, class H1, class H2>
  void bind(DHMap<VarSpec, T, H1, H2>& map, const VarSpec& v, T b);
  void bind(const VarSpec& v, TermSpec b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2);
  bool occurs(VarSpec const& vs, TermSpec const& ts);

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

inline AutoDerefTermSpec::AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s) : term(s->derefBound(t)) {}

};

namespace Lib {
  template<>
  struct BottomUpChildIter<Kernel::AutoDerefTermSpec>
  {
    using Item = Kernel::AutoDerefTermSpec;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self, Kernel::AutoDerefTermSpec::Context c) : _self(Item(self)), _arg(0) {}
 
    Item const& self() { return _self; }

    Item next(Kernel::AutoDerefTermSpec::Context c)
    { return Kernel::AutoDerefTermSpec(_self.term.anyArg(_arg++), c.subs); }

    bool hasNext(Kernel::AutoDerefTermSpec::Context c)
    { return _self.term.isTerm() && _arg < _self.term.nAllArgs(); }

    unsigned nChildren(Kernel::AutoDerefTermSpec::Context c)
    { return _self.term.isTerm() ? _self.term.nAllArgs() : 0; }
  };

} // namespace Lib

#endif /*__RobSubstitution__*/

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

template<class TermSpecOrList, class VarBankOrInt>
class RobSubstitution;

struct TermSpec { // for backwards compatibility
  static const int UNBOUND_INDEX;
  static const int SPECIAL_INDEX;  
  
  TermSpec() {}
  TermSpec(TermList t, int i) : trm(t), index(i) {}
  TermSpec(unsigned v, int i) : index(i) {
    if(i == SPECIAL_INDEX){
      trm = TermList(v, true); // special variable
    } else {
      trm = TermList(v, false); // standard variable
    }
  }

  auto asTuple() const -> decltype(auto) { return std::tie(trm, index); }
  IMPL_COMPARISONS_FROM_TUPLE(TermSpec)
  IMPL_HASH_FROM_TUPLE(TermSpec)

  bool sameContent(const TermSpec& ts)
  {
    bool termSameContent=trm.sameContent(&ts.trm);
    return termSameContent && (index==ts.index || trm.isSpecialVar() ||
      (trm.isTerm() && (
        (trm.term()->shared() && trm.term()->ground()) ||
         trm.term()->arity()==0 )));
  }

  static bool equals(TermSpec t1, TermSpec t2){
    return t1.index == t2.index && TermList::equals(t1.trm, t2.trm);
  }

  TermList trm;
  int index;

  int bank() const { return index; }
  bool isVar() const { return trm.isVar(); }
  bool isSpecialVar() const { return trm.isSpecialVar(); }
  bool isOrdinaryVar() const { return trm.isOrdinaryVar(); }
  bool isTerm() const { return trm.isTerm(); }
  bool isOutputVar() const { return isVar() && index == UNBOUND_INDEX; }
#if VHOL
  bool containsLooseIndex() const { return trm.containsLooseIndex(); }
#endif
  bool onBank() const { return true; } // always on a bank
  unsigned var() const {  ASS(trm.isVar()); return trm.var(); }
  const Term* term() const { ASS(isTerm());  return trm.term(); }
  TermList::Top top() const { return trm.top(); }

  TermSpec nthArg(unsigned i ) const {
    ASS(isTerm());
    return TermSpec(trm.nthArg(i), index);
  }

  /** WARNING implicit conversion */ 
  operator TermList() const {return trm;}

  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self)
  { return out << self.trm << "/" << self.index;; }

  TermSpec clone() const { return *this; }
};

template<class TermSpecOrList, class VarBankOrInt>
class UnificationConstraint
{
protected:  
  TermSpecOrList _t1;
  TermSpecOrList _t2;

  using Constraint = UnificationConstraint<TermSpecOrList,VarBankOrInt>;  
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;
public:
  // TODO get rid of default constr
  UnificationConstraint() {}
  CLASS_NAME(UnificationConstraint)
  USE_ALLOCATOR(UnificationConstraint)
 
  auto asTuple() const -> decltype(auto) { return std::tie(_t1, _t2); }
  IMPL_COMPARISONS_FROM_TUPLE(UnificationConstraint);
  IMPL_HASH_FROM_TUPLE(UnificationConstraint);

  Constraint  clone() const { return Constraint(lhs(), rhs()); }

  UnificationConstraint(TermSpecOrList t1, TermSpecOrList t2)
  : _t1(t1), _t2(t2)
  {}

  Option<Literal*> toLiteral(RobSubst& s);

  TermSpecOrList const& lhs() const { return _t1; }
  TermSpecOrList const& rhs() const { return _t2; }

  friend std::ostream& operator<<(std::ostream& out, Constraint  const& self)
  { return out << self._t1 << " != " << self._t2; }

};

template<class TermSpecOrList, class VarBankOrInt>
class UnificationConstraintStack
{
  using Constraint = UnificationConstraint<TermSpecOrList,VarBankOrInt>; 
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

  Stack<Constraint> _cont;
public:
  CLASS_NAME(UnificationConstraintStack)
  USE_ALLOCATOR(UnificationConstraintStack)
  UnificationConstraintStack() : _cont() {}
  UnificationConstraintStack(UnificationConstraintStack&&) = default;
  UnificationConstraintStack& operator=(UnificationConstraintStack&&) = default;

  auto iter() const
  { return iterTraits(_cont.iter()); }

  // only require these functions for termlists ...
  Recycled<Stack<Literal*>> literals(RobSubst& s);

  auto literalIter(RobSubst& s)
  { return iterTraits(_cont.iter())
              .filterMap([&](auto& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack<TermSpecOrList, VarBankOrInt> const& self)
  { return out << self._cont; }

  void reset() { _cont.reset(); }
  bool keepRecycled() const { return _cont.keepRecycled() > 0; }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(Constraint c, Option<BacktrackData&> bd);
  Constraint pop(Option<BacktrackData&> bd);
};

using namespace Lib;

namespace UnificationAlgorithms {
  class AbstractingUnification;
  class HOLUnification;
  class HOLInstantiation;
  class HOLGeneralisation;
  class RobUnification;
}

template<class TermSpecOrList, class VarBankOrInt>
class RobSubstitution
:public Backtrackable
{
  friend class UnificationAlgorithms::AbstractingUnification;
  friend class UnificationAlgorithms::HOLUnification;
  friend class UnificationAlgorithms::HOLInstantiation;
  friend class UnificationAlgorithms::HOLGeneralisation;  
  friend class UnificationConstraint<TermSpecOrList, VarBankOrInt>;

  using Constraint = UnificationConstraint<TermSpecOrList,VarBankOrInt>; 
  using ConstraintStack = UnificationConstraintStack<TermSpecOrList,VarBankOrInt>;
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

public:
  CLASS_NAME(RobSubstitution);
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() : _nextUnboundAvailable(0) {}
  virtual ~RobSubstitution() = default;

  /* When a `RobSubstitution` is applied to a Term by default the variables in the resulting
   * Term will be in a new variable index, that starts mapping the first occurring
   * variable in the output to X0, the second one to X1, ....
   * In some cases this behaviour should be changed. For example if we a variables sigma such that
   * `(s)sigma = t` using `RobSubstitution::match` we want that the variables are not assigned to a new
   * index but to the same one as `t`. Therefore this function lets you set the output index of the
   * substitution.
   *
   * Be aware that this is not possible when:
   * - applying the substitution to variables that are not in the output index, that were not bound in the
   *   substitution (i.e. part of generalization operations, etc.)
   * - computing unifications
   */
  void setOutputIndex(VarBankOrInt idx) { _outputIndex = idx; }

  // TODO, in the future create a separate function for applicative FOL unification. Will be cleaner
  /* 
   * In the higher-order case, in some instances we want to carry out first-order applicative unification
   * This the same as first-order unification, but we need an added check to ensure that we never bind a variable
   * to a term that contains a loose index. To use this form of unification, the flag applicativeUnify is added.
   */
  bool unify(TermSpecOrList t1, TermSpecOrList t2
#if VHOL
    , bool applicativeUnify = false
#endif
  );
  bool match(TermSpecOrList base, TermSpecOrList instance, VarBankOrInt baseBank);

  void denormalize(const Renaming& normalizer, VarBankOrInt normBank, VarBankOrInt denormBank);
  bool isUnbound(unsigned var, VarBankOrInt bank) const
  {
    return isUnbound(TermSpecOrList(var, bank));
  }
  void reset()
  {
    _bank.reset();
    _constr->reset();
    _nextUnboundAvailable=0;
    resetOutputIndex();
  }
  
  Recycled<LiteralStack> constraints(){ return _constr->literals(*this); }

  bool keepRecycled() const { return _bank.keepRecycled(); }


  TermList::Top getSpecialVarTop(unsigned specialVar) const;
  Literal* apply(Literal* lit, VarBankOrInt bank) const;
  Stack<Literal*> apply(Stack<Literal*> cl, VarBankOrInt bank) const;
  size_t getApplicationResultWeight(Literal* lit, VarBankOrInt bank) const;
  size_t getApplicationResultWeight(TermSpecOrList t, VarBankOrInt bank) const;
  TermList apply(TermSpecOrList t, VarBankOrInt bank) const;  
  
  virtual TermList apply(TermSpecOrList t) const = 0;
  virtual TermSpecOrList getUnboundVar() const = 0;
  virtual TermSpecOrList getLitArg(Literal* lit, unsigned idx, VarBankOrInt bank) const = 0;
  virtual TermSpecOrList getLitSort(Literal* lit, VarBankOrInt bank) const = 0;
  virtual bool isDefault(VarBankOrInt bank) const = 0;
  virtual void resetOutputIndex() = 0;

  // functions are needed by so many other classes that it is 
  // easier to just make them public rather than adding other
  // classes as friends
  TermSpecOrList deref(TermSpecOrList v) const;
  TermSpecOrList derefBound(TermSpecOrList const& v) const;

#if VDEBUG
  /**
   * Return number of bindings stored in the substitution.
   *
   * - 0 means a fresh substitution.
   * - Without backtracking, this number doesn't decrease.
   */
  size_t size() const {return _bank.size(); }

#endif
  RobSubstitution(RobSubstitution&& obj) = default;
  RobSubstitution& operator=(RobSubstitution&& obj) = default;

  VarBankOrInt outputBank() const { return _outputIndex; }

protected:  
  typedef DHMap<TermSpecOrList,TermSpecOrList> BankType;  
  mutable unsigned _nextUnboundAvailable;
  BankType _bank;
  Recycled<ConstraintStack> _constr;
  bool sameTermContent(TermSpecOrList t1, TermSpecOrList t2);
  void bind(const TermSpecOrList& v, TermSpecOrList b);

  VarBankOrInt _outputIndex;

  VirtualIterator<RobSubst*> getAssocIterator(RobSubst* subst,
    TermSpecOrList l1, TermSpecOrList s1, TermSpecOrList l2, TermSpecOrList s2, bool complementary);

  struct AssocContext;
  class AssocIterator;

private:
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;

  bool isUnbound(TermSpecOrList v) const;

  void pushConstraint(Constraint c){
    _constr->add(std::move(c), bd());
  }
  Constraint popConstraint(){
    return _constr->pop(bd());
  }  
  bool emptyConstraints(){
    return _constr->isEmpty();
  }

  TermSpecOrList root(TermSpecOrList v) const;
  bool occurs(TermSpecOrList const& vs, TermSpecOrList const& ts);

  Option<BacktrackData&> bd(){
    if(bdIsRecording()){
      return Option<BacktrackData&>(bdGet());
    } else {
      return Option<BacktrackData&>();
    }
  }

  friend std::ostream& operator<<(std::ostream& out, RobSubst const& self)
  { return out << "bindings: " << self._bank << "\n" << "constraints: " << self._constr; }

  class BindingBacktrackObject
  : public BacktrackObject
  {
  public:
    BindingBacktrackObject(RobSubst* subst, TermSpecOrList v)
    :_subst(subst), _var(v)
    {
      Option<TermSpecOrList&> t = _subst->_bank.find(_var);
      if(t) {
        _term = some(*t);
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
    RobSubst* _subst;
    TermSpecOrList _var;
    Option<TermSpecOrList> _term;
  };
};

class RobSubstitutionTL : public RobSubstitution<TermList, VarBank>
{
  friend class UnificationConstraint<TermList, VarBank>;

public:

  RobSubstitutionTL() {
    _outputIndex = VarBank::OUTPUT_BANK;
  }

  SubstIterator unifiers(Literal* l1,  Literal* l2, bool complementary);

  Literal* apply(Literal* lit, VarBank bank) const 
  { return RobSubstitution<TermList, VarBank>::apply(lit, bank); } 

  TermList apply(TermList t, VarBank bank) const
  { return RobSubstitution<TermList, VarBank>::apply(t, bank); } 

  /**
   * Bind special variable to a specified term
   *
   * Calls to this method must happen before calls to any
   * other methods. Also no special variables can occur in
   * binding term, as no occur-check is performed.
   */
  void bindSpecialVar(unsigned var, TermList t)
  {
    TermList vs(var, true);

    ASS(!_bank.find(vs));
    bind(vs, t);
  }

private:
  /** This method should only be used when all variables of 
    * t are on a bank different to DEFAULT_BANK */
  virtual TermList apply(TermList t) const override 
  { return RobSubstitution<TermList, VarBank>::apply(t, DEFAULT_BANK); }

  virtual TermList getUnboundVar() const override
  { return TermList(_nextUnboundAvailable++, VarBank::OUTPUT_BANK); }  

  virtual TermList getLitArg(Literal* lit, unsigned idx, VarBank b) const override
  { return *lit->nthArgument(idx); }

  virtual TermList getLitSort(Literal* lit, VarBank bank) const override
  { ASS(lit->isTwoVarEquality()); return lit->twoVarEqSort(); }

  virtual bool isDefault(VarBank bank) const override
  { return bank == VarBank::OUTPUT_BANK; }

  virtual void resetOutputIndex() override
  { _outputIndex = VarBank::OUTPUT_BANK; }

  struct ToRobTermList;
};

// for backwards compatibility purposes
class RobSubstitutionTS : public RobSubstitution<TermSpec, int>
{
  friend class UnificationConstraint<TermSpec, int>;

public:

  RobSubstitutionTS() {
    _outputIndex = TermSpec::UNBOUND_INDEX;
  }

  bool unify(TermList t1, int idx1, TermList t2, int idx2); 
  bool match(TermList t1, int idx1, TermList t2, int idx2); 

  SubstIteratorTS unifiers(Literal* l1, int l1idx, Literal* l2, int l2idx, bool complementary);
  
  Literal* apply(Literal* lit, int index) const 
  { return RobSubstitution<TermSpec, int>::apply(lit, index); } 

  TermList apply(TermList t, int index) const
  { return RobSubstitution<TermSpec, int>::apply(TermSpec(t,index), index); } 

private:

  virtual TermList apply(TermSpec t) const override 
  { return RobSubstitution<TermSpec, int>::apply(t, t.index); }

  virtual TermSpec getUnboundVar() const override
  { return TermSpec(_nextUnboundAvailable++, TermSpec::UNBOUND_INDEX); }

  virtual TermSpec getLitArg(Literal* lit, unsigned idx, int b) const override
  { return TermSpec(*lit->nthArgument(idx),b); }

  virtual TermSpec getLitSort(Literal* lit, int b) const override
  { ASS(lit->isTwoVarEquality()); return TermSpec(lit->twoVarEqSort(),b); }

  virtual bool isDefault(int bank) const override
  { return bank == TermSpec::UNBOUND_INDEX; }

  virtual void resetOutputIndex() override
  { _outputIndex = TermSpec::UNBOUND_INDEX; }

  struct ToRobTermSpec;
};

using namespace Lib;

template<class TermSpecOrList, class VarBankOrInt>
struct AutoDerefTerm
{
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

  TermSpecOrList term;
  RobSubst const* subs;
  VarBankOrInt bank;

  AutoDerefTerm(TermSpecOrList const& t, RobSubst const* s, VarBankOrInt b) 
    : subs(s)
    , bank(b) {  
      CALL("AutoDerefTerm::AutoDerefTerm");

      term = t.isOrdinaryVar() && !t.onBank() ? 
        s->derefBound(TermSpecOrList(t.var(), b)) : 
        s->derefBound(t);
    }

  AutoDerefTerm clone() const { return { term, subs, bank }; }
  explicit AutoDerefTerm(AutoDerefTerm const& other) : term(other.term), subs(other.subs), bank(other.bank) {}
  AutoDerefTerm(AutoDerefTerm && other) = default;
  friend std::ostream& operator<<(std::ostream& out, AutoDerefTerm const& self)
  { return out << self.term << "@" << *self.subs; }

};

};

namespace Lib {

  template<>
  // struct BottomUpChildIter<pair<Kernel::TermSpec, Kernel::RobSubstitution const*>>
  struct BottomUpChildIter<Kernel::AutoDerefTerm<TermList, Kernel::VarBank>>
  {
    using Item = Kernel::AutoDerefTerm<TermList, Kernel::VarBank>;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self) : _self(Item(self)), _arg(0) {}
  
    Item self() { return _self.clone(); }

    Item next()
    { return Item(_self.term.nthArg(_arg++), _self.subs, _self.bank); }

    bool hasNext()
    { return _self.term.isTerm() && _arg < _self.term.term()->arity(); }

    unsigned nChildren()
    { return _self.term.isVar() ? 0 : _self.term.term()->arity(); }
  };

  // TODO get rid of code duplication ...
  template<>
  struct BottomUpChildIter<Kernel::AutoDerefTerm<Kernel::TermSpec,int>>
  {
    using Item = Kernel::AutoDerefTerm<Kernel::TermSpec,int>;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self) : _self(Item(self)), _arg(0) {}
  
    Item self() { return _self.clone(); }

    Item next()
    { return Item(_self.term.nthArg(_arg++), _self.subs, _self.bank); }

    bool hasNext()
    { return _self.term.isTerm() && _arg < _self.term.term()->arity(); }

    unsigned nChildren()
    { return _self.term.isVar() ? 0 : _self.term.term()->arity(); }
  };



} // namespace Lib

#endif /*__RobSubstitution__*/

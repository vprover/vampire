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
#include "Term.hpp"
#include "MismatchHandler.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"

#if VDEBUG
#include <iostream>
#include "Lib/VString.hpp"
#endif

namespace Kernel
{

using namespace Lib;

class RobSubstitution
:public Backtrackable
{
public:
  CLASS_NAME(RobSubstitution);
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() : _funcSubtermMap(nullptr), _nextUnboundAvailable(0) {}

  SubstIterator matches(Literal* base, int baseIndex,
	  Literal* instance, int instanceIndex, bool complementary);
  SubstIterator unifiers(Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  bool unify(TermList t1,int index1, TermList t2, int index2, MismatchHandler* hndlr=0);
  bool match(TermList base,int baseIndex, TermList instance, int instanceIndex);

  bool unifyArgs(Term* t1,int index1, Term* t2, int index2, MismatchHandler* hndlr=0);
  bool matchArgs(Term* base,int baseIndex, Term* instance, int instanceIndex);

  void denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex);
  bool isUnbound(unsigned var, int index) const
  {
    return isUnbound(VarSpec(var,index));
  }
  void reset()
  {
    _funcSubtermMap = 0;
    _bank.reset();
    _nextUnboundAvailable=0;
  }

  void setMap(FuncSubtermMap* fmap){
    _funcSubtermMap = fmap;
  }
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
  TermList getSpecialVarTop(unsigned specialVar) const;
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
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

  /** Specifies instance of a variable (i.e. (variable, variable bank) pair) */
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
     static unsigned hash(VarSpec& o) {
       return HashUtils::combine(o.var, o.index);
     }
    };
    /** struct containing second hash function for DHMap object storing variable banks */
    struct Hash2
    {
      static unsigned hash(VarSpec& o) {
        return HashUtils::combine(o.index, o.var);
      }
    };
  };
  /** Specifies an instance of a term (i.e. (term, variable bank) pair */
  struct TermSpec
  {
    /** Create a new TermSpec struct */
    TermSpec() : index(0) {}
    /** Create a new TermSpec struct */
    TermSpec(TermList term, int index) : term(term), index(index) {}
    /** Create a new TermSpec struct from a VarSpec*/
    explicit TermSpec(const VarSpec& vs) : index(vs.index)
    {
      if(index==SPECIAL_INDEX) {
        term.makeSpecialVar(vs.var);
      } else {
        term.makeVar(vs.var);
      }
    }
    /**
     * If it's sure, that @b ts has the same content as this TermSpec,
     * return true. If they don't (or it cannot be easily checked), return
     * false. Only term content is taken into account, i.e. when two
     * literals are pointer do by ts.term, their polarity is ignored.
     */
    bool sameTermContent(const TermSpec& ts)
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

    bool isVSpecialVar()
    {
      return term.isVSpecialVar();
    }

    bool isVar()
    {
      return term.isVar();
    }
    bool operator==(const TermSpec& o) const
    { return term==o.term && index==o.index; }

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  typedef pair<TermSpec,TermSpec> TTPair;
 
  /** struct containing first hash function of TTPair objects*/
  struct TTPairHash
  {
   static unsigned hash(TTPair& o)
   {
     return IdentityHash::hash(o.first.term.content())^o.first.index ^
       ((IdentityHash::hash(o.second.term.content())^o.second.index)<<1);
   }
  };

  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self)
  { return out << self.term << "/" << self.index; }

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
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;


  static const int SPECIAL_INDEX;
  static const int UNBOUND_INDEX;

  bool isUnbound(VarSpec v) const;
  TermSpec deref(VarSpec v) const;
  TermSpec derefBound(TermSpec v) const;

  void addToConstraints(const VarSpec& v1, const VarSpec& v2,MismatchHandler* hndlr);
  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v) const;
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2,MismatchHandler* hndlr);
  bool occurs(VarSpec vs, TermSpec ts);

  inline
  VarSpec getVarSpec(TermSpec ts) const
  {
    return getVarSpec(ts.term, ts.index);
  }

  VarSpec getVarSpec(TermList tl, int index) const
  {
    CALL("RobSubstitution::getVarSpec");
    ASS(tl.isVar());
    index = tl.isSpecialVar() ? SPECIAL_INDEX : index;
    return VarSpec(tl.var(), index);
  }

  typedef DHMap<VarSpec,TermSpec,VarSpec::Hash1, VarSpec::Hash2> BankType;

  FuncSubtermMap* _funcSubtermMap;
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
      if(! _subst->_bank.find(_var,_term)) {
	_term.term.makeEmpty();
      }
    }
    void backtrack()
    {
      if(_term.term.isEmpty()) {
	_subst->_bank.remove(_var);
      } else {
	_subst->_bank.set(_var,_term);
      }
    }
    friend std::ostream& operator<<(std::ostream& out, BindingBacktrackObject const& self)
    { return out << "(ROB backtrack object for " << self._var << ")"; }
    CLASS_NAME(RobSubstitution::BindingBacktrackObject);
    USE_ALLOCATOR(BindingBacktrackObject);
  private:
    RobSubstitution* _subst;
    VarSpec _var;
    TermSpec _term;
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

#endif /*__RobSubstitution__*/


/*
 * File RobSubstitution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __RobSubstitution__
#define __RobSubstitution__

#include <utility>

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Set.hpp"
#include "Lib/BiMap.hpp"
#include "Term.hpp"

#if VDEBUG

#include <iostream>
#include "Lib/VString.hpp"

#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

class RobSubstitution
:public Backtrackable
{
public:
  CLASS_NAME(RobSubstitution);
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() : _nextUnboundAvailable(0),_nextAuxAvailable(0) {}

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
  bool isSpecialUnbound(unsigned var, int index) const
  {
    return isUnbound(VarSpec(var,SPECIAL_INDEX));
  }
  void reset()
  {
    _funcSubtermMap = 0;
    _constraints.reset();
    _bank.reset();
    _nextAuxAvailable=0;
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
  vstring toString(bool deref=false) const;
  /**
   * Return number of bindings stored in the substitution.
   *
   * - 0 means a fresh substitution.
   * - Without backtracking, this number doesn't decrease.
   */
  size_t size() const {return _bank.size(); }
#endif

  unsigned constraintsSize()  const { return _constraints.size(); }

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

#if VDEBUG
    vstring toString() const;
#endif

    /** number of variable */
    unsigned var;
    /** index of variable bank */
    int index;

    /** struct containing first hash function for DHMap object storing variable banks */
    struct Hash1
    {
     static unsigned hash(VarSpec& o, int capacity);
    };
    /** struct containing second hash function for DHMap object storing variable banks */
    struct Hash2
    {
      static unsigned hash(VarSpec& o);
    };
  };
  struct TermSpec
  {
    /** Create a new VarSpec struct */
    TermSpec() {}
    /** Create a new VarSpec struct */
    TermSpec(TermList term, int index) : term(term), index(index) {}
    /** Create a new VarSpec struct */
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
#if VDEBUG
    vstring toString() const;
#endif

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  typedef pair<TermSpec,TermSpec> TTPair;
  typedef Set<TTPair> UnifConstraints;

  const UnifConstraints& constraints() const { return _constraints; }

  /** struct containing first hash function of TTPair objects*/
  struct TTPairHash
  {
   static unsigned hash(TTPair& o)
   {
     return IdentityHash::hash(o.first.term.content())^o.first.index ^
       ((IdentityHash::hash(o.second.term.content())^o.second.index)<<1);
   }
  };

private:
  /** Copy constructor is private and without a body, because we don't want any. */
  RobSubstitution(const RobSubstitution& obj);
  /** operator= is private and without a body, because we don't want any. */
  RobSubstitution& operator=(const RobSubstitution& obj);


  static const int AUX_INDEX;
  static const int SPECIAL_INDEX;
  static const int UNBOUND_INDEX;

  bool isUnbound(VarSpec v) const;
  TermSpec deref(VarSpec v) const;
  TermSpec derefBound(TermSpec v) const;

  void addToConstraints(const VarSpec& v1, const VarSpec& v2);
  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v) const;
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2);
  bool handleDifferentTops(TermSpec t1, TermSpec t2, Stack<TTPair>& toDo, TermList* ct);
  void makeEqual(VarSpec v1, VarSpec v2, TermSpec target);
  void unifyUnbound(VarSpec v, TermSpec ts);
  bool occurs(VarSpec vs, TermSpec ts);

  VarSpec getAuxVar(VarSpec target)
  {
    CALL("RobSubstitution::getAuxVar");
    if(target.index==AUX_INDEX) {
      return target;
    }
    VarSpec res(_nextAuxAvailable++,AUX_INDEX);
    bindVar(res, target);
    return res;
  }
  inline
  VarSpec getVarSpec(TermSpec ts) const
  {
    return getVarSpec(ts.term, ts.index);
  }
  VarSpec getVarSpec(TermList tl, int index) const
  {
    CALL("RobSubstitution::getVarSpec");
    ASS(tl.isVar());
    if(tl.isSpecialVar()) {
      return VarSpec(tl.var(), SPECIAL_INDEX);
    } else {
      ASS(index!=AUX_INDEX || tl.var()<_nextAuxAvailable);
      return VarSpec(tl.var(), index);
    }
  }
  static void swap(TermSpec& ts1, TermSpec& ts2);

  typedef DHMap<VarSpec,TermSpec,VarSpec::Hash1, VarSpec::Hash2> BankType;

  FuncSubtermMap* _funcSubtermMap;
  mutable BankType _bank;
  mutable UnifConstraints _constraints;

  DHMap<int, int> _denormIndexes;

  mutable unsigned _nextUnboundAvailable;
  unsigned _nextAuxAvailable;

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
#if VDEBUG
    vstring toString() const
    {
      return "(ROB backtrack object for "+ _var.toString() +")";
    }
#endif
    CLASS_NAME(RobSubstitution::BindingBacktrackObject);
    USE_ALLOCATOR(BindingBacktrackObject);
  private:
    RobSubstitution* _subst;
    VarSpec _var;
    TermSpec _term;
  };

  class ConstraintBacktrackObject
  : public BacktrackObject
  {
  public: 
    ConstraintBacktrackObject(RobSubstitution* subst, TTPair con)
    : _subst(subst), _con(con)
    {}
    
    void backtrack()
    {
      ALWAYS(_subst->_constraints.remove(_con));
    }

    CLASS_NAME(RobSubstitution::ConstraintBacktrackObject);
    USE_ALLOCATOR(ConstraintBacktrackObject);
  private:
    RobSubstitution* _subst;
    TTPair _con;
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

#if VDEBUG

ostream& operator<< (ostream& out, RobSubstitution::VarSpec vs );
ostream& operator<< (ostream& out, RobSubstitution::TermSpec vs );

#endif


};


namespace Lib
{
/**
 * Traits structure specialisation. (See DHMap.hpp)
 */
template<>
struct HashTraits<Kernel::RobSubstitution::VarSpec::Hash1>
{
  enum {SINGLE_PARAM_HASH=0};
};
};

#endif /*__RobSubstitution__*/

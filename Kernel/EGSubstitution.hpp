/**
 * @file EGSubstitution.hpp
 * Defines class EGSubstitution.
 *
 */

#ifndef __EGSubstitution__
#define __EGSubstitution__

#include <utility>

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/BacktrackData.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"

#if VDEBUG

#include <iostream>
#include <string>

#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

class EGSubstitution
:public Backtrackable
{
public:
  EGSubstitution() : _nextUnboundAvailable(0),_nextAuxAvailable(0),
    _currTimeStamp(1), _unchecked(16) {}

  bool unify(TermList t1,int index1, TermList t2, int index2);
  bool match(TermList base,int baseIndex, TermList instance, int instanceIndex);
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
    _bank.reset();
    _nextAuxAvailable=0;
    _nextUnboundAvailable=0;
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
    CALL("EGSubstitution::getAuxVar");

    VarSpec vs(var, SPECIAL_INDEX);
    ASS(!_bank.find(vs));
    bind(vs, TermSpec(t,index));

//    _rs.bindSpecialVar(var,t,index);
  }
  TermList getSpecialVarTop(unsigned specialVar);
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;

#if VDEBUG
  std::string toString(bool deref=false) const;
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

#if VDEBUG
    std::string toString() const;
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

    bool isVar()
    {
      return term.isVar() && index!=RESERVED_INDEX;
    }
    bool operator==(const TermSpec& o) const
    { return term==o.term && index==o.index; }
    bool operator!=(const TermSpec& o) const
    { return !(*this==o); }
#if VDEBUG
    string toString() const;
#endif

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  typedef pair<TermSpec,TermSpec> TTPair;
  typedef Stack<VarSpec> VarStack;

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
  EGSubstitution(const EGSubstitution& obj);
  /** operator= is private and without a body, because we don't want any. */
  EGSubstitution& operator=(const EGSubstitution& obj);

  bool unifyArgs(Term* t1,int index1, Term* t2, int index2);
  bool matchArgs(Term* base,int baseIndex, Term* instance, int instanceIndex);

  static const int RESERVED_INDEX;
  static const int AUX_INDEX;
  static const int SPECIAL_INDEX;
  static const int UNBOUND_INDEX;

  static const TermSpec TS_DONE;
  static const TermSpec TS_LOOP;
  static const TermSpec TS_NIL;

  void storeForBacktrack(VarSpec v);

  bool isRoot(VarSpec v) const;
  TermSpec parent(VarSpec v) const;
  void setParent(VarSpec v, TermSpec t, bool canCauseLoop=true);
  VarSpec root(VarSpec v, VarStack& path);
  VarSpec getRootAndCollapse(VarSpec v);
  VarSpec rootWithoutCollapsing(VarSpec v) const;
  void collapse(VarStack& path, VarSpec v, bool canCauseLoop=true);

  void markChanged(VarSpec v);
  void nextTimeStamp();

  bool unify(TermSpec t1, TermSpec t2);
  bool recurUnify(VarSpec v, TermSpec y, TermSpec t, Stack<TTPair>& toDo);
  bool varUnify(VarSpec u, TermSpec t, Stack<TTPair>& toDo);

  bool isUnbound(VarSpec v) const;
  TermSpec deref(VarSpec v) const;
  TermSpec derefBound(TermSpec v) const;

  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);

  bool match(TermSpec base, TermSpec instance);

  bool occursCheck(VarSpec var);

  VarSpec getAuxVar(VarSpec target)
  {
    CALL("EGSubstitution::getAuxVar");
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
    CALL("EGSubstitution::getVarSpec");
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
  typedef DHMap<VarSpec,unsigned,VarSpec::Hash1, VarSpec::Hash2> TimeStampStore;

  mutable BankType _bank;

  DHMap<int, int> _denormIndexes;

  mutable unsigned _nextUnboundAvailable;
  unsigned _nextAuxAvailable;
  unsigned _currTimeStamp;

  TimeStampStore _tStamps;
  VarStack _unchecked;

//  RobSubstitution _rs;


  class BindingBacktrackObject
  : public BacktrackObject
  {
  public:
    BindingBacktrackObject(EGSubstitution* subst, VarSpec v, TermSpec t)
    : _subst(subst), _var(v), _term(t)
    {
    }
    BindingBacktrackObject(EGSubstitution* subst, VarSpec v)
    : _subst(subst), _var(v)
    {
      _term.term.makeEmpty();
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
    std::string toString() const
    {
      return "(EG backtrack object for "+ _var.toString() +")";
    }
#endif
    CLASS_NAME("EGSubstitution::BindingBacktrackObject");
    USE_ALLOCATOR(BindingBacktrackObject);
  private:
    EGSubstitution* _subst;
    VarSpec _var;
    TermSpec _term;
  };

};

#if VDEBUG

ostream& operator<< (ostream& out, EGSubstitution::VarSpec vs );
ostream& operator<< (ostream& out, EGSubstitution::TermSpec vs );

#endif


};


namespace Lib
{
/**
 * Traits structure specialisation. (See DHMap.hpp)
 */
template<>
struct HashTraits<Kernel::EGSubstitution::VarSpec::Hash1>
{
  enum {SINGLE_PARAM_HASH=0};
};
};

#endif /*__EGSubstitution__*/

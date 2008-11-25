/**
 * @file MMSubstitution.hpp
 * Defines class MMSubstitution.
 *
 */

#ifndef __MMSubstitution__
#define __MMSubstitution__

#include <utility>

#include "../Lib/DHMap.hpp"
#include "../Lib/BacktrackData.hpp"
#include "Term.hpp"

#ifdef VDEBUG

#include <string>

#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

class MMSubstitution
:public Backtrackable
{
public:
  MMSubstitution() : _nextUnboundAvailable(0),_nextAuxAvailable(0) {}
  
  bool unify(TermList t1,int index1, TermList t2, int index2);
  bool isUnbound(unsigned var, int index) const
  {
    return isUnbound(VarSpec(var,index));
  }
  bool isSpecialUnbound(unsigned var, int index) const
  {
    return isUnbound(VarSpec(var,SPECIAL_INDEX));
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
  TermList getSpecialVarTop(unsigned var) const
  {
    return deref(VarSpec(var, SPECIAL_INDEX)).term;
  }
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
  
#ifdef VDEBUG
  std::string toString() const;
#endif
  
private:
  static const int AUX_INDEX=-3;
  static const int SPECIAL_INDEX=-2;
  static const int UNBOUND_INDEX=-1;
  
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
    
    #ifdef VDEBUG
    std::string toString() const
    {
      return Int::toString(var)+"/"+Int::toString(index);
    }
    #endif

    /** number of variable */
    unsigned var;
    /** index of variable bank */
    int index;
    
    /** class containing first hash function for DHMap object storing variable banks */
    class Hash1
    {
    public:
      static unsigned hash(VarSpec& o, int capacity);
    };
    /** class containing second hash function for DHMap object storing variable banks */
    class Hash2
    {
    public:
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
     * false.
     */
    bool sameContent(const TermSpec& ts)
    {
      bool termSameContent=term.sameContent(&ts.term);
      if(!termSameContent) {
	return false;
      }
      return index==ts.index || term.isSpecialVar() ||
      	(term.isTerm() && term.term()->shared() && term.term()->ground()); 
    }
    
    bool isVar()
    {
      return term.isVar();
    }

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  typedef pair<TermSpec,TermSpec> TTPair;

  bool isUnbound(VarSpec v) const;
  TermSpec deref(VarSpec v) const;
  TermSpec derefBound(TermSpec v) const;
  
  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v) const;
  bool unify(TermSpec t1, TermSpec t2);
  bool handleDifferentTops(TermSpec t1, TermSpec t2, 
  	Stack<TTPair>& toDo, TermList* ct);
  void makeEqual(VarSpec v1, VarSpec v2, TermSpec target);
  void unifyUnbound(VarSpec v, TermSpec ts);
  
  bool occurCheckFails() const;

  VarSpec getAuxVar(VarSpec target)
  {
    CALL("MMSubstitution::getAuxVar");
    VarSpec res(_nextAuxAvailable++,AUX_INDEX);
    bindVar(res, target);
    return res; 
  }
  static VarSpec getVarSpec(TermSpec ts)
  {
    return getVarSpec(ts.term, ts.index);
  }
  static VarSpec getVarSpec(TermList tl, int index)
  {
    CALL("MMSubstitution::getVarSpec");
    ASS(tl.isVar());
    if(tl.isSpecialVar()) {
      return VarSpec(tl.var(), SPECIAL_INDEX);
    } else {
      return VarSpec(tl.var(), index);
    }
  }
  static void swap(TermSpec& ts1, TermSpec& ts2);
  
  typedef DHMap<VarSpec,TermSpec,VarSpec::Hash1, VarSpec::Hash2> BankType; 
  
  mutable BankType _bank;
  
  mutable unsigned _nextUnboundAvailable;
  mutable unsigned _nextAuxAvailable;
  
  class BindingBacktrackObject
  : public BacktrackObject
  {
  public:
    BindingBacktrackObject(MMSubstitution* subst, VarSpec v)
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
#ifdef VDEBUG
    std::string toString() const
    {
      return "(MM backtrack object for "+ _var.toString() +")";
    }
#endif
  private:
    MMSubstitution* _subst;
    VarSpec _var;
    TermSpec _term;
  };
};

};


namespace Lib 
{
/**
 * Traits structure specialisation. (See DHMap.hpp) 
 */
template<>
struct HashTraits<Kernel::MMSubstitution::VarSpec::Hash1>
{
  enum {SINGLE_PARAM_HASH=0};
};
};

#endif /*__MMSubstitution__*/

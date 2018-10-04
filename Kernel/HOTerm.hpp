
/*
 * File HOTerm.hpp.
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
 * @file HOTerm.hpp
 * Defines class HigherOrderHOTerm.
 */

#ifndef __HOTerm__
#define __HOTerm__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Deque.hpp"

#include "Kernel/HOSortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"

namespace Kernel {

class HOTerm {

CLASS_NAME(HOTerm);
USE_ALLOCATOR(HOTerm);

private:

public:
  
  typedef Signature::Symbol SS;
  typedef HOSortHelper HSH;

  //create a new higher-order term
  explicit HOTerm(TermList ts,  int hsort = -1, int hind = -1)
    :_head(ts), _headInd(hind) 
  {
    CALL("HOTerm::HOTerm");
    ASS(!ts.isVar || hsort > -1);

    if(hsort > -1){
      _headsort = (unsigned)hsort;
      _srt = _headsort;
    } else {
      _headsort = SortHelper::getResultSort(ts.term());
      _srt = _headsort;
    }

    _arity = HSH::arity(_headsort);
    if(_arity) {
      void** mem = ALLOC_KNOWN(_arity*sizeof(HOTerm*),className());
      _args = static_cast<HOTerm**>(mem);
    } else {
      _args = 0;
    }
    _lastarg = _args;
    _end = _args+_arity;
  }

  /** copy constructor, leave for now
  HOTerm(const HOTerm& ht)
   : _head(ht._head),
     _headsort(ht._headsort),
     _termsort(ht._termsort),
     _headInd(ht._headInd),
     _arity(ht._arity),
     _args(ht._args),
     _lastarg(ht._lastarg),
     _end(ht._end),
  {} */


  /** De-allocate the args
   */
  inline ~HOTerm()
  {
    CALL("HOTerm::~HOTerm");

    HOTerm** ht = _args;
    while(ht!=_lastarg) {
      *ht->~HOTerm();
      ht++;
    }
    if(_args) {
      DEALLOC_KNOWN(_args,_arity*sizeof(HOTerm*),className());
    }
  }

  /** head symbol of this HOTerm */
  TermList _head;
  /** sort of head symbol */
  unsigned _headsort;
  /** sort of term */
  unsigned _termsort;
  //Only relevant when using structure in combiatory unification
  int _headInd;
  /** Maximum allowable number of args for this head symbol */
  unsigned  _arity;
  /** the arguments */
  HOTerm** _args;
  /** points to to location after final argument */
  HOTerm** _lastarg;
  /** points to _args + arity */
  HOTerm** _end;
  
  inline unsigned argnum() const { 
    return _lastarg - _args; 
  }
  //zero indexed
  HOTerm* ntharg(unsigned n){
    ASS(_args + n < _lastarg);
    return _args[n];
  }
  //zero indexed    
  unsigned nthArgSort(unsigned n) const{
    ASS(_args + n < _lastarg);
    return _args[n]->sort();      
  }
  //n must be less than or equal to argnum()
  unsigned sortOfLengthNPref(unsigned n) const{
    ASS(_args + n < _lastarg);
    return HSH::appliedToN(headsort, n);
  }
  /** adds argument to end of args*/
  void addArg(HOTerm* ht){
    CALL("HOTerm::addArg");
#if VDEBUG
    ASS_REP(HSH::arity(_termsort) > 0, env.sorts->sortName(_termsort));
    ASS(HSH::domain(_termsort) == ht->sort());
    ASS(_lastarg < _end);
#endif
    *_lastarg = ht;
    _lastarg++;
    _termsort = HSH::range(_termsort);
  }
  /** Returns the sort of whole term */
  unsigned sort() const { return _termsort;}
  /** Returns true if HOTerm has variable head */
  bool varHead() const { return head.isVar();}
  /** Returns true if the HOTerm is a variable */
  bool isVar() const { 
    return head.isVar() && (_args == _lastarg); 
  }
  /** returns true if var with args */
  bool isAppliedVar() const { 
    return head.isVar() && (_args != _lastarg); 
  }
  /** Returns true if HOTerm has combinator as head */
  bool combHead() const { 
    if(head.isVar()){
      return false;
    }
    SS* sym = env.signature->getFunction(head.term()->functor());
    SS::HOLConstant c = sym->getConst();
    return (c >= SS::S_COMB && c <= SS::K_COMB); 
  }
  /** Returns the combinator. Can only be called after a call to isComb */
  SS::HOLConstant headComb() const {
    ASS(!head.isVar());
    SS* sym = env.signature->getFunction(head.term()->functor());
    SS::HOLConstant c = sym->getConst();
    ASS(c >= SS::S_COMB && c <= SS::K_COMB); 
    return c;
  }
  /** Returns true if HOTerm is an underapplied combinator term */
  bool underAppliedCombTerm() const {
     if(!combHead()){ return false; }
     SS::HOLConstant c = headComb();
     if(c >= SS::S_COMB && c <= SS::C_COMB && argnum() < 3){ return true; }
     if(c == SS::K_COMB && argnum() < 2){ return true; }
     if(c == SS::I_COMB && argnum() < 1){ return true; }
     return false;
  }
  /** Returns true if both HOTerms have same non-var non-comb head */
  bool sameFirstOrderHead(const HOTerm* hotm) const {
    if(varHead() || hotm->varHead()){ return false; }
    if(combHead() || hotm->combHead()){ return false; }
    return head.term()->functor() == hotm->head.term()->functor();
  }
  /** Returns true if both HOTerms have diff non-var non-comb heads */
  bool diffFirstOrderHead(const HOTerm* hotm) const {
    if(varHead() || hotm->varHead()){ return false; }
    if(combHead() || hotm->combHead()){ return false; }
    return head.term()->functor() != hotm->head.term()->functor();
  }
  /** returns true if same variable heads */
  bool sameVarHead(const HOTerm* hotm, bool useIndices = false) const {
    if(useIndices && headInd != hotm->headInd){ return false; }
    if(!varHead() || !hotm->varHead()){ return false; }      
    return head.var() == hotm->head.var();
  }
  //make const HOTerm
  void headify(HOTerm* tm);
  /** Returns true if this HOTerm is 
   *  syntactically equal to the first argument
   *  if @b vars is false, then non-ground terms 
   *  will always return false
   */
  bool equal(const HOTerm*,bool useIndices = false ) const;
#if VDEBUG
  vstring toString (bool withSorts = false, bool withIndices = false) const;
#endif

};

}

#endif // __HOTerm__


/*
 * File HOSortHelper.hpp.
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
 * @file HOSortHelper.hpp
 * Defines class HigherOrderHOSortHelper.
 */

#ifndef __HOSortHelper__
#define __HOSortHelper__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Deque.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include <memory>

namespace Kernel {

class HOSortHelper {
private:

public:
  
  typedef Signature::Symbol SS;

  struct HOTerm{

    CLASS_NAME(HOTerm);
    USE_ALLOCATOR(HOTerm);

    //create a new higher-order term
    HOTerm(TermList ts,  int hsort = -1, int hind = -1):head(ts),headInd(hind) 
    {
      if(hsort > -1){
        headsort = (unsigned)hsort;
        srt = headsort;
      } else {
        if(!ts.isVar()){
          headsort = SortHelper::getResultSort(ts.term());
          srt = headsort;
        }
      }
    }
    //copy constructor
    HOTerm( const HOTerm &ht){
      cout << "CALLING HOTerm COPY CONSTRUCTOR with " + ht.toString(false, true) << endl;
      head = ht.head;
      headsort = ht.headsort;
      srt = ht.srt;
      args = ht.args;
      headInd = ht.headInd;
    } 

    HOTerm(){}
  
    //head symbol of this HOTerm
    TermList head;
    //WARNING if head is variable and argnums is 0 then headsort is not set!    
    unsigned headsort;
    /** sort of term */
    //WARNING if headsort not assigned sort is not assigned either!
    unsigned srt;
    //args of this HOTerm
    Deque<HOTerm> args;
    //Only relevant when using structure in combiatory unification
    int headInd;
    
    inline unsigned argnum() const { return args.size(); }
    //zero indexed
    HOTerm ntharg(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[n];
    }
    HOTerm* nthargptr(unsigned n) {
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return &args[n];
    }
    //zero indexed    
    unsigned nthArgSort(unsigned n) const{
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[n].sort();      
    }
    //n must be less than or equal to argnum()
    unsigned sortOfLengthNPref(unsigned n) const{
      ASS(n <= args.size());
      return appliedToN(headsort, n);
    }
    /** adds argument to end of args*/
    void addArg(const HOTerm& ht){
      CALL("HOTerm::addArg");
  #if VDEBUG
      ASS_REP(arity(srt) > 0, env.sorts->sortName(srt));
      ASS(domain(srt) == ht.sort());
  #endif
      args.push_back(ht);
      srt = range(srt);
    }
    /** Returns the sort of whole term */
    unsigned sort() const { return srt;}
    /** Returns true if HOTerm has variable head */
    bool varHead() const { return head.isVar();}
    /** Returns true if the HOTerm is a variable */
    bool isVar() const { return head.isVar() && !args.size(); }
    /** returns true if var with args */
    bool isAppliedVar() const { return head.isVar() && args.size() > 0; }
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
       if(c >= SS::S_COMB && c <= SS::C_COMB && args.size() < 3){ return true; }
       if(c == SS::K_COMB && args.size() < 2){ return true; }
       if(c == SS::I_COMB && args.size() < 1){ return true; }
       return false;
    }
    /** Returns true if both HOTerms have same non-var non-comb head */
    bool sameFirstOrderHead(const HOTerm& hotm) const {
      if(varHead() || hotm.varHead()){ return false; }
      if(combHead() || hotm.combHead()){ return false; }
      return head.term()->functor() == hotm.head.term()->functor();
    }
    /** Returns true if both HOTerms have diff non-var non-comb heads */
    bool diffFirstOrderHead(const HOTerm& hotm) const {
      if(varHead() || hotm.varHead()){ return false; }
      if(combHead() || hotm.combHead()){ return false; }
      return head.term()->functor() != hotm.head.term()->functor();
    }
    /** returns true if same variable heads */
    bool sameVarHead(const HOTerm& hotm, bool useIndices = false) const {
      if(useIndices && headInd != hotm.headInd){ return false; }
      if(!varHead() || !hotm.varHead()){ return false; }      
      return head.var() == hotm.head.var();
    }
    //make const HOTerm
    void headify(HOTerm tm);
    /** Returns true if this HOTerm is 
     *  syntactically equal to the first argument
     *  if @b vars is false, then non-ground terms 
     *  will always return false
     */
    bool equal(const HOTerm&,bool useIndices = false ) const;
#if VDEBUG
    vstring toString (bool withSorts = false, bool withIndices = false) const;
#endif
  };

  typedef unique_ptr<HOTerm> HOTerm_ptr;

  static TermList appify(HOTerm);
  static HOTerm deappify(TermList,int index = -1);

  /** Returns the sort of the head of an applicative term */
  static unsigned getHeadSort(TermList ts);
  /** Returns the sort of the nth argument of the applicative term ts*/
  static unsigned getNthArgSort(TermList ts, unsigned n);
  /** Returns the number of args the head of an applicative term is applied to */
  static unsigned argNum(TermList ts);
  /** Returns the resulting sort if a head of sort @b funcsort was to be applied to n arguments*/
  static unsigned appliedToN(unsigned funcSort, unsigned n);
  /**  */
  static unsigned appliedToN(TermList ts, unsigned n);
  /** Returns the nth argument sort of functional sort @b funcSort */
  static unsigned getNthArgSort(unsigned funcSort, unsigned n);
  /** Returns the head symbol of an applicative term */
  //shouldn't really be here as not a sort function
  static TermList getHead(TermList ts);
  /** given a functional sort, returns its range */
  static unsigned range(unsigned sort);
  /** given a functional sort, returns its domain */
  static unsigned domain(unsigned sort);
  /** Returns the arity of a sort. Basic sorts have arity 0 */
  static unsigned arity(unsigned sort);
  /** Takes two termlists and returns the result of applying the 
   *  first to the second. Sort conditions must be met
   */
  static TermList apply(TermList t1, unsigned s1, TermList t2, unsigned s2);
  /** Returns true if the termlist is a constant */
  static bool isConstant(TermList tl){
    return (tl.isTerm() && !tl.term()->arity());
  }
  /** Add function sort and returns results */
  static unsigned addFuncSort(unsigned dom, unsigned range){
    return env.sorts->addFunctionSort(dom, range);
  }
  /** returns the higher-order sort with @b argSorts as its domain sorts and
      @b range as its range */
  static unsigned getHigherOrderSort(const Stack<unsigned>& argsSorts, unsigned range);
  /** returns appified term with args (including head) in @args and sorts in @argSorts */
  static Term* createAppifiedTerm(TermList head, unsigned headsort,
                                  const Stack<unsigned>& argSorts,
                                  const Stack<TermList>& args);
  /** Returns combinator constant */
  static TermList getCombTerm(SS::HOLConstant cons, unsigned sort);

};

}

#endif // __HOSortHelper__

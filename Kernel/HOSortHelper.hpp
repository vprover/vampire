
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

namespace Kernel {

class HOSortHelper {
private:

public:
  
  typedef Signature::Symbol SS;

  struct HOTerm{
    //create a new higher-order term
    HOTerm(TermList ts,  int hsort = -1)
    {
      head = ts;
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

    //would this cause a runtime exception if args hasn't been initialised?
    inline unsigned argnum() { return args.size(); }
    //zero indexed
    HOTerm ntharg(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[n];
    }
    HOTerm* nthargptr(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return &args[n];
    }
    //zero indexed    
    unsigned nthArgSort(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[n].sort();      
    }
    //n must be less than or equal to argnum()
    unsigned sortOfLengthNPref(unsigned n){
      ASS(n <= args.size());
      return appliedToN(headsort, n);
    }
    /** adds argument to end of args*/
    void addArg(HOTerm ht){
  #if vdebug
      ASS(arity(srt) > 0);
      ASS(domain(srt) == ht.sort());
  #endif
      args.push_back(ht);
      srt = range(srt);
    }
    /** Returns the sort of whole term */
    unsigned sort() { return srt;}
    /** Returns true if HOTerm has variable head */
    bool varHead() { return head.isVar();}
    /** Returns true if the HOTerm is a variable */
    bool isVar() { return head.isVar() && !args.size(); }
    /** Returns true if HOTerm has combinator as head */
    bool combHead() { 
      if(head.isVar()){
        return false;
      }
      SS* sym = env.signature->getFunction(head.term()->functor());
      SS::HOLConstant c = sym->getConst();
      return (c >= SS::S_COMB && c <= SS::K_COMB); 
    }
    /** Returns the combinator. Can only be called after a call to isComb */
    SS::HOLConstant headComb() {
      ASS(!head.isVar());
      SS* sym = env.signature->getFunction(head.term()->functor());
      SS::HOLConstant c = sym->getConst();
      ASS(c >= SS::S_COMB && c <= SS::K_COMB); 
      return c;
    }
    /** Returns true if HOTerm is an underapplied combinator term */
    bool underAppliedCombTerm() {
       if(!combHead()){ return false; }
       SS::HOLConstant c = headComb();
       if(c >= SS::S_COMB && c <= SS::C_COMB && args.size() < 3){ return true; }
       if(c == SS::K_COMB && args.size() < 2){ return true; }
       if(c == SS::I_COMB && args.size() < 1){ return true; }
       return false;
    }
    /** Returns true if both HOTerms have same non-var non-comb head */
    bool sameFirstOrderHead(HOTerm hotm){
      if(varHead() || hotm.varHead()){ return false; }
      if(combHead() || hotm.combHead()){ return false; }
      return head.term()->functor() == hotm.head.term()->functor();
    }
    /** Returns true if both HOTerms have diff non-var non-comb heads */
    bool diffFirstOrderHead(HOTerm hotm){
      if(varHead() || hotm.varHead()){ return false; }
      if(combHead() || hotm.combHead()){ return false; }
      return head.term()->functor() != hotm.head.term()->functor();
    }
    void headify(HOTerm tm);
#if VDEBUG
    vstring toString(bool withSorts = false);
#endif
  };

  static TermList appify(HOTerm);
  static HOTerm deappify(TermList);

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

  /** Returns combinator constant */
  static TermList getCombTerm(SS::HOLConstant cons, unsigned sort);
  /** Returns the maximum variable peresent in term */
  static unsigned getMaxVar(TermList ts){
    TermVarIterator vit(&ts);
    unsigned max = 0;
    while(vit.hasNext()){
      if(vit.next() > max){
        max = vit.next();
      }
    }
    return max;
  }

};

}

#endif // __HOSortHelper__

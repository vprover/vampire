
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

namespace Kernel {

class HOSortHelper {
private:

public:
  
  typedef Signature::Symbol SS;

  struct HOTerm{
    //create a new higher-order term
    HOTerm(TermList ts, unsigned ind): index(ind)
    {
      if(ts.isVar()){
        head = ts;
      } else {
        ASS(ts.isTerm());
        SS* sym = env.signature->getFunction(ts.term()->functor());
        while(sym->hOLAPP()){
          args.push_front(*(ts.term()->nthArgument(1)));
          sorts.push_front(SortHelper::getArgSort(ts.term(), 1));
          headsort = SortHelper::getArgSort(ts.term(), 0);
          ts = *(ts.term()->nthArgument(0));
          if(ts.isVar()){ break; }
          sym = env.signature->getFunction(ts.term()->functor());
        }
        head = ts;
      }
    }

    HOTerm(TermList ts){
      HOTerm(ts, 0);
    }

    HOTerm():index(0){}
  
    //head symbol of this HOTerm
    TermList head;
    //WARNING if head is variable and argnums is 0 then headsort is not set!    
    unsigned headsort;
    unsigned index;
    //args of this HOTerm
    Deque<TermList> args;
    Deque<unsigned> sorts;
    inline unsigned argnum() { return args.size(); }
    //zero indexed
    TermList ntharg(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[n];
    }
    //zero indexed    
    unsigned nthArgSort(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return sorts[n];      
    }
    //n must be less than or equal to argnum()
    unsigned sortOfLengthNPref(unsigned n){
      ASS(n <= args.size());
      return appliedToN(headsort, n);
    }
    /** Returns the sort of whole term */
    unsigned sort() { return sortOfLengthNPref(args.size());}
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

    TermList appify();
  };

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

};

}

#endif // __HOSortHelper__

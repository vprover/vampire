
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

#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"

namespace Kernel {

class HOSortHelper {
private:

public:
  
  
  struct HOTerm{
    //create a new higher-order term
    HOTerm(TermList ts){
      if(ts.isVar()){
        head = ts;
      } else {
        ASS(ts.isTerm());
        Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
        while(sym->hOLAPP()){
          args.push(*(ts.term()->nthArgument(1)));
          sorts.push(SortHelper::getArgSort(ts.term(), 1));
          headsort = SortHelper::getArgSort(ts.term(), 0);
          ts = *(ts.term()->nthArgument(0));
          if(ts.isVar()){ break; }
          sym = env.signature->getFunction(ts.term()->functor());
        }
        head = ts;
      }
    }

    //head symbol of this HOTerm
    TermList head;
    //WARNING if head is variable and argnums is 0 then headsort is not set!    
    unsigned headsort;
    //args of this HOTerm
    Stack<TermList> args;
    Stack<unsigned> sorts;
    inline unsigned argnum() { return args.size(); }
    //zero indexed
    TermList ntharg(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return args[argnum - n];
    }
    //zero indexed    
    unsigned nthArgSort(unsigned n){
      unsigned argnum = args.size();
      ASS(n <= argnum);
      return sorts[argnum - n];      
    }
    //n must be less than or equal to argnum()
    unsigned sortOfLengthNPref(unsigned n){
      ASS(n <= args.size());
      return appliedToN(headsort, 1);
    }
    TermList toTermList();
  };

  /** returns the sort of the head of an applicative term */
  static unsigned getHeadSort(TermList ts);
  /** returns the sort of the nth argument of the applicative term ts*/
  static unsigned getNthArgSort(TermList ts, unsigned n);
  /** returns the number of args the head of an applicative term is applied to */
  static unsigned argNum(TermList ts);
  /** returns the resulting sort if a head of sort @b funcsort was to be applied to n arguments*/
  static unsigned appliedToN(unsigned funcSort, unsigned n);
  /**  */
  static unsigned appliedToN(TermList ts, unsigned n);
  /** returns the nth argument sort of functional sort @b funcSort */
  static unsigned getNthArgSort(unsigned funcSort, unsigned n);
  /** returns the head symbol of an applicative term */
  //shouldn't really be here as not a sort function
  static TermList getHead(TermList ts);
  /** given a functional sort, returns its range */
  static unsigned range(unsigned sort);
  /** given a functional sort, returns its domain */
  static unsigned domain(unsigned sort);

};

}

#endif // __HOSortHelper__

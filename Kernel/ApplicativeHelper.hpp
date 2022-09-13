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
 * @file ApplicativeHelper.hpp
 * Defines class ApplicativeHelper.
 */

#ifndef __ApplicativeHelper__
#define __ApplicativeHelper__

#include "Forwards.hpp"
#include "Signature.hpp"
#include "Lib/Deque.hpp"
#include "Lib/BiMap.hpp"
#include "Kernel/TermTransformer.hpp"

using namespace Kernel;
using namespace Shell;

#if VHOL
// reduce a term to normal form
// uses a applicative order reduction strategy
// Currently use a leftmost outermost stratgey
// An innermost strategy is theoretically more efficient
// but is difficult to write iteratively TODO
class BetaNormaliser : public TermTransformer
{
public:

  BetaNormaliser() {
    dontTransformSorts();
  }  
  TermList normalise(TermList t);
  TermList transformSubterm(TermList t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;
};

// reduce to eta short form
// normalises top down carrying out parallel eta reductions
// for terms such as ^^^.f 2 1 0
class EtaNormaliser : public TermTransformer
{
public:

  EtaNormaliser() {
    dontTransformSorts();
  }  
  TermList normalise(TermList t);
  TermList transformSubterm(TermList t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

private:
  bool _ignoring;
  TermList _awaiting;
};

class RedexReducer : public TermTransformer 
{
public:
  RedexReducer() {
    dontTransformSorts();
  }    
  TermList reduce(TermList redex);
  TermList transformSubterm(TermList t) override; 
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

private:
  TermList _t2; // term to replace index with (^x.t1) t2
  unsigned _replace; // index to replace
};

class TermShifter : public TermTransformer
{
public:
  TermShifter() : _minFreeIndex(-1)  {
    dontTransformSorts();
  }   
  // positive value -> shift up
  // negative -> shift down 
  // 0 record minimum free index 
  TermList shift(TermList term, int shiftBy); 
  TermList transformSubterm(TermList t) override; 
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

  Option<unsigned> minFreeIndex(){ 
    return _minFreeIndex > -1 ? Option<unsigned>((unsigned)_minFreeIndex) : Option<unsigned>();
  }

private:
  unsigned _cutOff; // any index higher than _cutOff is a free index
  int _shiftBy; // the amount to shift a free index by
  int _minFreeIndex;
};

class ApplicativeHelper {
public:

  static TermList createAppTerm(TermList sort, TermList arg1, TermList arg2);
  static TermList createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);
  static TermList createAppTerm3(TermList sort, TermList arg1, TermList arg2, TermList arg3);
  static TermList createAppTerm(TermList sort, TermList arg1, TermList arg2, TermList arg3, TermList arg4); 
  static TermList createAppTerm(TermList sort, TermList head, TermStack& terms); 
  static TermList createAppTerm(TermList sort, TermList head, TermList* args, unsigned arity, bool shared = true); 
  static TermList createLambdaTerm(TermList varSort, TermList termSort, TermList term); 
  static TermList getDeBruijnIndex(int index, TermList sort);
  static TermList getNthArg(TermList arrowSort, unsigned argNum);
  static TermList getResultApplieadToNArgs(TermList arrowSort, unsigned argNum);
  //Broken!
  static TermList headSort(TermList app);
  static unsigned getArity(TermList sort);
  static void getHeadAndAllArgs(TermList term, TermList& head, TermStack& args); 
  static void getHeadAndArgs(TermList term, TermList& head, TermStack& args); 
  static void getHeadAndArgs(Term* term, TermList& head, TermStack& args);  
  static void getHeadAndArgs(const Term* term, TermList& head, Deque<TermList>& args); 
  static void getHeadSortAndArgs(TermList term, TermList& head, TermList& headSort, TermStack& args);
  static void getArgSorts(TermList t, TermStack& sorts); 
  static Signature::Proxy getProxy(const TermList t);
  static bool isBool(TermList t);
  static bool isTrue(TermList term);
  static bool isFalse(TermList term);
};

#endif

#endif // __ApplicativeHelper__

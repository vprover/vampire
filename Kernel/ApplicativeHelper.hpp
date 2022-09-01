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

// reduce a term to normal form
// uses a applicative order reduction stragegy
// (inner-most left-most redex first)
class BetaNormaliser : public TermTransformer
{
public:

  BetaNormaliser() {
    recurseIntoReplaced();
    dontTransformSorts();
  }  
  TermList normalise(TermList t);
  TermList transformSubterm(TermList t) override;
};

class RedexReducer : public TermTransformer 
{
public:
  TermList reduce(TermList redex);
  TermList transformSubterm(TermList t) override; 
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;

private:
  TermList _t2; // term to replace index with (^x.t1) t2
  unsigned _replace; // index to replace
};

class TermLifter : public TermTransformer
{
public:
  TermList lift(TermList term, unsigned liftBy);
  TermList transformSubterm(TermList t) override; 
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;

private:
  unsigned _cutOff; // any index higher than _cutOff is a free index
  unsigned _liftBy; // the amount to lift a free index by (the number of extra lambdas between it and its binder)
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
  static TermList getResultSort(TermList sort);
  static unsigned getArity(TermList sort);
  static void getHeadAndAllArgs(TermList term, TermList& head, TermStack& args); 
  static void getHeadAndArgs(TermList term, TermList& head, TermStack& args); 
  static void getHeadAndArgs(Term* term, TermList& head, TermStack& args);  
  static void getHeadAndArgs(const Term* term, TermList& head, Deque<TermList>& args); 
  static void getHeadSortAndArgs(TermList term, TermList& head, TermList& headSort, TermStack& args); 
  static Signature::Proxy getProxy(const TermList t);
  static TermList getHead(TermList t);
  static TermList getHead(Term* t);  
  static bool isBool(TermList t);
  static bool isTrue(TermList term);
  static bool isFalse(TermList term);
  static bool isRedex(TermList term);
};

#endif // __ApplicativeHelper__

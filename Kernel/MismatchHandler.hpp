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
 * @file MismatchHandler.hpp
 * Defines class MismatchHandler.
 *
 */

#ifndef __MismatchHandler__
#define __MismatchHandler__

#include "Forwards.hpp"
#include "Shell/Options.hpp"
#include "Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/MaybeBool.hpp"
#include "Lib/BiMap.hpp"

namespace Kernel
{

class AtomicMismatchHandler 
{
public:

  virtual ~AtomicMismatchHandler();

  // Returns true if <t1, t2> can form a constraint
  // Implementors NEED to override this function with
  // their specific logic. 
  // It shold be possible to make use of isConstraintTerm() here
  virtual bool isConstraintPair(TermList t1, TermList t2) = 0;
  virtual TermList transformSubterm(TermList t) = 0;

  // With polymorphism, a term may end up being a constraint term
  // depending on type substitutions.
  // Also a term such as f(a,b) : $int may be a constraint term 
  // but we also want to unify against it.
  //
  // Implementors of this function need to be aware of the following:
  // - when a term t is inserted into a substitution tree that uses a handler
  //   this function is run on t. 
  //   + If it returns true, we subsequently ONLY create constraints with t and 
  //     do not try and unify with t (unless the query term is a variable)
  //   + If it returns false, we ONLY unify and do not create constraints with t
  //   + If it returns maybe we will attempt to do BOTH. Unify query terms with t
  //     and create constraints.
  // - Similarly, when we query with a term trm, we run this function on trm
  //   + If it returns true, we ONLY attempt to find constraint partners for trm
  //   + If it returns false, we ONLY attempt to find unification partners for trm
  //   + If it returns maybe, we attempt to find BOTH type of partners for trm
  // - It may be convenient to use this function in the implementation of transformSubterm
  //   View UWAMismatchHandler::transformSubterm() for an example of this
  virtual MaybeBool isConstraintTerm(TermList t) = 0;
  VSpecVarToTermMap* getTermMap() { return &_termMap; }
protected:
  VSpecVarToTermMap _termMap;
};

/**
 * Meta handler
 * Invariant: for all handlers in _inner, a maximum of ONE handler
 * can return a non-false value on a call to isConstraintTerm 
 */
class MismatchHandler : 
  public TermTransformer
{
public:

  MismatchHandler() : TermTransformer(false) {}

  // Returns true if the mismatch can be handled by some handler
  //
  // Implementors do NOT need to override this function. Only the composite handler
  // needs to.
  bool handle(TermList t1, unsigned index1, 
              TermList t2, unsigned index2, 
              UnificationConstraintStack& ucs, BacktrackData& bd, bool recording);

  TermList transformSubterm(TermList trm) override;
  MaybeBool isConstraintTerm(TermList t); 
  Term* get(unsigned var);

  void addHandler(unique_ptr<AtomicMismatchHandler> hndlr);

  CLASS_NAME(MismatchHandler);
  USE_ALLOCATOR(MismatchHandler);

private:
  void introduceConstraint(
      TermList t1, unsigned index1, 
      TermList t2, unsigned index2, 
      UnificationConstraintStack& ucs, BacktrackData& bd, bool recording);

  Stack<unique_ptr<AtomicMismatchHandler>> _inners;
};

class UWAMismatchHandler : public AtomicMismatchHandler
{
public:
  UWAMismatchHandler(Shell::Options::UnificationWithAbstraction mode) : _mode(mode) {}
  ~UWAMismatchHandler() override {}

  bool isConstraintPair(TermList t1, TermList t2) override; 
  TermList transformSubterm(TermList trm) override;
  MaybeBool isConstraintTerm(TermList t) override; 

  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);
private:
  bool checkUWA(TermList t1, TermList t2); 
  Shell::Options::UnificationWithAbstraction const _mode;
};

class HOMismatchHandler : public AtomicMismatchHandler
{
public:
  HOMismatchHandler() {}
  ~HOMismatchHandler() override {}
  
  bool isConstraintPair(TermList t1, TermList t2) override;
  TermList transformSubterm(TermList trm) override;
  MaybeBool isConstraintTerm(TermList t) override; 

  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);
};


}
#endif /*__MismatchHandler__*/

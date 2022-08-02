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
#include "Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/MaybeBool.hpp"
#include "Lib/BiMap.hpp"

namespace Kernel
{

class MismatchHandler : public TermTransformer
{
public:

  MismatchHandler() : TermTransformer(false) {}

  // returns true if the mismatch was handled.
  virtual bool handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
    UnificationConstraintStack& ucs, BacktrackData& bd, bool recording) = 0;
  virtual TermList transformSubterm(TermList t) = 0;

  // With polymorphism, a term may end up being a constraint term
  // depending on type substitutions.
  // Also a term such as f(a,b) : $int may be a constraint term
  virtual MaybeBool isConstraintTerm(TermList t) = 0;

  bool areIdentical(Term* t1, Term* t2, unsigned idx1, unsigned idx2);

  virtual Term* get(unsigned var){ NOT_IMPLEMENTED; }

  VSpecVarToTermMap* getTermMap() { return &_termMap; }

protected: 
  virtual bool introduceConstraint(TermList t1,unsigned index1, TermList t2, unsigned index2, 
    UnificationConstraintStack& ucs, BacktrackData& bd, bool recording);
  
  VSpecVarToTermMap _termMap;
};

/**
 * Meta handler
 * Invariant: for all handlers in _inner, a maximum of ONE handler
 * can return a non-false value on a call to isConstraintTerm 
 */
class CompositeMismatchHandler : 
  public MismatchHandler
{
public:

  ~CompositeMismatchHandler();
  virtual bool handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
    UnificationConstraintStack& ucs, BacktrackData& bd, bool recording) override;
  TermList transformSubterm(TermList trm) override;
  MaybeBool isConstraintTerm(TermList t) override; 
  Term* get(unsigned var) override;

  void addHandler(MismatchHandler* hndlr);

  CLASS_NAME(CompositeMismatchHandler);
  USE_ALLOCATOR(CompositeMismatchHandler);

private:
  typedef List<MismatchHandler*> MHList;
  MHList* _inners;
};

class UWAMismatchHandler : public MismatchHandler
{
public:
  UWAMismatchHandler() {}
  virtual bool handle(TermList t1, unsigned index1, TermList t2, unsigned index2,
    UnificationConstraintStack& ucs, BacktrackData& bd,  bool recording) override;
  TermList transformSubterm(TermList trm) override;

  MaybeBool isConstraintTerm(TermList t) override; 

  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);
private:
  bool checkUWA(TermList t1, TermList t2); 
};

class HOMismatchHandler : public MismatchHandler
{
public:
  HOMismatchHandler() {}
  
  virtual bool handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
    UnificationConstraintStack& ucs, BacktrackData& bd, bool recording) override;
  TermList transformSubterm(TermList trm) override;
  MaybeBool isConstraintTerm(TermList t) override; 

  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);
};


}
#endif /*__MismatchHandler__*/

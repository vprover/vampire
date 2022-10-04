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
#include "Shell/Options.hpp"

namespace Kernel
{

class MismatchHandler
{
public:
  // returns true if the mismatch was handled.
  virtual bool handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2) = 0;
};

class UWAMismatchHandler : public MismatchHandler
{
public:
  UWAMismatchHandler(Shell::Options::UnificationWithAbstraction mode, Stack<UnificationConstraint>& c) : _mode(mode), _constraints(c) /*, specialVar(0)*/ {}
  virtual bool handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2);

  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);

  bool checkUWA(TermList t1, TermList t2); 
private:
  virtual bool introduceConstraint(TermList t1,unsigned index1, TermList t2, unsigned index2);

  const Shell::Options::UnificationWithAbstraction _mode;
  Stack<UnificationConstraint>& _constraints;
};

class HOMismatchHandler : public MismatchHandler
{
public:
  HOMismatchHandler(UnificationConstraintStack& c) : _constraints(c) {}
  
  virtual bool handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2);

  CLASS_NAME(HOMismatchHandler);
  USE_ALLOCATOR(HOMismatchHandler);

private:

  Stack<UnificationConstraint>& _constraints;
};


}
#endif /*__MismatchHandler__*/

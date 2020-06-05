
/*
 * File MismatchHandler.hpp.
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
 * @file MismatchHandler.hpp
 * Defines class MismatchHandler.
 *
 */

#ifndef __MismatchHandler__
#define __MismatchHandler__

#include "Forwards.hpp"
#include "Term.hpp"

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
  UWAMismatchHandler(Stack<UnificationConstraint>& c) : constraints(c), specialVar(0) {}
  virtual bool handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2);

  CLASS_NAME(UWAMismatchHandler);
  USE_ALLOCATOR(UWAMismatchHandler);

private:
  bool checkUWA(TermList t1, TermList t2); 
  virtual bool introduceConstraint(RobSubstitution* subst,TermList t1,unsigned index1, TermList t2, unsigned index2);

  Stack<UnificationConstraint>& constraints;
  unsigned specialVar;
};

}
#endif /*__MismatchHandler__*/

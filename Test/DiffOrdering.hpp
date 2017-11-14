
/*
 * File DiffOrdering.hpp.
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
 * @file DiffOrdering.hpp
 * Defines class DiffOrdering.
 */

#ifndef __DiffOrdering__
#define __DiffOrdering__

#include "Forwards.hpp"

#include "Lib/SmartPtr.hpp"

#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

namespace Test {

using namespace Kernel;

/**
 * An ordering class that takes two orderings and outputs a message
 * if their results differ. The result of the first ordering is always
 * returned.
 */
class DiffOrdering
: public Ordering
{
public:
  DiffOrdering(OrderingSP o1, OrderingSP o2)
  : o1(o1), o2(o2)
  {
  }

  virtual Result compare(Literal* l1,Literal* l2)
  {
    Result r1=o1->compare(l1,l2);
    Result r2=o2->compare(l1,l2);
    return r1;
  }
  virtual Result compare(TermList t1,TermList t2)
  {
    Result r1=o1->compare(t1,t2);
    Result r2=o2->compare(t1,t2);
    return r1;
  }

  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2)
  {
    Comparison r1=o1->compareFunctors(fun1,fun2);
    Comparison r2=o2->compareFunctors(fun1,fun2);    
    return r1;
  }

private:
  OrderingSP o1;
  OrderingSP o2;
};

}

#endif // __DiffOrdering__

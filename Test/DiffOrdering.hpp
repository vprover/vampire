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
    if(r1!=r2) {
      LOGV("----");
      LOGV(*l1);
      LOGV(*l2);
      LOGV(resultToString(r1));
      LOGV(resultToString(r2));
    }
    return r1;
  }
  virtual Result compare(TermList t1,TermList t2)
  {
    Result r1=o1->compare(t1,t2);
    Result r2=o2->compare(t1,t2);
    if(r1!=r2) {
      LOGV("----");
      LOGV(t1);
      LOGV(t2);
      LOGV(resultToString(r1));
      LOGV(resultToString(r2));
    }
    return r1;
  }

  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2)
  {
    Comparison r1=o1->compareFunctors(fun1,fun2);
    Comparison r2=o2->compareFunctors(fun1,fun2);
    if(r1!=r2) {
      LOGV("----");
      LOGV(env.signature->functionName(fun1));
      LOGV(env.signature->functionName(fun2));
      LOGV(r1);
      LOGV(r2);
    }
    return r1;
  }

private:
  OrderingSP o1;
  OrderingSP o2;
};

}

#endif // __DiffOrdering__

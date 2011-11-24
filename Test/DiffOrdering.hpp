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
      TRACE("ord_diff",
	  tout << "lit1: " << *l1 << endl;
	  tout << "lit2: " << *l2 << endl;
	  tout << "res1: " << resultToString(r1) << endl;
	  tout << "res2: " << resultToString(r2) << endl;
      );
    }
    return r1;
  }
  virtual Result compare(TermList t1,TermList t2)
  {
    Result r1=o1->compare(t1,t2);
    Result r2=o2->compare(t1,t2);
    if(r1!=r2) {
      TRACE("ord_diff",
	  tout << "trm1: " << t1 << endl;
	  tout << "trm2: " << t2 << endl;
	  tout << "res1: " << resultToString(r1) << endl;
	  tout << "res2: " << resultToString(r2) << endl;
      );
    }
    return r1;
  }

  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2)
  {
    Comparison r1=o1->compareFunctors(fun1,fun2);
    Comparison r2=o2->compareFunctors(fun1,fun2);
    if(r1!=r2) {
      TRACE("ord_diff",
	  tout << "fun1: " << env.signature->functionName(fun1) << endl;
	  tout << "fun2: " << env.signature->functionName(fun2) << endl;
	  tout << "res1: " << r1 << endl;
	  tout << "res2: " << r2 << endl;
      );
    }
    return r1;
  }

private:
  OrderingSP o1;
  OrderingSP o2;
};

}

#endif // __DiffOrdering__

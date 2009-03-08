/**
 * @file CompositeLiteralComparator.hpp
 * Defines class CompositeLiteralComparator and some other atomic
 * literal comparator classes.
 */

#ifndef __CompositeLiteralComparator__
#define __CompositeLiteralComparator__

#include "../Lib/Comparison.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

template<class Comp1, class Comp2>
class CompositeLiteralComparator
{
public:
  Comparison compare(Literal* l1, Literal* l2)
  {
    Comparison res1=_c1.compare(l1,l2);
    return (res1==EQUAL)?_c2.compare(l1,l2):res1;
  }
private:
  Comp1 _c1;
  Comp2 _c2;
};

}

#endif /* __CompositeLiteralComparator__ */

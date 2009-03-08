/**
 * @file CompositeLiteralComparator.hpp
 * Defines namespace Kernel::LiteralComparators containing atomic
 * literal comparator classes.
 */

#ifndef __CompositeLiteralComparator__
#define __CompositeLiteralComparator__

#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"

#include "Term.hpp"

namespace Kernel {
namespace LiteralComparators {

using namespace Lib;

template<class Comp1, class Comp2>
class Composite
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

template<class Comp>
class Inverse
{
public:
  Comparison compare(Literal* l1, Literal* l2)
  {
    return static_cast<Comparison>(-_c.compare(l1,l2));
  }
private:
  Comp _c;
};

struct NoPositiveEquality
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    bool l1PE=l1->isEquality()&&l1->isPositive();
    bool l2PE=l2->isEquality()&&l2->isPositive();
    if( l1PE && !l2PE ) {
      return LESS;
    } else if( !l1PE && l2PE ) {
      return GREATER;
    } else {
      return EQUAL;
    }
  }
};

struct MaximalSize
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    return Int::compare(l1->weight(), l2->weight());
  }
};

struct LeastTopLevelVariables
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    return static_cast<Comparison>(-Int::compare(getTLVarCnt(l1), getTLVarCnt(l2)));
  }
private:
  unsigned getTLVarCnt(Literal* l)
  {
    unsigned res;
    for(TermList* arg=l->args(); arg->isNonEmpty(); arg=arg->next()) {
      if(arg->isVar()) {
	res++;
      }
    }
    return res;
  }
};

}
}

#endif /* __CompositeLiteralComparator__ */

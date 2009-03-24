/**
 * @file CompositeLiteralComparator.hpp
 * Defines namespace Kernel::LiteralComparators containing atomic
 * literal comparator classes.
 */

#ifndef __CompositeLiteralComparator__
#define __CompositeLiteralComparator__

#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"

#include "LiteralSelector.hpp"
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
    return _c.compare(l2,l1);
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

struct Negative
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    bool l1N=l1->isNegative();
    bool l2N=l2->isNegative();
    if( l1N && !l2N ) {
      return GREATER;
    } else if( !l1N && l2N ) {
      return LESS;
    } else {
      return EQUAL;
    }
  }
};

struct NegativeEquality
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    bool l1NE=l1->isEquality()&&l1->isNegative();
    bool l2NE=l2->isEquality()&&l2->isNegative();
    if( l1NE && !l2NE ) {
      return GREATER;
    } else if( !l1NE && l2NE ) {
      return LESS;
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

struct LeastVariables
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    return Int::compare(l2->vars(), l1->vars());
  }
};

struct LeastDistinctVariables
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    return Int::compare(l2->getDistinctVars(), l1->getDistinctVars());
  }
};

struct LeastTopLevelVariables
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    return Int::compare(getTLVarCnt(l2), getTLVarCnt(l1));
  }
private:
  unsigned getTLVarCnt(Literal* l)
  {
    unsigned res=0;
    for(TermList* arg=l->args(); arg->isNonEmpty(); arg=arg->next()) {
      if(arg->isVar()) {
	res++;
      }
    }
    return res;
  }
};

struct LexComparator
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    ASS(l1->shared());
    ASS(l2->shared());

    if(l1->header()!=l2->header()) {
      return Int::compare(l1->header(),l2->header());
    }

    Term::SubtermIterator sit1(l1);
    Term::SubtermIterator sit2(l2);
    while(sit1.hasNext()) {
      ASS(sit2.hasNext());
      TermList st1=sit1.next();
      TermList st2=sit2.next();
      if(st1.isTerm()) {
	if(st2.isTerm()) {
	  unsigned f1=st1.term()->functor();
	  unsigned f2=st2.term()->functor();
	  if(f1!=f2) {
	    return Int::compare(f1,f2);
	  }
	} else {
	  return GREATER;
	}
      } else {
	if(st2.isTerm()) {
	  return LESS;
	} else {
	  if(st1.var()!=st2.var()) {
	    return Int::compare(st1.var(),st2.var());
	  }
	}
      }
    }
    ASS(l1==l2);
    return EQUAL;
  }
};

}
}

#endif /* __CompositeLiteralComparator__ */

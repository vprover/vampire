/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __REBALANCING_H__
#define __REBALANCING_H__

#include <iostream>
#include "Lib/Environment.hpp"
#include "Forwards.hpp"
#include "SortHelper.hpp"


#define DEBUG(...) // DBG(__VA_ARGS__)

#define CALL_DBG(...) CALL(__VA_ARGS__)

namespace Kernel {
  namespace Rebalancing {

    template<class FunctionInverter> class Balancer;
    template<class FunctionInverter> class BalanceIter;


    struct Node;
    class InversionContext;

    struct Node {
      Node(const Term& term, unsigned index) : _term(&term), _index(index) {}
      const Term& term() const { return *_term; }
      unsigned index() const { return _index; };

      TermList operator*() const { 
        ASS(inBounds());
        return *_term->nthArgument(_index);
      }      

      bool inBounds() const { 
        return _index < _term->arity();
      }

    private:
      template<class C>
      friend class BalanceIter;
      Term const* const _term;
      unsigned _index;
    };

    template<class C> 
    class Balancer {
      const Literal& _lit;
      friend class BalanceIter<C>;
    public:
      Balancer(const Literal& l);
      BalanceIter<C> begin() const;
      BalanceIter<C> end() const;
    };

    std::ostream& operator<<(std::ostream& out, const Node&);

    /** An iterator over all possible rebalancings of a literal. 
     * For example iterating over `x * 7 = y + 1`  gives the formulas
     * x = (y + 1) / 7
     * y = (x * 7) - 1
     *
     * This class is designed for (and only for) being used as an stdlib 
     * iterator. i.e. it is meant to be used in for loops:
     * for ( auto x : Balancer<...>(lit) ) {
     *   auto lhs = lit.lhs();
     *   auto rhs = lit.buildRhs();
     *   auto literal = lit.build();
     *   ... do stuff 
     * }
     */
    template<class C> class BalanceIter {

      /* "call-stack". top of the stack is the term that is currently being traversed. */
      Stack<Node> _path;
      /* index of the side of the equality that is to be investigated next. i.e.:
       */
      unsigned _litIndex;
      const Balancer<C>& _balancer;

      friend class Balancer<C>;
      BalanceIter(const Balancer<C>&, bool end);

      bool inBounds() const;
      void findNextVar();
      TermList derefPath() const;
      void incrementPath();
      bool canInvert() const;
    public:
      void operator++();
      const BalanceIter& operator*() const;
      template<class D>
      friend bool operator!=(const BalanceIter<D>&, const BalanceIter<D>&);

      TermList lhs() const;
      TermList buildRhs() const;
      Literal& build() const;
    };

    class InversionContext {
      const Term& _toInvert;
      const TermList _toWrap;
      const unsigned _unwrapIdx;
      public: 
      friend std::ostream& operator<<(std::ostream& out, const InversionContext&);
      InversionContext(const Term& toInvert, unsigned unwrapIdx, const TermList toWrap) : 
        _toInvert(toInvert),
        _toWrap(toWrap),
        _unwrapIdx(unwrapIdx)
      { }
      TermList toWrap() const { return _toWrap; }
      TermList toUnwrap() const { return _toInvert[_unwrapIdx]; }
      const Term& topTerm() const { return _toInvert; }
      unsigned topIdx() const { return _unwrapIdx; }
    };


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////// IMPLEMENTATION
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class C> 
Balancer<C>::Balancer(const Literal& l) : _lit(l) { }

template<class C> BalanceIter<C>::BalanceIter(const Balancer<C>& balancer, bool end) 
  : _path(Stack<Node>())
  , _litIndex(end ? 2 : 0)
  , _balancer(balancer)
{
  CALL_DBG("BalanceIter()")
  if (end) {
    DEBUG("end")
  } else {
    DEBUG("begin(", balancer._lit.toString(), ")");
    ASS(balancer._lit.isEquality())
    findNextVar();
  }
}

template<class C> 
BalanceIter<C> Balancer<C>::begin() const {
  return BalanceIter<C>(*this, false);
}

template<class C> 
BalanceIter<C> Balancer<C>::end() const {
  return BalanceIter<C>(*this, true);
}


template<class C> bool BalanceIter<C>::inBounds() const
{ 
  return _litIndex < 2;
}

template<class C> TermList BalanceIter<C>::derefPath() const 
{ 
  ASS(_litIndex < 2);
  if (_path.isEmpty()) {
    return _balancer._lit[_litIndex];

  } else {
    auto node = _path.top();
    return node.term()[node.index()];
  }
}

template<class C> bool BalanceIter<C>::canInvert() const 
{
  CALL("Balancer::canInver()")
  if (_path.isEmpty()) {
    DEBUG("can invert empty")
    return true;/* <- we can 'invert' an equality by doing nothing*/
  } else {
    auto ctxt = InversionContext(_path.top().term(), _path.top().index(), _balancer._lit[1 - _litIndex]);
    return C::canInvertTop(ctxt);
  }
}

/** moves to the next invertible point in the term */
template<class C> void BalanceIter<C>::incrementPath() 
{ 
  CALL_DBG("BalanceIter::incrementPath")

  auto peak = [&]() -> Node& { return _path.top(); };
  auto incPeak = [&]() {
     ++peak()._index;
     DEBUG("peakIndex := ", peak().index());
  };
  auto incLit = [&]() {
    _litIndex++;
    DEBUG("_litIndex := ", _litIndex)
  };
  auto inc = [&]() {
    if (_path.isEmpty()) 
      incLit();
    else 
      incPeak();
  };
  do {

    if ( derefPath().isTerm()  
        && derefPath().term()->arity() > 0 
        && canInvert()) {

      DEBUG("push")
      _path.push(Node(*derefPath().term(), 0));

    } else {
      DEBUG("inc")

      if (_path.isEmpty()) {
        incLit();

      } else {
        /* we inspecte the next term in the same side of the equality */

          incPeak();
          if (!peak().inBounds()) {
            /* index invalidated.  */
            
            do {
                _path.pop();
                DEBUG("pop()")
                inc();
                
            } while (!_path.isEmpty() && !peak().inBounds());
          }
      }
    }
  } while (!canInvert() && inBounds());
}

template<class C> void BalanceIter<C>::findNextVar() 
{ 
  CALL_DBG("BalanceIter::findNextVar")

  while(inBounds() && !derefPath().isVar() ) {
    incrementPath();
  }
}

template<class C> void BalanceIter<C>::operator++() { 
  CALL_DBG("BalanceIter::operator++")
  incrementPath();
  if (inBounds())
    findNextVar();
}


template<class C> 
const BalanceIter<C>& BalanceIter<C>::operator*() const { 
  CALL_DBG("BalanceIter::operator*")
  DEBUG(lhs())
  return *this;
}

template<class C> 
bool operator!=(const BalanceIter<C>& lhs, const BalanceIter<C>& rhs) { 
  CALL_DBG("BalanceIter::operator!=")
  ASS(rhs._path.isEmpty());
  auto out = lhs.inBounds();//!lhs._path.isEmpty() || lhs._litIndex != 2;
  return out;
}


template<class C> 
TermList BalanceIter<C>::lhs() const 
{
  // CALL_DBG("BalanceIter::lhs")
  auto out = derefPath();
  ASS_REP(out.isVar(), out);
  // DEBUG(out)
  return out;
}
   
template<class C> 
TermList BalanceIter<C>::buildRhs() const { 
  ASS(_balancer._lit.arity() == 2 && _litIndex < 2)
  TermList rhs = _balancer._lit[1 - _litIndex];
  for (auto n : _path) {
    auto ctxt = InversionContext(n.term(), n.index(), rhs);
    rhs = C::invertTop(ctxt);
  }
  return rhs;
}

template<class C> 
Literal& BalanceIter<C>::build() const { 
  return Literal::createEquality(_balancer._lit.polarity(), lhs(), buildRhs(), SortHelper::getTermSort(lhs(), &_balancer._lit));
}

} // namespace Rebalancing

} // namespace Kernel
#undef DEBUG

#endif // __REBALANCING_H__


#ifndef __REBALANCING_H__
#define __REBALANCING_H__

#include <iostream>
#include "num_traits.hpp"

#include "Lib/Environment.hpp"
#include "Forwards.hpp"

#include "Rebalancing.hpp"
#include "num_traits.hpp"

#define DEBUG(...) //CallDbg::writeIndent(cout) << __VA_ARGS__ << endl;
#define DEBUG_ME DEBUG("############  "  << _path << " -> " << pointedAt() << " litIndex: " << _litIndex)

#define CALL_DBG(...) CALL(__VA_ARGS__); CallDbg x(__VA_ARGS__); 

struct CallDbg {
  static unsigned indent; 
  const char* const _msg;
  static std::ostream& writeIndent(std::ostream& out) {
    for (auto i = 0; i < indent; i++) {
      out << "\t";
    }
    return out;
  }
  CallDbg(decltype(_msg) msg)  : _msg(msg) {
    DEBUG("START " << _msg)
    indent++;
  }  
  ~CallDbg() {
    indent--;
    DEBUG("END   " << _msg)
  }
};
unsigned CallDbg::indent = 0;

namespace Kernel {
  namespace Rebalancing {

    template<class ConstantType> class Balancer;
    template<class ConstantType> class BalanceIter;
    template<class ConstantType> class Balance;

    template<class C> 
    class Balancer {
      const Literal& _lit;
      friend class BalanceIter<C>;
    public:
      Balancer(const Literal& l);
      BalanceIter<C> begin() const;
      BalanceIter<C> end() const;
    };

    struct Node {
      unsigned index;
      Term const* const _term;
      const Term& term() const { return *_term; }
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
      using number = num_traits<C>;

      /* "call-stack". top of the stack is the term that is currently being traversed. */
      Stack<Node> _path;
      /* index of the side of the equality that is to be investigated next. i.e.:
       */
      unsigned _litIndex;
      const Balancer<C>& _balancer;

      friend class Balancer<C>;
      BalanceIter(const Balancer<C>&, bool end);

      bool inRange() const;
      void findNextVar();
      TermList pointedAt() const;
      void incrementPtr();
    public:
      void operator++();
      const BalanceIter& operator*() const;
      template<class D>
      friend bool operator!=(const BalanceIter<D>&, const BalanceIter<D>&);

      TermList lhs() const;
      TermList buildRhs() const;
      Literal& build() const;
    };

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////// IMPLEMENTATION
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// namespace Kernel {
//
// namespace Rebalancing {
//
#define UNIMPLEMENTED \
  ASSERTION_VIOLATION

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
    DEBUG(balancer._lit);
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


template<class C> bool BalanceIter<C>::inRange() const
{ 
  return _litIndex < 2;
}

template<class C> TermList BalanceIter<C>::pointedAt() const 
{ 
  ASS(_litIndex < 2);
  if (_path.isEmpty()) {
    return _balancer._lit[_litIndex];

  } else {
    auto node = _path.top();
    return node.term()[node.index];
  }
}


template<class C> void BalanceIter<C>::incrementPtr() 
{ 
  CALL_DBG("BalanceIter::incrementPtr")

  auto canInvert = [this]() -> bool { return pointedAt().isTerm() && pointedAt().term()->arity() > 0  && true; };//TODO
  auto peak = [&]() -> Node& { return _path.top(); };

  if (canInvert()) {
    DEBUG("push")
    _path.push(Node {
        ._term = pointedAt().term(),
        .index = 0,
    });
    return;
  } else {
  while (true) {
    if (_path.isEmpty()) {
      _litIndex++;
      DEBUG("_litIndex := " << _litIndex)
      if (_litIndex > 1) {
        /* we have already inspected the full literal */
        return;

      } else {
        /* we need to inspect one side of the equality */
        // ASS(_balancer._lit[_litIndex].isTerm());
        // _path.push(Node {
        //     ._term = _balancer._lit[_litIndex].term(),
        //     .index = 0,
        // });
        return;
      }

    } else {
      /* we inspecte the next term in the same side of the equality */
      auto index = ++peak().index;
      DEBUG("peakIndex := " << peak().index)
      if (index >= peak().term().arity()) {
        /* index invalidated.  */
        _path.pop();
        DEBUG("pop()")

      } else {

        return;
      }
    }
  }
  }
}

template<class C> void BalanceIter<C>::findNextVar() 
{ 
  CALL_DBG("BalanceIter::findNextVar")

  while(inRange() && !pointedAt().isVar() ) {
    DEBUG_ME
    incrementPtr();
  }
}

template<class C> void BalanceIter<C>::operator++() { 
  CALL_DBG("BalanceIter::operator++")
  // DEBUG_ME
  incrementPtr();
  // if (_path.isEmpty()) {
  //   ASS(_litIndex < 2)
  //   _litIndex++;
  // } else {
  //   _path.top().index += 1;
  //   if (_path.top().index >= _path.top().term().arity()) {
  //     _path.pop();
  //   }
  // }
  if (inRange())
    findNextVar();
}


template<class C> 
const BalanceIter<C>& BalanceIter<C>::operator*() const { 
  CALL_DBG("BalanceIter::operator*")
  return *this;
}

template<class C> 
bool operator!=(const BalanceIter<C>& lhs, const BalanceIter<C>& rhs) { 
  CALL_DBG("BalanceIter::operator!=")
  ASS(rhs._path.isEmpty());
  auto out = lhs.inRange();//!lhs._path.isEmpty() || lhs._litIndex != 2;
  return out;
}


template<class C> 
TermList BalanceIter<C>::lhs() const 
{
  CALL_DBG("BalanceIter::lhs")
  auto out = pointedAt();
  ASS_REP(out.isVar(), out);
  DEBUG(out)
  return out;
}
   
template<class C> 
TermList BalanceIter<C>::buildRhs() const { 
  UNIMPLEMENTED
}
       
template<class C> 
Literal& BalanceIter<C>::build() const { 
  return Literal::createEquality(_balancer._lit.polarity(), lhs(), buildRhs(), number::sort);
}

std::ostream& operator<<(std::ostream& out, const Node& n) {
  out << n.term() << "@" << n.index;
  return out;
}

} // namespace Rebalancing

} // namespace Kernel

#endif // __REBALANCING_H__


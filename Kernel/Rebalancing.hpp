#ifndef __REBALANCING_H__
#define __REBALANCING_H__

#include <iostream>

namespace Kernel {
  namespace Rebalancing {

    template<class ConstantType> class Balancer;
    template<class ConstantType> class BalanceIter;
    template<class ConstantType> class Balance;

    template<class C> 
    class Balancer {
      const Literal& _lit;
    public:
      Balancer(const Literal& l);
      BalanceIter<C> begin() const;
      BalanceIter<C> end() const;
    };
    template<class C> 
    class BalanceIter {

      struct Node {
        unsigned index;
        const Term& term;
      };

      Stack<Node> _path;

      // const Balancer<C>& balancer;
      friend class Balancer<C>;
      BalanceIter(const Balancer<C>&);

    public:
      void operator++();
      const BalanceIter& operator*() const;
      template<class D>
      friend bool operator!=(const BalanceIter<D>&, const BalanceIter<D>&);

      TermList lhs() const;
      TermList buildRhs() const;
      Literal& build() const;
    };

  }
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////// IMPLEMENTATION
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#include "Lib/Environment.hpp"
#include "Forwards.hpp"

#include "Rebalancing.hpp"
#include "num_traits.hpp"

namespace Kernel {

namespace Rebalancing {

#define UNIMPLEMENTED \
  ASSERTION_VIOLATION

template<class C> 
Balancer<C>::Balancer(const Literal& l) : _lit(l) { }

template<class C> 
BalanceIter<C>::BalanceIter(const Balancer<C>& balancer) : _path(Stack<Node>()) {
  UNIMPLEMENTED
}

template<class C> 
BalanceIter<C> Balancer<C>::begin() const {
  return BalanceIter<C>(*this);
}

template<class C> 
BalanceIter<C> Balancer<C>::end() const {
  UNIMPLEMENTED
}

template<class C> 
void BalanceIter<C>::operator++() { 
  UNIMPLEMENTED 
}

template<class C> 
const BalanceIter<C>& BalanceIter<C>::operator*() const { 
  ASS(!_path.isEmpty());
  return *this;
}

template<class C> 
bool operator!=(const BalanceIter<C>& lhs, const BalanceIter<C>& rhs) { 
  UNIMPLEMENTED
}

template<class C> 
TermList BalanceIter<C>::lhs() const { 
  UNIMPLEMENTED
}
   
template<class C> 
TermList BalanceIter<C>::buildRhs() const { 
  UNIMPLEMENTED
}
       
template<class C> 
Literal& BalanceIter<C>::build() const { 
  UNIMPLEMENTED
}

}

}

#endif // __REBALANCING_H__


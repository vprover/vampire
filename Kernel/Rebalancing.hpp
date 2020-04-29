#ifndef __REBALANCING_H__
#define __REBALANCING_H__

#include <iostream>

namespace Kernel {
  namespace Rebalancing {

    template<class ConstantType> class Balancer;
    template<class ConstantType> class BalanceIter;
    template<class ConstantType> class Balance;

    template<class ConstantType> 
    class Balancer {
      const Literal& _lit;
    public:
      Balancer(const Literal& l);
      BalanceIter<ConstantType> begin() const;
      BalanceIter<ConstantType> end() const;
    };
    template<class ConstantType> 
    class BalanceIter {

      struct Node {
        unsigned index;
        const Term& term;
      };

      Stack<Node> path;

      // const Balancer<ConstantType>& balancer;
      friend class Balancer<ConstantType>;
      BalanceIter(const Balancer<ConstantType>&);

    public:
      void operator++();
      Balance<ConstantType> operator*() const;
      template<class C>
      friend bool operator!=(const BalanceIter<C>&, const BalanceIter<C>&);
    };

    template<class ConstantType> 
    class Balance {
    public:
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

template<class Cons> 
Balancer<Cons>::Balancer(const Literal& l) : _lit(l) { }

template<class Cons> 
BalanceIter<Cons>::BalanceIter(const Balancer<Cons>& balancer) {
  UNIMPLEMENTED
}

template<class Cons> 
BalanceIter<Cons> Balancer<Cons>::begin() const {
  return BalanceIter<Cons>(*this);
}

template<class Cons> 
BalanceIter<Cons> Balancer<Cons>::end() const {
  UNIMPLEMENTED
}

template<class Cons> 
void BalanceIter<Cons>::operator++() { 
  UNIMPLEMENTED 
}

template<class Cons> 
Balance<Cons> BalanceIter<Cons>::operator*() const { 
  UNIMPLEMENTED
}

template<class Cons> 
bool operator!=(const BalanceIter<Cons>& lhs, const BalanceIter<Cons>& rhs) { 
  UNIMPLEMENTED
}

template<class Cons> 
TermList Balance<Cons>::lhs() const { 
  UNIMPLEMENTED
}
   
template<class Cons> 
TermList Balance<Cons>::buildRhs() const { 
  UNIMPLEMENTED
}
       
template<class Cons> 
Literal& Balance<Cons>::build() const { 
  UNIMPLEMENTED
}

}

}

#endif // __REBALANCING_H__


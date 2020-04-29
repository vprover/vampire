#ifndef __REBALANCING_H__
#define __REBALANCING_H__

#include <iostream>

namespace Kernel {
  namespace Rebalancing {

    class Balancer;
    class BalanceIter;
    class Balance;

    class Balancer {
    public:
      Balancer(Literal& l);
      BalanceIter begin() const;
      BalanceIter end() const;
    };

    class BalanceIter {
    public:
      void operator++();
      Balance operator*() const;
      friend bool operator!=(const BalanceIter&, const BalanceIter&);
    };

    class Balance {
    public:
      TermList lhs() const;
      TermList buildRhs() const;
      Literal& build() const;
    };

  }
}

#endif // __REBALANCING_H__


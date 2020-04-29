

#include "Lib/Environment.hpp"
#include "Forwards.hpp"

#include "Rebalancing.hpp"
#include "num_traits.hpp"

using namespace Kernel;
using namespace Kernel::Rebalancing;

#define UNIMPLEMENTED \
  ASSERTION_VIOLATION

Balancer::Balancer(Literal& l) {
  UNIMPLEMENTED
}

BalanceIter Balancer::begin() const {
  UNIMPLEMENTED
}

BalanceIter Balancer::end() const {
  UNIMPLEMENTED
}

void BalanceIter::operator++() { 
  UNIMPLEMENTED 
}

Balance BalanceIter::operator*() const { 
  UNIMPLEMENTED
}

bool Kernel::Rebalancing::operator!=(const BalanceIter& lhs, const BalanceIter& rhs) { 
  UNIMPLEMENTED
}

TermList Balance::lhs() const { 
  UNIMPLEMENTED
}
   
TermList Balance::buildRhs() const { 
  UNIMPLEMENTED
}
       
Literal& Balance::build() const { 
  UNIMPLEMENTED
}
       



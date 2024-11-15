/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file IntegerFourierMotzkin.hpp
 * Defines class IntegerFourierMotzkin
 *
 */

#ifndef __LASCA_IntegerFourierMotzkin__
#define __LASCA_IntegerFourierMotzkin__

#include "FourierMotzkin.hpp"
#include "Coherence.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing; using namespace Saturation;

template<class NumTraits>
struct IntegerFourierMotzkinConf
{
  IntegerFourierMotzkinConf(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
  {  }

  using Premise0 = FourierMotzkin::Lhs;
  using Premise1 = FourierMotzkin::Rhs;
  using Premise2 = typename Coherence<NumTraits>::Lhs;

  auto applyRule(
      Premise0 const& prem0, unsigned varBank0,
      Premise1 const& prem1, unsigned varBank1,
      Premise2 const& prem2, unsigned varBank2,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(prem0, varBank0, 
                      prem1, varBank1,
                      prem2, varBank2, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      Premise0 const& prem0, unsigned varBank0,
      Premise1 const& prem1, unsigned varBank1,
      Premise2 const& prem2, unsigned varBank2,
      AbstractingUnifier& uwa) const
  // TODO
  { return assertionViolation<Option<Clause*>>(); }

  std::shared_ptr<LascaState> _shared;
};

template<class NumTraits>
struct IntegerFourierMotzkin : public TriInf<IntegerFourierMotzkinConf<NumTraits>>  {
  IntegerFourierMotzkin(std::shared_ptr<LascaState> state) 
    : TriInf<IntegerFourierMotzkinConf<NumTraits>>(state, IntegerFourierMotzkinConf<NumTraits>(state)) {}
};

} // namespace LASCA 
} // namespace Inferences 


#endif /*__LASCA_IntegerFourierMotzkin__*/

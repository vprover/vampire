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
 * @file VariableElimination.hpp
 * Defines class VariableElimination
 *
 */

#ifndef __VariableElimination__
#define __VariableElimination__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VariableElimination
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(VariableElimination);
  USE_ALLOCATOR(VariableElimination);

  VariableElimination(VariableElimination&&) = default;
  VariableElimination(shared_ptr<LascaState> shared, bool simplify) 
    : _shared(std::move(shared))
    , _simplify(simplify)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  template<class NumTraits>
  struct FoundVarInLiteral {
    FoundVarInLiteral(
      unsigned idx,
      typename NumTraits::ConstantType numeral,
      LascaLiteral<NumTraits> literal) : idx(idx)
          , numeral(numeral)
          , literal(literal) {}

    unsigned idx;
    typename NumTraits::ConstantType numeral;
    LascaLiteral<NumTraits> literal;
  };

  template<class NumTraits>
  struct FoundVariable 
  {
    FoundVariable(MonomFactors<NumTraits> var) : var(var), posIneq(), negIneq(), eq(), neq() {}
    FoundVariable(FoundVariable&&) = default;
    FoundVariable& operator=(FoundVariable&&) = default;
    MonomFactors<NumTraits> var;
    Stack<FoundVarInLiteral<NumTraits>> posIneq;
    Stack<FoundVarInLiteral<NumTraits>> negIneq;
    Stack<FoundVarInLiteral<NumTraits>> eq;
    Stack<FoundVarInLiteral<NumTraits>> neq;

    bool isOneSideBounded() const
    {
      return (this->posIneq.size() != 0 && this->negIneq.size() == 0 && this->eq.size() == 0 && this->neq.size() == 0)
          || (this->posIneq.size() == 0 && this->negIneq.size() != 0 && this->eq.size() == 0 && this->neq.size() == 0); }
  };


  using AnyFoundVariable = Coproduct< FoundVariable< IntTraits> 
                                    , FoundVariable< RatTraits> 
                                    , FoundVariable<RealTraits> 
                                    >;

  Option<AnyFoundVariable> findUnshieldedVar(Clause* premise) const;

                            ClauseIterator applyRule(Clause* premise, FoundVariable<IntTraits> found) const { return ClauseIterator::getEmpty(); };
  template<class NumTraits> ClauseIterator applyRule(Clause* premise, FoundVariable<NumTraits> found) const;

  ClauseGenerationResult generateSimplify(Clause* premise)  final override;
  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  static auto isOneSideBounded(AnyFoundVariable const& v)
  { return v.apply([](auto& v) { return v.isOneSideBounded(); }); }

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  shared_ptr<LascaState> _shared;
  const bool _simplify;
};

} // namespace LASCA 
} // namespace Inferences 

// lalalalala
#endif /*__VariableElimination__*/
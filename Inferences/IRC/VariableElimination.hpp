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
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace IRC {

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
  VariableElimination(shared_ptr<IrcState> shared, bool simplify) 
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
      IrcLiteral<NumTraits> literal) : idx(idx)
          , numeral(numeral)
          , literal(literal) {}

    unsigned idx;
    typename NumTraits::ConstantType numeral;
    IrcLiteral<NumTraits> literal;
  };

  template<class NumTraits>
  struct FoundVariable 
  {
    FoundVariable(Perfect<MonomFactors<NumTraits>> var) : var(var), posIneq(), negIneq(), eq(), neq() {}
    FoundVariable(FoundVariable&&) = default;
    FoundVariable& operator=(FoundVariable&&) = default;
    Perfect<MonomFactors<NumTraits>> var;
    Stack<FoundVarInLiteral<NumTraits>> posIneq;
    Stack<FoundVarInLiteral<NumTraits>> negIneq;
    Stack<FoundVarInLiteral<NumTraits>> eq;
    Stack<FoundVarInLiteral<NumTraits>> neq;
  };

  using AnyFoundVariable = Coproduct< FoundVariable< IntTraits> 
                                    , FoundVariable< RatTraits> 
                                    , FoundVariable<RealTraits> 
                                    >;

  Option<AnyFoundVariable> findUnshieldedVar(Clause* premise) const;

                            ClauseIterator eliminateVar(Clause* premise, FoundVariable<IntTraits> found) const { return ClauseIterator::getEmpty(); };
  template<class NumTraits> ClauseIterator eliminateVar(Clause* premise, FoundVariable<NumTraits> found) const;

  ClauseGenerationResult generateSimplify(Clause* premise)  final override;
  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  shared_ptr<IrcState> _shared;
  const bool _simplify;
};

} // namespace IRC 
} // namespace Inferences 

// lalalalala
#endif /*__VariableElimination__*/

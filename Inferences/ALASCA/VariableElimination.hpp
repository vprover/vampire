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
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VariableElimination
{
public:
  USE_ALLOCATOR(VariableElimination);

  VariableElimination(VariableElimination&&) = default;
  VariableElimination(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  template<class NumTraits>
  struct FoundVarInLiteral {
    FoundVarInLiteral(
      unsigned idx,
      typename NumTraits::ConstantType numeral,
      AlascaLiteralItp<NumTraits> literal) : idx(idx)
          , numeral(numeral)
          , literal(literal) {}

    unsigned idx;
    typename NumTraits::ConstantType numeral;
    AlascaLiteralItp<NumTraits> literal;
  };

  template<class NumTraits>
  struct FoundVariable 
  {
    FoundVariable(TermList var) : var(var), posIneq(), negIneq(), eq(), neq() {}
    FoundVariable(FoundVariable&&) = default;
    FoundVariable& operator=(FoundVariable&&) = default;
    TermList var;
    Stack<FoundVarInLiteral<NumTraits>> posIneq;
    Stack<FoundVarInLiteral<NumTraits>> negIneq;
    Stack<FoundVarInLiteral<NumTraits>> eq;
    Stack<FoundVarInLiteral<NumTraits>> neq;

    bool isOneSideBounded() const
    {
      return (this->posIneq.size() != 0 && this->negIneq.size() == 0 && this->eq.size() == 0 && this->neq.size() == 0)
          || (this->posIneq.size() == 0 && this->negIneq.size() != 0 && this->eq.size() == 0 && this->neq.size() == 0); }
    friend std::ostream& operator<<(std::ostream& out, FoundVariable const& self)
    { return out << "FoundVariable"; }
  };


  using AnyFoundVariable = Coproduct< FoundVariable< IntTraits> 
                                    , FoundVariable< RatTraits> 
                                    , FoundVariable<RealTraits> 
                                    >;

  Option<AnyFoundVariable> findUnshieldedVar(Clause* premise) const;


                            ClauseIterator applyRule(Clause* premise, FoundVariable<IntTraits> found) const { return ClauseIterator::getEmpty(); };
  template<class NumTraits> ClauseIterator applyRule(Clause* premise, FoundVariable<NumTraits> found) const;

  Option<ClauseIterator> apply(Clause* cl) const;

private:

  static auto isOneSideBounded(AnyFoundVariable const& v)
  { return v.apply([](auto& v) { return v.isOneSideBounded(); }); }

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  std::shared_ptr<AlascaState> _shared;
};

class VariableEliminationSGI
: public SimplifyingGeneratingInference
{
public:
  USE_ALLOCATOR(VariableEliminationSGI);

  VariableEliminationSGI(VariableEliminationSGI&&) = default;

  explicit VariableEliminationSGI(std::shared_ptr<AlascaState> state)
    : _inner(std::move(state))
  {  }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  ClauseGenerationResult generateSimplify(Clause* premise)  final override;
  
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override 
  { return lookeaheadResultDoesNotDependOnSelection(); }

private:
  VariableElimination _inner;
};

class VariableEliminationISE
: public ImmediateSimplificationEngineMany
{
public:
  USE_ALLOCATOR(VariableEliminationISE);

  VariableEliminationISE(VariableEliminationISE&&) = default;
  VariableEliminationISE(std::shared_ptr<AlascaState> shared)
    : _inner(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  Option<ClauseIterator> simplifyMany(Clause* premise) final override
  { return _inner.apply(premise); }
  
private:
  VariableElimination _inner;
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__VariableElimination__*/

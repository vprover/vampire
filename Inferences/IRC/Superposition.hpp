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
 * @file Superposition.hpp
 * Defines class Superposition
 *
 */

#ifndef __IRC_Superposition__
#define __IRC_Superposition__

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

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  Superposition(Superposition&&) = default;
  Superposition(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    , _indexLhs(nullptr)
    , _indexRhs(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

                            Option<ClauseIterator> genRhs(Clause* clause, Literal* literal, TermList s2) const;
  template<class NumTraits> Option<ClauseIterator> genRhs(Clause* clause, Literal* literal, TermList s2) const;

  template<class NumTraits> ClauseIterator genRhs(NumTraits, Clause* clause, Lib::shared_ptr<Stack<Literal*>> maxLits);
                            ClauseIterator genRhs(IntTraits, Clause* clause, Lib::shared_ptr<Stack<Literal*>> maxLits);
  template<class NumTraits> ClauseIterator genLhs(NumTraits, Clause* clause, Lib::shared_ptr<Stack<Literal*>> maxLits);
                            ClauseIterator genLhs(IntTraits, Clause* clause, Lib::shared_ptr<Stack<Literal*>> maxLits);

  template<class NumTraits> Option<ClauseIterator> genLhs(Clause* clause, Literal* literal, IrcLiteral<NumTraits> lit, Monom<NumTraits> k_s1) const;
  template<class NumTraits> Option<Clause*> applyRule(
    Clause* hyp1,            // <- `C1 \/ ±ks1+t1 ≈ 0` 
    Literal* pivot1,         // <-       `±ks1+t1 ≈ 0` 
    IrcLiteral<NumTraits> eq,// <-       `±ks1+t1 ≈ 0` 
    Monom<NumTraits> k_s1,   // <-       `±ks1` 
    Clause* hyp2,        // <- `C2 \/ u[s2]+t2 <> 0` 
    Literal* pivot2,     // <-       `u[s2]+t2 <> 0` 
    TermList s2,  // <-       `s2` 
    ResultSubstitutionSP& res_substitution,
    UnificationConstraintStackSP& res_constraints,
    int bank1
    ) const;


  shared_ptr<IrcState> _shared;
  IRCSuperpositionLhsIndex* _indexLhs;
  IRCSuperpositionRhsIndex* _indexRhs;
};

} // namespace IRC
} // namespace Inferences

#endif /*__IRC_Superposition__*/

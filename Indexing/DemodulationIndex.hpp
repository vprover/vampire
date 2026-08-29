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
 * @file DemodulationIndex.hpp
 * indices related to demodulation
 */

#ifndef __DemodulationIndex__
#define __DemodulationIndex__

#include "Kernel/TermOrderingDiagram.hpp"

#include "TermIndex.hpp"

namespace Indexing {

/** Custom leaf data for forward demodulation to store the demodulator
 * left- and right-hand side normalized and cache preorderedness. */
struct DemodulatorData
{
  DemodulatorData(TypedTermList term, TypedTermList rhs, Clause* clause, bool preordered, const Ordering& ord)
    : term(term), rhs(rhs), clause(clause), preordered(preordered), tod(ord.createTermOrderingDiagram())
  {
    // insert pointer to owner as non-null value representing success
    tod->insert({ { term, rhs, Ordering::GREATER } }, this);
#if VDEBUG
    ASS(term.containsAllVariablesOf(rhs));
    ASS(!preordered || ord.compare(term,rhs)==Ordering::GREATER);
    Renaming r;
    r.normalizeVariables(term);
    ASS_EQ(term,r.apply(term));
    ASS_EQ(rhs,r.apply(rhs));
#endif
  }

  // lhs, the identifier is required to be `term` by CodeTree
  TypedTermList term;
  TermList rhs;
  Clause* clause;
  bool preordered; // whether term > rhs
  TermOrderingDiagramUP tod; // TOD for checking term > rhs

  TypedTermList const& key() const { return term; }

  auto asTuple() const
  { return std::make_tuple(clause->number(), term, rhs); }

  IMPL_COMPARISONS_FROM_TUPLE(DemodulatorData)

  friend std::ostream& operator<<(std::ostream& out, DemodulatorData const& self)
  { return out << self.term.untyped() << " = " << self.rhs << ", " << self.clause->toString(); }
};

template<>
struct is_indexed_data_normalized<DemodulatorData>
{ static constexpr bool value = true; };

/**
 * Term index for backward demodulation
 */
template<bool higherOrder>
class DemodulationSubtermIndex
: public TermIndex<TermLiteralClause>
{
public:
  DemodulationSubtermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _skipNonequationalLiterals;
};

/**
 * Term index for forward demodulation
 */
template<bool higherOrder>
class DemodulationLHSIndex
: public GeneralizingTermIndex<higherOrder, DemodulatorData>
{
public:
  DemodulationLHSIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
  const bool _preordered;
};

} //namespace Indexing

#endif

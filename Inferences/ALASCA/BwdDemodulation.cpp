/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "BwdDemodulation.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using Demod = Inferences::ALASCA::Demodulation;

namespace Inferences {
namespace ALASCA {

BwdDemodulation::BwdDemodulation(SaturationAlgorithm& salg)
  : _shared(salg.alascaState()), _index(salg.getSimplifyingIndex<AlascaIndex<Rhs>>())
{}

////////////////////////////////////////////////////////////////////////////////////////////////////
// RULE APPLICATION
////////////////////////////////////////////////////////////////////////////////////////////////////


auto applyResultSubstitution(ResultSubstitution& subs, TermList t)
{ return subs.applyToBoundQuery(t); }

auto applyResultSubstitution(ResultSubstitution& subs, Literal* lit)
{ 
  Stack<TermList> terms(lit->arity()); 
  for (unsigned i = 0; i < lit->arity(); i++) {
    terms.push(applyResultSubstitution(subs, *lit->nthArgument(i)));
  }
  return Literal::create(lit, terms.begin());
}

/**
 * Perform backward simplification with @b premise.
 *
 * Descendant classes should pay attention to the possibility that TODO check this pay attention stuff
 * the premise could be present in the simplification indexes at
 * the time of call to this method.
 */
void BwdDemodulation::perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
{
  DEBUG_CODE(unsigned cnt = 0;)
  for (auto lhs : Lhs::iter(_shared, premise)) {
    DEBUG_CODE(cnt++;)
    Stack<BwSimplificationRecord> simpls;
    Set<Clause*> simplified;
    for (auto rhs : _index->instances(lhs.biggerSide())) {
        auto toSimpl = rhs.data->clause;
        if (simplified.contains(toSimpl)) {
          /* We skip this potential simplification, because we do not simplify the same clause in 
           * two different ways with the same equality.  */
        } else {
          auto maybeSimpl = Demod::apply(_shared, lhs, *rhs.data);
          if (maybeSimpl.isSome()) {
            simplified.insert(toSimpl);
            simpls.push(BwSimplificationRecord(toSimpl, maybeSimpl.unwrap()));
          }
        }
    }
    if (!simpls.isEmpty()) {
      simplifications = pvi(arrayIter(std::move(simpls)));
      return;
    }
  }
  ASS(cnt <= 1)
  simplifications = BwSimplificationRecordIterator::getEmpty();
}

} // namespace ALASCA
} // namespace Inferences

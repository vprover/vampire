LASCAclude "BwdDemodulationModLA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using Demod = Inferences::LASCA::DemodulationModLA;

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

namespace Indexing {

void BwdDemodulationModLAIndex::handleClause(Clause* toSimplify, bool adding)
{
  CALL("BwdDemodulationModLAIndex::handleClause");
  
  for (auto pos : Demod::simplifyablePositions(*_shared, toSimplify)) {
    if (pos.term.isTerm()) {
      auto term = pos.term.term();
      auto isRightNumberTerm = forAnyNumTraits([&](auto numTraits){
          using NumTraits = decltype(numTraits);
          return SortHelper::getResultSort(term) == NumTraits::sort()
              && !NumTraits::isNumeral(term)
              && !(NumTraits::mulF() == term->functor() && NumTraits::isNumeral(*term->nthArgument(0)) );
                      // ^^^ term = k * t
      });
      if (isRightNumberTerm) {
        if (adding) {
          DEBUG("\tinserting: ", term);
          _is->insert(DefaultTermLeafData(pos.term, pos.lit, toSimplify));
        } else {
          DEBUG("\tremoving: ", term);
          _is->remove(DefaultTermLeafData(pos.term, pos.lit, toSimplify));
        }
      }
    }
  }
}

} // namespace Indexing


namespace Inferences {
namespace LASCA {


#if VDEBUG
void BwdDemodulationModLA::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _index = (BwdDemodulationModLAIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif



void BwdDemodulationModLA::attach(SaturationAlgorithm* salg)
{
  ASS(!_index);

  this->BackwardSimplificationEngine::attach(salg);
  _index=static_cast<BwdDemodulationModLAIndex*> (
	  _salg->getIndexManager()->request(LASCA_BWD_DEMODULATION_SUBST_TREE) );
  _index->setShared(_shared);
}

void BwdDemodulationModLA::detach()
{

  CALL("Superposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(LASCA_BWD_DEMODULATION_SUBST_TREE);
  this->BackwardSimplificationEngine::detach();
}


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
void BwdDemodulationModLA::perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
{
  for (auto simpl : Demod::simplifiers(*_shared, premise)) {
    auto simpls = simpl.apply([&](auto simpl) {
      auto s = simpl.monom.factors->denormalize();
      auto inst = _index->getInstances(s, /* retrieveSubstitutions */ true);
      Stack<BwSimplificationRecord> simpls;
      Set<Clause*> simplified;
      while (inst.hasNext()) {
        auto res = inst.next();
        auto toSimpl = res.clause;
        if (simplified.contains(toSimpl)) {
          /* We skip this potential simplification, because we do not simplify the same clause in 
           * two different ways with the same equality. 
           * This could result into things like 
           *   r(f(a), f(a)) ==> { r(a, f(a)), r(f(a), a) } ==> { r(a,a), r(a,a) }
           * instead of
           *   r(f(a), f(a)) ==> r(a, f(a)) ==> r(a,a)
           * (for premise 0 = f(a) - a)
           */
        } else {
          auto sigma = [&](auto t) 
            { return res.substitution ? applyResultSubstitution(*res.substitution, t) : t; };
          auto maybeSimpl = Demod::apply(*_shared, toSimpl, premise, simpl.lit, simpl.monom.factors->denormalize(), simpl.monom.factors, sigma);
          if (maybeSimpl.isSome()) {
            simplified.insert(toSimpl);
            simpls.push(BwSimplificationRecord(toSimpl, maybeSimpl.unwrap()));
          }
        }
      }
      return simpls;
    });
    if (!simpls.isEmpty()) {
      simplifications = pvi(ownedArrayishIterator(std::move(simpls)));
      return;
    }
  }
  simplifications = BwSimplificationRecordIterator::getEmpty();
}

} // namespace LASCA
} // namespace Inferences

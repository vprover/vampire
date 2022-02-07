#include "Inferences/IRC/FwdDemodulationModLA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using Demod = Inferences::IRC::DemodulationModLA;

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

namespace Indexing {

void FwdDemodulationModLAIndex::handleClause(Clause* cl, bool add)
{
  CALL("FwdDemodulationModLAIndex::handleClause");
  DEBUG("handling: ", *cl);
  for (auto simplifier : Demod::simplifiers(*_shared, cl)) {
    simplifier.apply([&](auto simplifier){
       auto term = simplifier.monom.factors->denormalize();
       auto lit = (*cl)[0];
      if (add) {
        DEBUG("\tinserting: ", term);
        _is->insert(term, lit, cl);
      } else {
        DEBUG("\tremoving: ", term);
        _is->remove(term, lit, cl);
      }
    });
  }
}

} // namespace Indexing


namespace Inferences {
namespace IRC {

#if VDEBUG
void FwdDemodulationModLA::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _index = (FwdDemodulationModLAIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif

void FwdDemodulationModLA::attach(SaturationAlgorithm* salg)
{  
  ASS(!_index);

  this->ForwardSimplificationEngine::attach(salg);
  _index=static_cast<FwdDemodulationModLAIndex*> (
	  _salg->getIndexManager()->request(IRC_FWD_DEMODULATION_SUBST_TREE) );
  _index->setShared(_shared);
}

void FwdDemodulationModLA::detach()
{

  CALL("Superposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_FWD_DEMODULATION_SUBST_TREE);
  this->ForwardSimplificationEngine::detach();
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// RULE APPLICATION
////////////////////////////////////////////////////////////////////////////////////////////////////

/**
 * Perform forward simplification on @b cl
 *
 * Return true if the simplification is applicable on @b cl,
 * set @b replacement to a replacing clause if there is one (otherwise keep @b replacement = nullptr)
 *
 * @b premises will contain clauses that justify the simplification
 * performed.
 */
bool FwdDemodulationModLA::perform(Clause* toSimplify, Clause*& replacement, ClauseIterator& premises)
{
  ASS_EQ(replacement, NULL)
  Stack<Literal*> simplified;
  for (auto pos : Demod::simplifyablePositions(*_shared, toSimplify)) {
    DEBUG("simplifyable position: ", pos.term, " in ", *pos.lit)
    auto gen = _index->getGeneralizations(pos.term, /* retrieveSubstitutions */ true);
    while (gen.hasNext()) {
      auto res = gen.next();
      auto applied = _shared->renormalize(res.literal).unwrap()
        .apply([&](auto lit) {
            using NumTraits = typename decltype(lit)::NumTraits;
            auto s = res.term;
            auto s_norm  = _shared
              ->normalize(TypedTermList(s, NumTraits::sort()))
              .template wrapPoly<NumTraits>()
              ->tryMonom().unwrap().factors; 


            auto sigma = [&](auto t) 
              { return res.substitution ? res.substitution->applyToBoundResult(t)
                                        : t; };

            auto simplified = Demod::apply(*_shared, toSimplify, res.clause, lit, s, s_norm, sigma);
            if (simplified.isSome()) {
              replacement = simplified.unwrap();
              premises    = pvi(getSingletonIterator(res.clause));
              return true;
            } else {
              return false;
            }
        });
      if (applied) {
        return true;
      }
    }
  }
  premises = ClauseIterator::getEmpty();
  return false;
}

} // namespace IRC
} // namespace Inferences

#include "Inferences/IRC/FwdDemodulationModLA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

namespace Indexing {

void FwdDemodulationModLAIndex::handleClause(Clause* c, bool adding)
{
  CALL("FwdDemodulationModLAIndex::handleClause");
  
  UNIMPLEMENTED
  // auto maxLits =  _shared->maxLiterals(c); // TODO use set instead of stack
  // forEachNumTraits([&](auto numTraits){
  //     using NumTraits = decltype(numTraits);
  //     for (auto& maxTerm : _shared->maxAtomicTermsNonVar<NumTraits>(c)) {
  //
  //       
  //       if (!maxTerm.self.tryNumeral().isSome() // <- skipping numerals
  //           && maxTerm.ircLit.isInequality() // <- skipping equalities
  //           && iterTraits(maxLits.iterFifo()).any([&](auto x){ return maxTerm.literal == x; })
  //           ) {
  //         auto term = maxTerm.self.factors->denormalize();
  //         auto lit = maxTerm.literal;
  //         if (adding) {
  //           DEBUG("\tinserting: ", term);
  //           _is->insert(term, lit, c);
  //         } else {
  //           DEBUG("\tremoving: ", term);
  //           _is->remove(term, lit, c);
  //         }
  //       }
  //     }
  // });
}

} // namespace Indexing


namespace Inferences {
namespace IRC {

void FwdDemodulationModLA::attach(SaturationAlgorithm* salg)
{  
  ASS(!_index);

  this->GeneratingInferenceEngine::attach(salg);
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
  this->GeneratingInferenceEngine::detach();
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
bool FwdDemodulationModLA::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  UNIMPLEMENTED
}

} // namespace IRC
} // namespace Inferences

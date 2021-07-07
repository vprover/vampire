#include "BwdDemodulationModLA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

namespace Indexing {

void BwdDemodulationModLAIndex::handleClause(Clause* c, bool adding)
{
  CALL("BwdDemodulationModLAIndex::handleClause");
  
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

void BwdDemodulationModLA::attach(SaturationAlgorithm* salg)
{
  ASS(!_index);

  this->GeneratingInferenceEngine::attach(salg);
  _index=static_cast<BwdDemodulationModLAIndex*> (
	  _salg->getIndexManager()->request(IRC_BWD_DEMODULATION_SUBST_TREE) );
  _index->setShared(_shared);
}

void BwdDemodulationModLA::detach()
{

  CALL("Superposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_BWD_DEMODULATION_SUBST_TREE);
  this->GeneratingInferenceEngine::detach();
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// RULE APPLICATION
////////////////////////////////////////////////////////////////////////////////////////////////////


/**
 * Perform backward simplification with @b premise.
 *
 * Descendant classes should pay attention to the possibility that
 * the premise could be present in the simplification indexes at
 * the time of call to this method.
 */
void BwdDemodulationModLA::perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
{
  UNIMPLEMENTED
}

} // namespace IRC
} // namespace Inferences

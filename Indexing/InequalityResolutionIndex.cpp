#include "InequalityResolutionIndex.hpp"
#include "Kernel/InequalityNormalizer.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class NumTraits>
bool InequalityResolutionIndex::handleLiteral(Literal* lit, Clause* c, bool adding)
{
  /* normlizing to t >= 0 */
  auto norm_ = this->normalizer().normalize<NumTraits>(lit);
  if (norm_.isSome()) {
    if (norm_.unwrap().overflowOccurred) {
      DEBUG("skipping overflown literal: ", norm_.unwrap().value)
      env.statistics->irOverflowNorm++;
      /* we skip it */

    } else {
      auto norm = std::move(norm_).unwrap().value;

      DEBUG("literal: ", norm);
      for (auto monom : norm.term().iterSummands()) {
        // if (!monom.tryNumeral().isSome()) { // TODO shall we skip this?
        if (!monom.factors->tryVar().isSome()) { // TODO shall we not skip this?

          auto term = monom.factors->denormalize();
          if (adding) {
            DEBUG("\tinserting: ", term);
            _is->insert(term, lit, c);
          } else {
            DEBUG("\tremoving: ", term);
            _is->remove(term, lit, c);
          }
        }
      }
    }
    return true;
  } else {
    return false;
  }
}

void InequalityResolutionIndex::handleClause(Clause* c, bool adding)
{
  CALL("InequalityResolutionIndex::handleClause");

  for (unsigned i = 0; i < c->size(); i++) {
    auto lit = (*c)[i];
    handleLiteral< IntTraits>(lit, c, adding) 
    || handleLiteral< RatTraits>(lit, c, adding)
    || handleLiteral<RealTraits>(lit, c, adding);
  }
}

}



#include "InequalityResolutionIndex.hpp"
#include "Kernel/IRC.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)

namespace Indexing {

// template<class NumTraits>
// bool InequalityResolutionIndex::handleLiteral(Literal* lit, Clause* c, bool adding)
// {
//   /* normlizing to t >= 0 */
//   auto norm_ = _shared->normalizer.normalizeIneq<NumTraits>(lit);
//   if (norm_.isSome()) {
//     if (norm_.unwrap().overflowOccurred) {
//       DEBUG("skipping overflown literal: ", norm_.unwrap().value)
//       /* we skip it */
//
//     } else {
//       auto norm = std::move(norm_).unwrap().value;
//
//       DEBUG("literal: ", norm);
//       for (auto monom : _shared->maxAtomicTerms(norm.inner())) {
//         ASS(monom.factors->tryVar().isNone())
//
//         // skipping numerals
//         if (!monom.tryNumeral().isSome()) { 
//
//           auto term = monom.factors->denormalize();
//           if (adding) {
//             DEBUG("\tinserting: ", term);
//             _is->insert(term, lit, c);
//           } else {
//             DEBUG("\tremoving: ", term);
//             _is->remove(term, lit, c);
//           }
//         }
//       }
//     }
//     return true;
//   } else {
//     return false;
//   }
// }

void InequalityResolutionIndex::handleClause(Clause* c, bool adding)
{
  CALL("InequalityResolutionIndex::handleClause");
  
  auto maxLits =  _shared->maxLiterals(c); // TODO use set instead of stack
  forEachNumTraits([&](auto numTraits){
      using NumTraits = decltype(numTraits);
      for (auto& maxTerm : _shared->maxAtomicTermsNonVar<NumTraits>(c)) {

        
        if (!maxTerm.self.tryNumeral().isSome() // <- skipping numerals
            && maxTerm.ircLit.isInequality() // <- skipping equalities
            && iterTraits(maxLits.iterFifo()).any([&](auto x){ return maxTerm.literal == x; })
            ) {
          auto term = maxTerm.self.factors->denormalize();
          auto lit = maxTerm.literal;
          if (adding) {
            DEBUG("\tinserting: ", term);
            _is->insert(term, lit, c);
          } else {
            DEBUG("\tremoving: ", term);
            _is->remove(term, lit, c);
          }
        }
      }
  });
  // for (auto lit : iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(c)))) {
  //   handleLiteral< IntTraits>(lit, c, adding) 
  //   || handleLiteral< RatTraits>(lit, c, adding)
  //   || handleLiteral<RealTraits>(lit, c, adding);
  // }
}


bool IRCSuperpositionIndex::handleUninterpreted(Literal* lit, Clause* c, bool adding)
{
  SubtermIterator iter(lit);
  while (iter.hasNext()) {
    handle(iter.next(), lit, c, adding);
  }
  return true;
}

void IRCSuperpositionIndex::handle(TermList term, Literal* lit, Clause* c, bool adding)
{
  if (!term.isVar()) { // TODO don't add k * term (?)
    if (adding) {
      DEBUG("\tinserting: ", term);
      _is->insert(term, lit, c);
    } else {
      DEBUG("\tremoving: ", term);
      _is->remove(term, lit, c);
    }
  }
}

template<class NumTraits>
bool IRCSuperpositionIndex::handleInequality(Literal* lit, Clause* c, bool adding)
{
  /* normlizing to t >= 0 */
  auto norm_ = _shared->normalizer.normalizeIneq<NumTraits>(lit);
  if (norm_.isSome()) {
    if (norm_.unwrap().overflowOccurred) {
      DEBUG("skipping overflown literal: ", norm_.unwrap().value)
      /* we skip it */

    } else {
      auto norm = std::move(norm_).unwrap().value;

      DEBUG("literal: ", norm);
      for (auto monom : _shared->maxAtomicTerms(norm.inner())) {
        ASS(monom.factors->tryVar().isNone())

        // skipping numerals
        if (!monom.tryNumeral().isSome()) {
          auto term = monom.factors->denormalize();
          handle(term, lit, c, adding);
          if (term.isTerm()) {
            SubtermIterator iter(term.term());
            while (iter.hasNext()) {
              handle(iter.next(), lit, c, adding);
            }
          }
        }
      }
    }
    return true;
  } else {
    return false;
  }
}

void IRCSuperpositionIndex::handleClause(Clause* c, bool adding)
{
  CALL("IRCSuperpositionIndex::handleClause");
  for (auto lit : iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(c)))) {
    handleInequality< IntTraits>(lit, c, adding) 
    || handleInequality< RatTraits>(lit, c, adding)
    || handleInequality<RealTraits>(lit, c, adding)
    || handleUninterpreted(lit, c, adding);
  }
}

} // namespatrue Indexing

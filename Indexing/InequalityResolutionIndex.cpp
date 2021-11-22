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
}


bool IRCSuperpositionRhsIndex::handleUninterpreted(Literal* lit, Clause* c, bool adding)
{
  SubtermIterator iter(lit);
  while (iter.hasNext()) {
    auto t = iter.next();
    if (!t.isVar())
      handle(t, lit, c, adding);
  }
  return true;
}

void IRCSuperpositionRhsIndex::handle(TermList term, Literal* lit, Clause* c, bool adding)
{
  ASS(!term.isVar())
  // TODO don't add k * term (?)
  if (adding) {
    DEBUG("\tinserting: ", term);
    _is->insert(term, lit, c);
  } else {
    DEBUG("\tremoving: ", term);
    _is->remove(term, lit, c);
  }
}

template<class NumTraits>
bool IRCSuperpositionRhsIndex::handleInequality(Literal* lit, Clause* c, bool adding)
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
          // if (!term.isVar())
          handle(term, lit, c, adding);
          if (term.isTerm()) {
            SubtermIterator iter(term.term());
            while (iter.hasNext()) {
              auto t = iter.next();
              if (!t.isVar())
                handle(t, lit, c, adding);
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

void IRCSuperpositionRhsIndex::handleClause(Clause* c, bool adding)
{
  CALL("IRCSuperpositionRhsIndex::handleClause");
  for (auto lit : iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(c)))) {
    handleInequality< IntTraits>(lit, c, adding) 
    || handleInequality< RatTraits>(lit, c, adding)
    || handleInequality<RealTraits>(lit, c, adding)
    || handleUninterpreted(lit, c, adding);
  }
}

//////////////////////////////////////////////////////////////////////////////////////////////////

void IRCSuperpositionLhsIndex::handle(TermList term, Literal* lit, Clause* c, bool adding)
{
  ASS(!term.isVar())
  // TODO don't add k * term (?)
  if (adding) {
    DEBUG("\tinserting: ", term);
    _is->insert(term, lit, c);
  } else {
    DEBUG("\tremoving: ", term);
    _is->remove(term, lit, c);
  }
}

template<class NumTraits>
bool IRCSuperpositionLhsIndex::handleInequality(Literal* lit, Clause* c, bool adding)
{
  CALL("IRCSuperpositionLhsIndex::handleInequality");
  /* normlizing to t >= 0 */
  // auto norm_ = _shared->normalizer.normalizeIneq<NumTraits>(lit);
  auto norm_ = _shared->normalizer.normalizeIrc<NumTraits>(lit);
  if (norm_.isSome()) {
    if (norm_.unwrap().overflowOccurred) {
      DEBUG("skipping overflown literal: ", norm_.unwrap().value)
      /* we skip it */

    } else {
      auto norm = std::move(norm_).unwrap().value;
      if (norm.symbol() != IrcPredicate::EQ)
        return true;

      DEBUG("literal: ", norm);
      for (auto monom : _shared->maxAtomicTerms(norm)) {
        ASS(monom.factors->tryVar().isNone())

        // skipping numerals
        if (!monom.tryNumeral().isSome()) {
          auto term = monom.factors->denormalize();
          handle(term, lit, c, adding);
        }
      }
    }
    return true;
  } else {
    return false;
  }
}

void IRCSuperpositionLhsIndex::handleClause(Clause* c, bool adding)
{
  CALL("IRCSuperpositionLhsIndex::handleClause");
  for (auto lit : iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(c)))) {
    handleInequality< IntTraits>(lit, c, adding) 
    || handleInequality< RatTraits>(lit, c, adding)
    || handleInequality<RealTraits>(lit, c, adding);
  }
}


} // namespatrue Indexing

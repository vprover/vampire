#include "InequalityResolutionIndex.hpp"
#include "Kernel/IRC.hpp"
#include "Shell/Statistics.hpp"
#include "Inferences/IRC/Superposition.hpp"

#define DEBUG(...)  //DBG(__VA_ARGS__)

namespace Indexing {

void InequalityResolutionIndex::handleClause(Clause* c, bool adding)
{
  CALL("InequalityResolutionIndex::handleClause");
  
  auto maxLits =  make_shared(new Stack<Literal*>(_shared->selectedLiterals(c))); // TODO use set instead of stack
  forEachNumTraits([&](auto numTraits){
      using NumTraits = decltype(numTraits);
      for (auto& maxTerm : _shared->selectedTerms<NumTraits>(c)) {
        
        if (!maxTerm.self.tryNumeral().isSome() // <- skipping numerals
            && maxTerm.ircLit.isInequality() // <- skipping equalities
            && iterTraits(maxLits->iterFifo()).any([&](auto x){ return maxTerm.literal == x; })
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

void IRCSuperpositionRhsIndex::handleClause(Clause* c, bool adding)
{
  CALL("IRCSuperpositionRhsIndex::handleClause");
  auto maxLits =  make_shared(new Stack<Literal*>(_shared->selectedLiterals(c))); // TODO use set instead of stack
  forEachNumTraits([&](auto numTraits) {
      for (auto hyp2 : Inferences::IRC::Superposition::iterHyp2Apps(_shared, numTraits, c, maxLits)) {
        handle(hyp2.key(), hyp2.pivot, hyp2.cl, adding);
      }
  });
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

void IRCSuperpositionLhsIndex::handleClause(Clause* c, bool adding)
{

  CALL("IRCSuperpositionLhsIndex::handleClause");
  auto maxLits =  make_shared(new Stack<Literal*>(_shared->selectedLiterals(c))); // TODO use set instead of stack
  forEachNumTraits([&](auto numTraits) {
      for (auto hyp1 : Inferences::IRC::Superposition::iterHyp1Apps(_shared, numTraits, c, maxLits)) {
        handle(hyp1.key(), hyp1.pivot, hyp1.cl, adding);
      }
  });
}


} // namespatrue Indexing

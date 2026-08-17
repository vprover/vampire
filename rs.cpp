#include <iostream>
#include <unordered_set>

#include "Kernel/Inference.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

using namespace Inferences;
using namespace Indexing;
using namespace Kernel;

static UnitList *ACTIVE_LIST = nullptr;
static SATSubsumption::SATSubsumptionAndResolution SUBSUMPTION_ENGINE;
static DuplicateLiteralRemovalISE REMOVE_DUPLICATE_LITERALS;
// TODO heap-allocated because their destructor running messes up Vampire's termination
static LiteralSubstitutionTree<LiteralClause> *ACTIVE_INDEX = new LiteralSubstitutionTree<LiteralClause>();
static LiteralSubstitutionTree<LiteralClause> *PASSIVE_INDEX = new LiteralSubstitutionTree<LiteralClause>();

static void addToActive(Clause *cl) {
  UnitList::push(cl, ACTIVE_LIST);
  for (Literal *l : cl->iterLits())
    ACTIVE_INDEX->insert({l, cl});
}

static void addToPassive(Clause *cl) {
  for (Literal *l : cl->iterLits())
    PASSIVE_INDEX->insert({l, cl});
}

static void removeFromPassive(Clause *cl) {
  for (Literal *l : cl->iterLits())
    PASSIVE_INDEX->remove({l, cl});
}

static bool subsume(Clause *cl) {
  for(Literal *l : cl->iterLits())
    for(auto result : iterTraits(ACTIVE_INDEX->getGeneralizations(l, false, false)))
      if(SUBSUMPTION_ENGINE.checkSubsumption(result.data->clause, cl, false))
        return true;
  return false;
}

static bool subsume(Clause *cl, Clause *&additional) {
  if(subsume(cl))
      return true;

  for(Literal *l : cl->iterLits())
    for(auto result : iterTraits(PASSIVE_INDEX->getGeneralizations(l, false, false)))
      if(SUBSUMPTION_ENGINE.checkSubsumption(result.data->clause, cl, false)) {
        additional = result.data->clause;
        return true;
      }
  return false;
}

static bool blockedOn(const std::vector<Literal *> &candidate, Literal *on) {
restart:
  Clause *additional = nullptr;
  for(auto result : iterTraits(ACTIVE_INDEX->getUnifications(on, true, true))) {
    std::unordered_set<Literal *> resolvent_lits;
    for(Literal *l : candidate)
      if(l != on)
        resolvent_lits.insert(result.unifier->applyToQuery(l));
    for(Literal *l : result.data->clause->iterLits())
      if(l != result.data->literal)
        resolvent_lits.insert(result.unifier->applyToResult(l));

    Clause *resolvent = Clause::fromIterator(
      getSTLIterator(resolvent_lits.begin(), resolvent_lits.end()),
      FromInput(UnitInputType::AXIOM)
    );
    // TODO check tautology

    bool subsumed = subsume(resolvent, additional);
    resolvent->destroy();
    if(!subsumed)
      return false;

    if(additional)
      break;
  }

  if(additional) {
    // TODO some more complex logic here, work out which combination of promotions is best?
    std::cout << "[RS] promote: " << additional->toString() << '\n';
    // we (potentially) used `additional` to simplify a clause, so now it moves to active
    removeFromPassive(additional);
    addToActive(additional);

    // now we might have missed a resolvent on `additional`, so restart
    goto restart;
  }

  return true;
}

static bool blocked(const std::vector<Literal *> &candidate) {
  for(Literal *l : candidate)
    if(blockedOn(candidate, l))
      return true;
  return false;
}

static Clause *create(std::vector<Literal *> candidate) {
  SimplifyingInferenceMany inference(InferenceRule::RESOLUTION_SUBSUMPTION, ACTIVE_LIST);
  Clause *result = Clause::fromIterator(
    getSTLIterator(candidate.begin(), candidate.end()),
    inference
  );
  result->incRefCnt();
  return result;
}

static Clause *tryCandidate(std::vector<Literal *> candidate) {
  if(blocked(candidate)) {
    Clause *replacement = create(std::move(candidate));
    // success!
    std::cout << "[RS] replaced: " << replacement->toString() << '\n';
    // ...but now we need to record it in the active set
    addToActive(replacement);
    return replacement;
  }
  return nullptr;
}

void rsInputClause(Clause *input) {
  input = REMOVE_DUPLICATE_LITERALS.simplify(input);
  std::cout << "[RS] input: " << *input << '\n';
  addToActive(input);
}

Clause *rsDerivedClause(Clause *derived) {
  // should already be simplified, no need to remove duplicate literals
  std::cout << "[RS] derived: " << derived->toString() << '\n';

  // TODO something more sensible with this case?
  if(subsume(derived))
    return nullptr;

  std::vector<Literal *> original;
  for(Literal *l : derived->iterLits())
    original.push_back(l);

  // try dropping literals
  for(Literal *l : original) {
    std::vector<Literal *> candidate;
    for(Literal *k : original)
      if(l != k)
        candidate.push_back(k);

    if(Clause *replacement = tryCandidate(std::move(candidate)))
      // TODO could consider iterating for more power?
      return replacement;
  }

  // TODO try dropping subterms

  // failed to simplify, but can at least use it for possible subsumptions
  addToPassive(derived);
  return nullptr;
}

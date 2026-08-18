#include <iostream>
#include <optional>
#include <unordered_set>

#include "Kernel/EqHelper.hpp"
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

Clause *createResolvent(
  std::vector<Literal *> candidate,
  QueryRes<ResultSubstitutionSP, LiteralClause> result,
  Literal *on
) {
  std::unordered_set<Literal *> resolvent_lits;
  for(Literal *l : candidate)
    if(l != on)
      resolvent_lits.insert(result.unifier->applyToQuery(l));
  for(Literal *l : result.data->clause->iterLits())
    if(l != result.data->literal)
      resolvent_lits.insert(result.unifier->applyToResult(l));

  // tautology check
  for(Literal *l : resolvent_lits)
    if(resolvent_lits.contains(Literal::complementaryLiteral(l)))
      return nullptr;

  return Clause::fromIterator(
    getSTLIterator(resolvent_lits.begin(), resolvent_lits.end()),
    FromInput(UnitInputType::AXIOM)
  );
}

static bool blockedOn(
  const std::vector<Literal *> &candidate,
  Literal *on,
  LiteralSubstitutionTree<LiteralClause> &index,
  std::vector<Clause *> &promoteThese
) {
  for(auto result : iterTraits(index.getUnifications(on, true, true))) {
    Clause *resolvent = createResolvent(candidate, result, on);
    if(!resolvent)
      continue;

    Clause *additional = nullptr;
    bool subsumed = subsume(resolvent, additional);
    resolvent->destroy();
    if(!subsumed)
      return false;

    if(additional)
      promoteThese.push_back(additional);
  }
  return true;
}

static bool blockedOn(const std::vector<Literal *> &candidate, Literal *on, DHSet<Clause *> &promoted) {
  std::vector<Clause *> promoteThese;
  if(!blockedOn(candidate, on, *ACTIVE_INDEX, promoteThese))
    return false;

  // `blockedOn` is allowed to promote some clauses `S` to subsume resolvents
  // but then we must consider the resolvents of `candidate` against `S` until fixed point
  while(!promoteThese.empty()) {
    auto promotedIndex = std::make_unique<LiteralSubstitutionTree<LiteralClause>>();
    for(Clause *cl : promoteThese) {
      if(!promoted.insert(cl))
        continue;
      for(Literal *l : cl->iterLits())
        promotedIndex->insert({l, cl});
    }
    promoteThese.clear();
    if(!blockedOn(candidate, on, *promotedIndex, promoteThese))
      return false;
  }

  return true;
}

static bool blocked(const std::vector<Literal *> &candidate, bool doPromotions = true) {
  std::vector<std::optional<DHSet<Clause *>>> promotions;
  for(Literal *l : candidate) {
    DHSet<Clause *> promoted;
    if(blockedOn(candidate, l, promoted))
      // optimisation: empty promotions are immediately best
      if(promoted.isEmpty())
        return true;
      else
        promotions.emplace_back(std::move(promoted));
    else
      promotions.emplace_back();
  }
  ASS_EQ(promotions.size(), candidate.size())

  // now select the smallest set of promotions possible
  std::optional<DHSet<Clause *>> best;
  for(auto &promote : promotions) {
    if(!promote)
      continue;
    ASS(promote->size())
    if(!best || best->size() > promote->size())
      best = std::move(promote);
  }

  if(best && doPromotions)
    for(Clause *cl : iterTraits(best->iterator())) {
      std::cout << "[RS] promote: " << cl->toString() << '\n';
      // we used `cl` to subsume a resolvent, so now it moves to the active set
      removeFromPassive(cl);
      addToActive(cl);
    }

  return bool(best);
}

static Clause *createReplacement(const std::vector<Literal *> &candidate) {
  SimplifyingInferenceMany inference(InferenceRule::RESOLUTION_SUBSUMPTION, ACTIVE_LIST);
  Clause *result = Clause::fromIterator(
    getSTLIterator(candidate.begin(), candidate.end()),
    inference
  );
  result->incRefCnt();
  // success!
  std::cout << "[RS] replaced: " << result->toString() << '\n';
  // ...but now we need to record it in the active set
  addToActive(result);
  return result;
}

void rsInputClause(Clause *input) {
  input = REMOVE_DUPLICATE_LITERALS.simplify(input);
  std::cout << "[RS] input: " << *input << '\n';
  addToActive(input);
}

// TODO something about when a clause is removed? AVATAR?
Clause *rsDerivedClause(Clause *cl) {
  // at this point cl should already be simplified, no need to remove duplicate literals

  // TODO this case is weird
  if(subsume(cl))
    return nullptr;

  // the candidate replacement
  std::vector<Literal *> candidate;
  for(Literal *l : cl->iterLits())
    candidate.push_back(l);

  // if original clause is not blocked, no stronger clause can be blocked
  if(!blocked(candidate, false)) {
    addToPassive(cl);
    return nullptr;
  }

  std::cout << "[RS] attempt: " << cl->toString() << '\n';

  bool success = false;

  // try dropping literals
  // TODO could this be done by inspecting the subsumption?
  unsigned dropIndex = 0;
  while(dropIndex < candidate.size()) {
    Literal *removed = candidate[dropIndex];
    candidate[dropIndex] = candidate.back();
    candidate.pop_back();

    if(blocked(candidate)) {
      std::cout << "[RS] dropped literal\n";
      success = true;
    }
    else {
      candidate.push_back(candidate[dropIndex]);
      candidate[dropIndex++] = removed;
    }
  }

  // try mapping subterms to a new variable
  unsigned fresh = cl->isGround() ? 0 : cl->maxVar() + 1;
  for(Literal *&change : candidate)
restart_subterms:
    for(Term *subterm : iterTraits(NonVariableNonTypeIterator(change))) {
      Literal *before = change;
      change = EqHelper::replace(change, TermList(subterm), TermList::var(fresh));
      if(blocked(candidate)) {
        std::cout << "[RS] replaced subterm\n";
        success = true;
        fresh++;
        goto restart_subterms;
      }
      change = before;
    }

  if(success)
    return createReplacement(candidate);

  // failed to simplify, but can at least use it for possible subsumptions
  addToPassive(cl);
  return nullptr;
}

#include "FO2Solver.hpp"
#include "F02Fragment/FO2Logger.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Stack.hpp"
#include <deque>
#include <cstdlib>
#include <unordered_set>
#include <stdexcept>
#include <vector>
#include <iostream>
#include <map>
#include <string>
#include <algorithm>
#include <cstdint>
#include <set>
#include <queue>
#include <tuple>
#include <unordered_map>
#include <chrono>
#include <memory>
#include <iomanip>

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

using namespace Kernel;
using namespace Lib;

namespace FO2Fragment {

namespace {
// Opt-in diagnostics. Times are exclusive wall times: nested operations
// suspend their parent timer. Snapshots survive hard timeouts; final reports
// are emitted only on normal stack unwinding, never from a signal handler.
struct PhaseProfile {
  using Clock = std::chrono::steady_clock;
  bool enabled = std::getenv("FO2_PHASE_PROFILE") != nullptr;
  std::map<std::string, double> seconds;
  std::map<std::string, size_t> counters;
  std::string phase = "search_other";
  Clock::time_point started = Clock::now(), last = started, lastReport = started;
  void charge() {
    if (!enabled) return;
    auto now = Clock::now();
    seconds[phase] += std::chrono::duration<double>(now - last).count();
    last = now;
  }
  void count(const char* name, size_t amount = 1) {
    if (enabled) counters[name] += amount;
  }
  void peak(const char* name, size_t value) {
    if (enabled) counters[name] = std::max(counters[name], value);
  }
  void report(bool final = false) {
    if (!enabled) return;
    charge();
    std::cerr << "FO2_PHASE scope=whole_search final=" << final
              << " elapsed_seconds=" << std::chrono::duration<double>(last-started).count();
    for (const auto& item : seconds) std::cerr << " " << item.first << "_seconds=" << item.second;
    for (const auto& item : counters) std::cerr << " " << item.first << "=" << item.second;
    std::cerr << std::endl;
    lastReport = Clock::now();
    last = lastReport; // Do not charge diagnostic output to an algorithmic phase.
  }
  void tick() {
    if (enabled && Clock::now() - lastReport >= std::chrono::milliseconds(250)) report();
  }
  struct Scope {
    PhaseProfile& owner;
    std::string previous;
    Scope(PhaseProfile& p, const char* name) : owner(p) {
      if (!owner.enabled) return;
      owner.charge(); previous = owner.phase; owner.phase = name;
    }
    ~Scope() {
      if (!owner.enabled) return;
      owner.charge(); owner.phase = previous; owner.tick();
    }
  };
  template<class F> auto measure(const char* name, F&& function) -> decltype(function()) {
    Scope scope(*this, name);
    return function();
  }
  ~PhaseProfile() { report(true); }
};
Problem makeSplitBranch(Problem& source, Clause* splitClause, const std::vector<Literal*>& part)
{
  Stack<Literal*> literals;
  for (Literal* literal : part) literals.push(literal);
  Clause* branchClause = Clause::fromStack(literals, splitClause->inference());

  UnitList* units = UnitList::empty();
  UnitList::Iterator it(source.units());
  while (it.hasNext()) {
    Unit* unit = it.next();
    if (unit != splitClause) UnitList::push(unit, units);
  }
  UnitList::push(branchClause, units);
  return Problem(UnitList::reverse(units));
}

/** Propagate units before splitting and before assigning proof indices.
 * Match only the unit's variables: the remaining clause must keep its full
 * universal scope. S2 validation and indexing follow this preprocessing.
 */
bool propagateUnits(Problem& problem)
{
  std::vector<Unit*> units;
  UnitList::Iterator it(problem.units());
  while (it.hasNext()) units.push_back(it.next());
  std::map<Literal*, Clause*> facts;
  std::map<std::pair<unsigned, bool>, std::vector<Clause*>> variableFacts;
  auto matchingUnit = [&](Literal* literal) -> Clause* {
    auto ground = facts.find(literal);
    if (ground != facts.end()) return ground->second;
    auto candidates = variableFacts.find({literal->functor(), literal->polarity()});
    if (candidates == variableFacts.end()) return nullptr;
    Literal* target = Literal::create(literal, true);
    for (Clause* candidate : candidates->second) {
      RobSubstitution matching;
      if (matching.match(TermList(Literal::create((*candidate)[0], true)), 0,
                         TermList(target), 1)) return candidate;
    }
    return nullptr;
  };
  bool modified = false;
  bool changed;
  do {
    changed = false;
    variableFacts.clear();
    for (Unit* unit : units) {
      if (!unit->isClause()) continue;
      Clause* clause = static_cast<Clause*>(unit);
      if (clause->length() == 0) return false;
      if (clause->length() != 1) continue;
      Literal* literal = (*clause)[0];
      VariableIterator variables(literal);
      if (variables.hasNext()) {
        variableFacts[{literal->functor(), literal->polarity()}].push_back(clause);
        continue;
      }
      if (facts.count(Literal::complementaryLiteral(literal))) return false;
      facts.emplace(literal, clause);
    }

    std::vector<Unit*> simplified;
    for (Unit* unit : units) {
      if (!unit->isClause()) {
        simplified.push_back(unit);
        continue;
      }
      Clause* clause = static_cast<Clause*>(unit);
      // Keep the facts themselves as constraints in the simplified problem.
      if (clause->length() == 1) {
        if (matchingUnit(Literal::complementaryLiteral((*clause)[0]))) return false;
        simplified.push_back(clause);
        continue;
      }
      bool satisfied = false;
      for (unsigned i = 0; i < clause->length(); ++i) {
        if (matchingUnit((*clause)[i])) { satisfied = true; break; }
      }
      if (satisfied) { modified = true; continue; }

      unsigned i = 0;
      while (i < clause->length()) {
        Clause* fact = matchingUnit(Literal::complementaryLiteral((*clause)[i]));
        if (!fact) { ++i; continue; }
        Stack<Literal*> remaining;
        for (unsigned j = 0; j < clause->length(); ++j) {
          if (i != j) remaining.push((*clause)[j]);
        }
        clause = Clause::fromStack(remaining,
            SimplifyingInference2(InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION,
                                 clause, fact));
        if (clause->length() == 0) return false;
        modified = changed = true;
      }
      simplified.push_back(clause);
    }
    units = std::move(simplified);
  } while (changed);

  if (modified) {
    UnitList* result = UnitList::empty();
    for (Unit* unit : units) UnitList::push(unit, result);
    problem.units() = UnitList::reverse(result);
    problem.invalidateProperty();
  }
  return true;
}

/**
 * Monitors the invariance of the class S2 (Lemma 10): every clause that enters the
 * saturation (initial clauses and clauses produced by resolution, factoring and splitting)
 * is checked against Definition 6. Prints a summary when the solver terminates.
 */
struct S2Monitor {
  // Disabled for timing runs: skip invariant checks, statistics and reports.
  static constexpr bool enabled = false;
  struct Stats {
    size_t checked = 0;
    size_t violations = 0;
    std::map<std::string, size_t> byOrigin;
    std::map<std::string, size_t> byReason;
    bool firstReported = false;
  };
  Stats generated; // raw output of the inferences (before splitting)
  Stats active;    // clauses entering the active set (after splitting)
  Stats indexGen;  // index condition of Lemma 10 on generated clauses
  Stats indexAct;  // index condition of Lemma 10 on active clauses
  Stats selection; // Lemma 9: selected literals contain all variables (active clauses)

  static void recordWith(bool ok, const std::string& reason, Stats& st, const char* stage, const IndexedClause& icl, const std::string& origin)
  {
    ++st.checked;
    if (ok) return;
    ++st.violations;
    ++st.byOrigin[origin];
    ++st.byReason[reason];
    if (!st.firstReported) {
      st.firstReported = true;
      FO2Logger::logPhase(std::string("[S2 INVARIANT] FIRST VIOLATION (") + stage + ", origin: " + origin + ", " + reason + "): " + icl.toStringWithSelection());
    }
  }

  static void record(Stats& st, const char* stage, const IndexedClause& icl, const std::string& origin)
  {
    std::string reason;
    bool ok = FO2Inferences::checkS2Invariant(icl, reason);
    recordWith(ok, reason, st, stage, icl, origin);
  }

  static void recordIndex(Stats& st, const char* stage, const IndexedClause& icl, const std::string& origin)
  {
    std::string reason;
    bool ok = FO2Inferences::checkIndexInvariant(icl, reason);
    recordWith(ok, reason, st, stage, icl, origin);
  }

  void checkGenerated(const IndexedClause& icl, const std::string& origin)
  {
    if (!enabled) return;
    record(generated, "generated", icl, origin);
    recordIndex(indexGen, "generated/index", icl, origin);
  }
  void checkActive(const IndexedClause& icl)
  {
    if (!enabled) return;
    record(active, "active", icl, "given");
    recordIndex(indexAct, "active/index", icl, "given");
    std::string reason;
    bool ok = FO2Inferences::checkSelectionCoversVars(icl, reason);
    recordWith(ok, reason, selection, "active/selection", icl, "given");
  }

  static void report(const char* stage, const Stats& st)
  {
    FO2Logger::logPhase(std::string("[S2 INVARIANT] ") + stage + ": checked " + std::to_string(st.checked) + " clauses, violations: " + std::to_string(st.violations));
    for (const auto& kv : st.byOrigin) {
      FO2Logger::logPhase(std::string("[S2 INVARIANT]   ") + stage + " by origin  " + kv.first + ": " + std::to_string(kv.second));
    }
    for (const auto& kv : st.byReason) {
      FO2Logger::logPhase(std::string("[S2 INVARIANT]   ") + stage + " by reason  " + kv.first + ": " + std::to_string(kv.second));
    }
  }

  ~S2Monitor()
  {
    if (!enabled) return;
    report("generated (before splitting)", generated);
    report("active (after splitting)", active);
    report("index condition, generated", indexGen);
    report("index condition, active", indexAct);
    report("Lemma 9 selection, active", selection);
  }
};
} // namespace

// Shared by splitting and saturation, so the bound applies to the complete
// search rather than being restarted for every branch.
static constexpr size_t MAX_TOTAL_ITERATIONS = 50000;

static FO2Result solveSaturated(Problem& prb, size_t& totalIterations, PhaseProfile& profile);

FO2Result FO2Solver::solve(Problem& prb)
{
  PhaseProfile profile;
  // Count the post-preprocessing input once, before splitting duplicates it
  // across alternative branches. Branch work below is cumulative instead.
  UnitList::Iterator initialInput(prb.units());
  while (initialInput.hasNext()) {
    if (initialInput.next()->isClause()) ++env.statistics->initialClauses;
  }
  env.statistics->phase = Shell::ExecutionPhase::SATURATION;
  env.statistics->finalActiveClauses = 0;
  env.statistics->finalPassiveClauses = 0;
  // Splitting creates alternative problems. Explore them iteratively so a
  // long chain of valid article-style splits cannot exhaust the C++ call stack.
  std::vector<UnitList*> pending{prb.units()};
  bool sawUnknown = false;
  size_t totalIterations = 0;
  while (!pending.empty()) {
    if (totalIterations >= MAX_TOTAL_ITERATIONS) {
      FO2Logger::logPhase("FO2 total iteration limit reached while exploring split branches: UNKNOWN");
      sawUnknown = true;
      break;
    }
    ++totalIterations; // Count each branch selected for examination.
    profile.count("branches_examined"); profile.peak("peak_branch_queue", pending.size()); profile.tick();

    UnitList* units = pending.back();
    pending.pop_back();
    Problem current(units);

    bool hasEquality = false;
    UnitList::Iterator equalityCheck(current.units());
    while (equalityCheck.hasNext() && !hasEquality) {
      Unit* unit = equalityCheck.next();
      if (!unit->isClause()) continue;
      Clause* clause = static_cast<Clause*>(unit);
      for (unsigned i = 0; i < clause->length(); ++i) {
        if ((*clause)[i]->isEquality()) {
          hasEquality = true;
          break;
        }
      }
    }
    if (hasEquality) {
      FO2Logger::logPhase("Input still contains built-in equality; expected equality-free clauses: UNKNOWN");
      sawUnknown = true;
      continue;
    }

    if (!profile.measure("propagation", [&] { return propagateUnits(current); })) {
      profile.count("branches_closed_by_propagation"); continue;
    }

    bool split = false;
    UnitList::Iterator splitIt(current.units());
    while (splitIt.hasNext()) {
      Unit* unit = splitIt.next();
      if (!unit->isClause()) continue;
      Clause* clause = static_cast<Clause*>(unit);
      std::vector<Literal*> r1, r2;
      if (!profile.measure("split_detection", [&] { return FO2Inferences::partitionClause(clause, r1, r2); })) continue;

      PhaseProfile::Scope splitTimer(profile, "split_construction");
      profile.count("splits"); profile.count("branches_created", 2);
      Problem branch1 = makeSplitBranch(current, clause, r1);
      Problem branch2 = makeSplitBranch(current, clause, r2);
      // LIFO: visit R1 first, while preserving R2 as the alternative branch.
      pending.push_back(branch2.units());
      pending.push_back(branch1.units());
      split = true;
      break;
    }
    if (split) continue;

    FO2Result result = solveSaturated(current, totalIterations, profile);
    if (result == FO2Result::SATISFIABLE) return result;
    if (result == FO2Result::UNKNOWN) sawUnknown = true;
  }

  return sawUnknown ? FO2Result::UNKNOWN : FO2Result::UNSATISFIABLE;
}

static FO2Result solveSaturated(Problem& prb, size_t& totalIterations, PhaseProfile& profile)
{
  FO2Logger::logPhase("Starting FO2 Saturation Engine (Section 4)");

  profile.count("saturation_calls");
  // Live snapshots also survive timeout termination without stack unwinding.
  // With splitting, these describe the most recent saturation branch.
  env.statistics->finalActiveClauses = 0;
  env.statistics->finalPassiveClauses = 0;
  PhaseProfile::Scope saturationTimer(profile, "saturation_other");
  S2Monitor s2Monitor;
  struct SearchMetrics {
    bool enabled = std::getenv("FO2_SEARCH_METRICS") != nullptr;
    size_t generated = 0, tautologies = 0, accepted = 0, peakPending = 0;
    size_t steps = 0, peakActive = 0, pendingRejected = 0, pendingRemoved = 0;
    size_t resolutionQueries = 0, resolutionCandidates = 0, resolutionFiltered = 0, activeRemoved = 0;
    void report() const {
      if (enabled) std::cerr << "FO2_SEARCH generated=" << generated
        << " tautologies=" << tautologies << " accepted=" << accepted
        << " peak_pending=" << peakPending << " steps=" << steps
        << " peak_active=" << peakActive << " pending_rejected=" << pendingRejected
        << " pending_removed=" << pendingRemoved
        << " resolution_queries=" << resolutionQueries << " resolution_candidates=" << resolutionCandidates
        << " resolution_filtered=" << resolutionFiltered << " active_removed=" << activeRemoved << std::endl;
    }
    ~SearchMetrics() { report(); }
  } metrics;
  // Exact complements are tautological regardless of proof indices. Merely
  // unifiable literals, e.g. p(X) | ~p(Y), must not be discarded.
  auto tautological = [](const IndexedClause& clause) {
    std::unordered_set<Literal*> literals;
    for (const auto& indexed : clause.literals()) {
      if (literals.count(Literal::complementaryLiteral(indexed.literal))) return true;
      literals.insert(indexed.literal);
    }
    return false;
  };
  struct PendingClause {
    size_t length;
    size_t age;
  };
  struct ShortestFirst {
    bool operator()(const PendingClause& left, const PendingClause& right) const {
      if (left.length != right.length) {
        return left.length > right.length;
      }
      return left.age > right.age;
    }
  };
  // Heap entries contain IDs only; each live clause is stored once. Four
  // shortest-first choices alternate with one oldest-first choice, so a long
  // clause cannot be postponed indefinitely by newly generated short clauses.
  std::priority_queue<PendingClause, std::vector<PendingClause>, ShortestFirst> passive;
  std::priority_queue<size_t, std::vector<size_t>, std::greater<size_t>> oldest;
  std::unordered_map<size_t, IndexedClause> pendingClauses;
  size_t givenSteps = 0;
  size_t nextAge = 0;
  using SubsumptionKey = std::tuple<unsigned, bool, unsigned>;
  auto signature = [](const IndexedClause& clause) {
    std::vector<SubsumptionKey> keys;
    for (const auto& literal : clause.literals()) {
      keys.emplace_back(literal.literal->functor(), literal.literal->polarity(), literal.index);
    }
    std::sort(keys.begin(), keys.end());
    keys.erase(std::unique(keys.begin(), keys.end()), keys.end());
    return keys;
  };
  struct ActiveClause {
    IndexedClause clause;
    std::vector<size_t> selected;
    std::vector<SubsumptionKey> signature;
    SubsumptionKey anchor;
  };
  std::map<size_t, ActiveClause> active;
  size_t nextActiveId = 0;
  // Resolve only selected literals with the same predicate and opposite sign.
  // Cache selection once per active clause instead of recomputing it for every
  // given clause (isSelected scans the containing clause).
  using LiteralKey = std::pair<unsigned, bool>;
  using LiteralLocation = std::pair<size_t, size_t>;
  // A variable is a wildcard; two distinct rigid argument roots cannot unify.
  using ArgumentRoots = std::vector<int64_t>;
  auto argumentRoots = [](const Literal* literal) {
    ArgumentRoots roots;
    for (unsigned i = 0; i < literal->arity(); ++i) {
      const auto& argument = *literal->nthArgument(i);
      roots.push_back(argument.isTerm() ? static_cast<int64_t>(argument.term()->functor()) : -1);
    }
    return roots;
  };
  auto compatibleRoots = [](const ArgumentRoots& left, const ArgumentRoots& right) {
    if (left.size() != right.size()) return false;
    for (size_t i = 0; i < left.size(); ++i)
      if (left[i] >= 0 && right[i] >= 0 && left[i] != right[i]) return false;
    return true;
  };
  std::map<LiteralKey, std::map<ArgumentRoots, std::set<LiteralLocation>>> resolutionIndex;
  std::map<LiteralKey, std::set<size_t>> unitIndex;
  // Every subsuming clause must have all its predicate/sign/index keys in
  // the target. One anchor suffices to retrieve forward candidates; all keys
  // are indexed to choose a small bucket for backward candidates.
  std::map<SubsumptionKey, std::set<size_t>> subsumptionAnchors;
  std::map<SubsumptionKey, std::set<size_t>> subsumptionIndex;
  auto indexActive = [&](size_t position) {
    auto& entry = active.at(position);
    if (entry.clause.length() == 1) {
      Literal* literal = entry.clause[0].literal;
      unitIndex[{literal->functor(), literal->polarity()}].insert(position);
    }
    for (size_t selected : entry.selected) {
      Literal* literal = entry.clause[selected].literal;
      resolutionIndex[{literal->functor(), literal->polarity()}][argumentRoots(literal)].emplace(position, selected);
    }
    SubsumptionKey anchor = entry.signature.front();
    size_t smallest = static_cast<size_t>(-1);
    for (const auto& key : entry.signature) {
      auto& bucket = subsumptionIndex[key];
      if (bucket.size() < smallest) { smallest = bucket.size(); anchor = key; }
      bucket.insert(position);
    }
    entry.anchor = anchor;
    subsumptionAnchors[anchor].insert(position);
  };
  auto eraseActive = [&](size_t id) {
    const auto& entry = active.at(id);
    auto eraseBucket = [&](auto& index, const auto& key) {
      auto bucket = index.find(key);
      bucket->second.erase(id);
      if (bucket->second.empty()) index.erase(bucket);
    };
    if (entry.clause.length() == 1) {
      auto* literal = entry.clause[0].literal;
      eraseBucket(unitIndex, LiteralKey{literal->functor(), literal->polarity()});
    }
    for (size_t selected : entry.selected) {
      auto* literal = entry.clause[selected].literal;
      auto predicate = resolutionIndex.find({literal->functor(), literal->polarity()});
      auto bucket = predicate->second.find(argumentRoots(literal));
      bucket->second.erase({id, selected});
      if (bucket->second.empty()) predicate->second.erase(bucket);
      if (predicate->second.empty()) resolutionIndex.erase(predicate);
    }
    eraseBucket(subsumptionAnchors, entry.anchor);
    for (const auto& key : entry.signature) eraseBucket(subsumptionIndex, key);
    active.erase(id);
    env.statistics->finalActiveClauses = active.size();
    ++metrics.activeRemoved; profile.count("active_removed");
  };
  const bool verifyIndex = std::getenv("FO2_VERIFY_INDEX") != nullptr;
  auto resolutionCandidates = [&](const Literal* literal) {
    PhaseProfile::Scope timer(profile, "resolution_lookup");
    ++metrics.resolutionQueries;
    std::vector<LiteralLocation> result;
    auto predicate = resolutionIndex.find({literal->functor(), !literal->polarity()});
    if (predicate != resolutionIndex.end()) {
      const auto roots = argumentRoots(literal);
      for (const auto& bucket : predicate->second) {
        if (compatibleRoots(roots, bucket.first)) {
          result.insert(result.end(), bucket.second.begin(), bucket.second.end());
        } else {
          metrics.resolutionFiltered += bucket.second.size();
        }
      }
    }
    metrics.resolutionCandidates += result.size(); profile.count("resolution_candidates", result.size());
    std::sort(result.begin(), result.end());
    if (verifyIndex) {
      // Independent full scan: every selected, actually unifiable partner
      // must be returned. False positives still go through normal resolution.
      for (const auto& item : active) {
        const auto& entry = item.second;
        for (size_t selected : entry.selected) {
          auto* candidate = entry.clause[selected].literal;
          if (candidate->functor() != literal->functor() || candidate->polarity() == literal->polarity()) continue;
          RobSubstitution substitution;
          if (substitution.unify(TermList(Literal::create(const_cast<Literal*>(literal), true)), 0,
                                 TermList(Literal::create(candidate, true)), 1) &&
              !std::binary_search(result.begin(), result.end(), LiteralLocation{item.first, selected}))
            throw std::logic_error("FO2 structural index lost a unifiable selected partner");
        }
      }
      for (const auto& location : result) {
        const auto& entry = active.at(location.first);
        if (std::find(entry.selected.begin(), entry.selected.end(), location.second) == entry.selected.end())
          throw std::logic_error("FO2 index returned an unselected literal");
      }
    }
    return result;
  };
  auto verifyActiveIndices = [&]() {
    if (!verifyIndex) return;
    decltype(resolutionIndex) expectedResolution;
    decltype(unitIndex) expectedUnits;
    decltype(subsumptionAnchors) expectedAnchors;
    decltype(subsumptionIndex) expectedSubsumption;
    for (const auto& item : active) {
      const size_t id = item.first;
      const auto& entry = item.second;
      if (entry.clause.length() == 1) {
        auto* literal = entry.clause[0].literal;
        expectedUnits[{literal->functor(), literal->polarity()}].insert(id);
      }
      for (size_t selected : entry.selected) {
        auto* literal = entry.clause[selected].literal;
        expectedResolution[{literal->functor(), literal->polarity()}][argumentRoots(literal)].emplace(id, selected);
      }
      if (!std::binary_search(entry.signature.begin(), entry.signature.end(), entry.anchor))
        throw std::logic_error("FO2 subsumption anchor is not in the clause signature");
      expectedAnchors[entry.anchor].insert(id);
      for (const auto& key : entry.signature) expectedSubsumption[key].insert(id);
    }
    if (resolutionIndex != expectedResolution || unitIndex != expectedUnits ||
        subsumptionAnchors != expectedAnchors || subsumptionIndex != expectedSubsumption)
      throw std::logic_error("FO2 incremental indices differ from complete reconstruction");
  };
  auto subsumedByActive = [&](const IndexedClause& clause,
                             const std::vector<SubsumptionKey>& keys) {
    PhaseProfile::Scope timer(profile, "active_forward_subsumption");
    for (const auto& key : keys) {
      auto candidates = subsumptionAnchors.find(key);
      if (candidates == subsumptionAnchors.end()) continue;
      for (size_t position : candidates->second) {
        const auto& entry = active.at(position);
        if (entry.clause.length() > clause.length() ||
            !std::includes(keys.begin(), keys.end(),
                           entry.signature.begin(), entry.signature.end())) continue;
        if (profile.measure("subsumption_match", [&] { profile.count("subsumption_tests"); return FO2Inferences::subsumes(entry.clause, clause); })) return true;
      }
    }
    return false;
  };
  struct PendingSignature {
    size_t length;
    std::vector<SubsumptionKey> keys;
    SubsumptionKey anchor;
  };
  std::unordered_map<size_t, PendingSignature> pendingSignatures;
  // Necessary-condition index only. Full indexed subsumption is unchanged.
  // Test each distinct signature once, and retrieve IDs only at eligible lengths.
  using LengthBuckets = std::map<size_t, std::set<size_t>>;
  // Sorted signature trie: forward queries follow only keys present in
  // the incoming signature. Terminal buckets therefore represent subsets.
  struct SignatureNode {
    std::map<SubsumptionKey, std::unique_ptr<SignatureNode>> children;
    LengthBuckets lengths;
  };
  SignatureNode pendingTrie;
  std::map<SubsumptionKey, LengthBuckets> pendingIndex;
  const bool verifyPending = std::getenv("FO2_VERIFY_PENDING_INDEX") != nullptr;
  auto bucketSize = [](const LengthBuckets& lengths) {
    size_t size = 0;
    for (const auto& item : lengths) size += item.second.size();
    return size;
  };
  // Maintain live IDs only: historical queue entries must not make these
  // candidate lists grow after clauses are selected or deleted.
  auto erasePending = [&](size_t age) {
    const auto& metadata = pendingSignatures.at(age);
    const size_t length = metadata.length;
    std::vector<std::pair<SignatureNode*, SubsumptionKey>> path;
    auto* node = &pendingTrie;
    for (const auto& key : metadata.keys) {
      path.emplace_back(node, key);
      node = node->children.at(key).get();
    }
    auto lengthBucket = node->lengths.find(length);
    lengthBucket->second.erase(age);
    if (lengthBucket->second.empty()) node->lengths.erase(lengthBucket);
    for (auto it = path.rbegin(); it != path.rend(); ++it) {
      auto child = it->first->children.find(it->second);
      if (!child->second->children.empty() || !child->second->lengths.empty()) break;
      it->first->children.erase(child);
    }
    for (const auto& key : metadata.keys) {
      auto bucket = pendingIndex.find(key);
      auto lengths = bucket->second.find(length);
      lengths->second.erase(age);
      if (lengths->second.empty()) bucket->second.erase(lengths);
      if (bucket->second.empty()) pendingIndex.erase(bucket);
    }
    pendingSignatures.erase(age);
    pendingClauses.erase(age);
    env.statistics->finalPassiveClauses = pendingClauses.size();
  };
  // Literals are shared by the kernel. Keep proof indices in the key: equal
  // unindexed clauses can have different inference eligibility.
  using ClauseKey = std::vector<std::pair<std::uintptr_t, unsigned>>;
  std::set<ClauseKey> seen;
  Substitution swapVariables;
  swapVariables.bind(0, TermList::var(1));
  swapVariables.bind(1, TermList::var(0));
  auto enqueue = [&](const IndexedClause& clause) {
    PhaseProfile::Scope enqueueTimer(profile, "enqueue_other");
    profile.count("enqueue_attempts"); profile.tick();
    ++metrics.generated;
    if (tautological(clause)) { ++metrics.tautologies; profile.count("tautology_rejections"); return; }
    ClauseKey key;
    {
    PhaseProfile::Scope duplicateTimer(profile, "duplicate_check");
    key.reserve(clause.length());
    for (const auto& literal : clause.literals()) {
      key.emplace_back(reinterpret_cast<std::uintptr_t>(literal.literal), literal.index);
    }
    std::sort(key.begin(), key.end());
    // Normalization numbers variables by their first occurrence, which depends
    // on literal order. In FO2 there are only two possible variable orders;
    // identify alpha-equivalent clauses while preserving each proof index.
    if (clause.varCount() == 2) {
      ClauseKey swapped;
      swapped.reserve(clause.length());
      for (const auto& literal : clause.literals()) {
        Literal* renamed = SubstHelper::apply(literal.literal, swapVariables);
        swapped.emplace_back(reinterpret_cast<std::uintptr_t>(renamed), literal.index);
      }
      std::sort(swapped.begin(), swapped.end());
      if (swapped < key) key = std::move(swapped);
    }
    // Exact/alpha duplicates are cheaper to reject than full subsumption.
    // Recheck subsumption at pop as the active set grows while clauses wait.
    if (seen.count(key)) { profile.count("duplicate_rejections"); return; }
    }
    const auto keys = signature(clause);
    if (subsumedByActive(clause, keys)) { profile.count("active_forward_rejections"); return; }
    {
    PhaseProfile::Scope pendingForwardTimer(profile, "pending_forward_scan");
    auto findSubsumer = [&](auto&& self, const SignatureNode& node, size_t start) -> bool {
      if (!node.lengths.empty()) {
        profile.count("pending_forward_signature_groups");
        const auto stop = node.lengths.upper_bound(clause.length());
        for (auto length = node.lengths.begin(); length != stop; ++length) {
          for (size_t age : length->second) {
            profile.count("pending_forward_ids_visited");
            const auto& candidate = pendingClauses.at(age);
            if (profile.measure("pending_forward_subsumption", [&] {
                  profile.count("subsumption_tests"); return FO2Inferences::subsumes(candidate, clause);
                })) return true;
          }
        }
      }
      for (size_t i = start; i < keys.size(); ++i) {
        profile.count("pending_forward_trie_probes");
        auto child = node.children.find(keys[i]);
        if (child != node.children.end() && self(self, *child->second, i + 1)) return true;
      }
      return false;
    };
    if (findSubsumer(findSubsumer, pendingTrie, 0)) {
      ++metrics.pendingRejected; profile.count("pending_forward_rejections");
      return;
    }
    // Independent exhaustive scan: no possible forward subsumer may be lost.
    // Do not use length or signature filters in this oracle.
    if (verifyPending) {
      for (const auto& candidate : pendingClauses)
        if (FO2Inferences::subsumes(candidate.second, clause))
          throw std::logic_error("FO2 pending index lost a forward subsumer");
    }
    }
    // A subsumed queued clause must contain every key of the new clause.
    // Retrieve candidates through the least populated required-key bucket.
    std::vector<size_t> removed;
    {
    PhaseProfile::Scope pendingBackwardTimer(profile, "pending_backward_scan");
    auto smallest = pendingIndex.end();
    size_t smallestSize = static_cast<size_t>(-1);
    for (const auto& required : keys) {
      auto bucket = pendingIndex.find(required);
      if (bucket == pendingIndex.end()) { smallest = pendingIndex.end(); break; }
      size_t eligible = 0;
      for (auto length = bucket->second.lower_bound(clause.length()); length != bucket->second.end(); ++length)
        eligible += length->second.size();
      if (eligible < smallestSize) { smallest = bucket; smallestSize = eligible; }
    }
    if (smallest != pendingIndex.end()) {
      for (auto length = smallest->second.lower_bound(clause.length()); length != smallest->second.end(); ++length) {
        for (size_t age : length->second) {
          profile.count("pending_backward_ids_visited");
          const auto& candidate = pendingClauses.at(age);
          const auto& candidateKeys = pendingSignatures.at(age).keys;
          if (!std::includes(candidateKeys.begin(), candidateKeys.end(), keys.begin(), keys.end())) {
            profile.count("pending_backward_signature_filtered"); continue;
          }
          if (profile.measure("pending_backward_subsumption", [&] {
                profile.count("subsumption_tests"); return FO2Inferences::subsumes(clause, candidate);
              })) removed.push_back(age);
        }
      }
    }
    if (verifyPending) {
      std::vector<size_t> expected;
      for (const auto& candidate : pendingClauses)
        if (FO2Inferences::subsumes(clause, candidate.second)) expected.push_back(candidate.first);
      std::sort(expected.begin(), expected.end());
      std::sort(removed.begin(), removed.end());
      if (expected != removed) throw std::logic_error("FO2 pending index backward subsumers differ from full scan");
    }
    }
    for (size_t age : removed) erasePending(age);
    metrics.pendingRemoved += removed.size(); profile.count("pending_removed", removed.size());
    PhaseProfile::Scope insertionTimer(profile, "passive_insert");
    if (seen.insert(std::move(key)).second) {
      const size_t age = nextAge++;
      pendingClauses.emplace(age, clause);
      ++env.statistics->passiveClauses;
      env.statistics->finalPassiveClauses = pendingClauses.size();
      SubsumptionKey anchor = keys.front();
      size_t smallestSize = static_cast<size_t>(-1);
      for (const auto& required : keys) {
        auto& bucket = pendingIndex[required];
        if (bucketSize(bucket) < smallestSize) { smallestSize = bucketSize(bucket); anchor = required; }
        bucket[clause.length()].insert(age);
      }
      pendingSignatures.emplace(age, PendingSignature{clause.length(), keys, anchor});
      auto* node = &pendingTrie;
      for (const auto& key : keys) {
        auto& child = node->children[key];
        if (!child) child = std::make_unique<SignatureNode>();
        node = child.get();
      }
      node->lengths[clause.length()].insert(age);
      passive.push({clause.length(), age});
      oldest.push(age);
      ++metrics.accepted; profile.count("accepted"); profile.peak("peak_pending", pendingClauses.size());
      metrics.peakPending = std::max(metrics.peakPending, pendingClauses.size());
    }
  };

  // Step 1: Collect and index initial clauses (S2+i class)
  {
  PhaseProfile::Scope initializationTimer(profile, "initialization_other");
  UnitList::Iterator uit(prb.units());
  while (uit.hasNext()) {
    Unit* u = uit.next();
    if (u->isClause()) {
      profile.count("initial_clauses");
      Clause* cl = static_cast<Clause*>(u);
      IndexedClause icl = IndexedClause::fromClause(cl);
      if (tautological(icl)) { ++metrics.generated; ++metrics.tautologies; continue; }
      for (const auto& ilit : icl.literals()) {
        if (!ilit.literal) continue;
        for (unsigned arg = 0; arg < ilit.literal->arity(); ++arg) {
          const TermList* termList = ilit.literal->nthArgument(arg);
          if (termList->isTerm() && termList->term()->arity() > 0 && termList->term()->arity() != 1) {
            FO2Logger::logPhase("Input is outside S2+i (non-unary function symbol): UNKNOWN");
            return FO2Result::UNKNOWN;
          }
        }
      }
      std::string invariantReason;
      if (!FO2Inferences::checkS2Invariant(icl, invariantReason) ||
          !FO2Inferences::checkIndexInvariant(icl, invariantReason)) {
        if (FO2Logger::showsPhases()) {
          FO2Logger::logPhase("Input is outside S2+i (" + invariantReason + "): UNKNOWN");
        }
        return FO2Result::UNKNOWN;
      }
      IndexedClause simpIcl;
      profile.measure("normalization", [&] { FO2Inferences::normalizeVariables(icl, simpIcl); });
      if (simpIcl.length() == 0) {
        FO2Logger::logPhase("Initial empty clause found: UNSATISFIABLE");
        return FO2Result::UNSATISFIABLE;
      }
      s2Monitor.checkGenerated(simpIcl, "initial");
      enqueue(simpIcl);
    }
  }

  }
  profile.report();
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[FO2Solver] Initial passive clauses: " + std::to_string(pendingClauses.size()));
  }

  while (!pendingClauses.empty() && totalIterations < MAX_TOTAL_ITERATIONS) {
    ++totalIterations; // Count each given-clause processing step.
    ++env.statistics->activations;
    ++metrics.steps; profile.count("given_steps"); profile.tick();
    if (metrics.enabled && metrics.steps % 1000 == 0) metrics.report();

    size_t age;
    if (++givenSteps % 5 == 0) {
      while (!pendingClauses.count(oldest.top())) oldest.pop();
      age = oldest.top();
      oldest.pop();
    } else {
      while (!pendingClauses.count(passive.top().age)) passive.pop();
      age = passive.top().age;
      passive.pop();
    }
    IndexedClause given = std::move(pendingClauses.at(age));
    erasePending(age);

    if (given.length() == 0) {
      FO2Logger::logPhase("Derived empty clause found: UNSATISFIABLE");
      return FO2Result::UNSATISFIABLE;
    }

    // Delete a selected literal only through a matching unit inference that
    // produces an indexed subsumer in S2+i. Recompute selection after each
    // shortening, since the eligible literals may have changed.
    bool shortened;
    do {
      shortened = false;
      for (size_t selected : given.getSelectedLiteralIndices()) {
        Literal* literal = given[selected].literal;
        auto units = unitIndex.find({literal->functor(), !literal->polarity()});
        if (units == unitIndex.end()) continue;
        for (size_t position : units->second) {
          IndexedClause replacement;
          if (!profile.measure("unit_simplification", [&] { profile.count("unit_attempts"); return FO2Inferences::simplifyWithUnit(given, active.at(position).clause, replacement); })) continue;
          given = replacement;
          if (given.length() == 0) return FO2Result::UNSATISFIABLE;
          shortened = true;
          break;
        }
        if (shortened) break;
      }
    } while (shortened);

    if (FO2Logger::showsDebug()) {
      FO2Logger::logDebug("[FO2Solver Step " + std::to_string(totalIterations) + "] Given: " + given.toStringWithSelection());
    }

    // Step 2: Forward Subsumption check
    const auto givenSignature = signature(given);
    if (subsumedByActive(given, givenSignature)) { profile.count("given_forward_rejections"); continue; }

    // Clauses must enter in S2+i after the branching split rule above.
    s2Monitor.checkActive(given);

    // Step 4: Backward Subsumption (remove active clauses subsumed by given)
    const std::set<size_t>* backwardCandidates = nullptr;
    for (const auto& key : givenSignature) {
      auto bucket = subsumptionIndex.find(key);
      if (bucket == subsumptionIndex.end()) { backwardCandidates = nullptr; break; }
      if (!backwardCandidates || bucket->second.size() < backwardCandidates->size()) {
        backwardCandidates = &bucket->second;
      }
    }
    std::set<size_t> removed;
    if (given.length() == 1) {
      Literal* literal = given[0].literal;
      const auto candidates = resolutionCandidates(literal);
      {
        for (const auto& location : candidates) {
          const size_t position = location.first;
          if (removed.count(position)) continue;
          IndexedClause replacement;
          if (!profile.measure("unit_simplification", [&] { profile.count("unit_attempts"); return FO2Inferences::simplifyWithUnit(active.at(position).clause, given, replacement); })) continue;
          if (replacement.length() == 0) return FO2Result::UNSATISFIABLE;
          profile.count("unit_outputs"); enqueue(replacement);
          removed.insert(position);
        }
      }
    }
    if (backwardCandidates) {
      for (size_t position : *backwardCandidates) {
        const auto& entry = active.at(position);
        const auto& act = entry.clause;
        if (given.length() <= act.length() &&
            std::includes(entry.signature.begin(), entry.signature.end(),
                          givenSignature.begin(), givenSignature.end()) &&
            profile.measure("active_backward_subsumption", [&] { profile.count("subsumption_tests"); return FO2Inferences::subsumes(given, act); })) {
          if (FO2Logger::showsDebug()) {
            FO2Logger::logDebug("[FO2Solver] Active clause replaced by subsumption: " + act.toString());
          }
          removed.insert(position);
        }
      }
    }
    for (size_t id : removed) eraseActive(id);
    verifyActiveIndices();

    // Step 5: Factoring on Given
    const auto selectedForFactoring = given.getSelectedLiteralIndices();
    for (size_t i : selectedForFactoring) {
      for (size_t j = 0; j < given.length(); ++j) {
        if (i == j) continue;
        IndexedClause factorRes;
        if (profile.measure("factoring", [&] { profile.count("factor_attempts"); return FO2Inferences::factor(given, i, j, factorRes); })) {
          IndexedClause simpFactor;
          profile.measure("normalization", [&] { FO2Inferences::normalizeVariables(factorRes, simpFactor); });
          if (simpFactor.length() == 0) {
            FO2Logger::logPhase("Empty clause derived from Factoring: UNSATISFIABLE");
            return FO2Result::UNSATISFIABLE;
          }
          if (FO2Logger::showsDebug()) {
            FO2Logger::logDebug("[FO2Solver] Generated factor: " + simpFactor.toStringWithSelection());
          }
          s2Monitor.checkGenerated(simpFactor, "factoring");
          profile.count("factor_outputs"); enqueue(simpFactor);
        }
      }
    }

    // Step 6: Resolution between Given and Active clauses
    const auto& selG = selectedForFactoring;
    for (size_t idxG : selG) {
      const Literal* litG = given[idxG].literal;
      const auto candidates = resolutionCandidates(litG);
      for (const auto& location : candidates) {
        const auto& act = active.at(location.first).clause;
        const size_t idxA = location.second;
        IndexedClause resolvent1;
        if (profile.measure("resolution", [&] { profile.count("resolution_attempts"); return FO2Inferences::resolve(given, idxG, act, idxA, resolvent1); })) {
          IndexedClause simpRes1;
          profile.measure("normalization", [&] { FO2Inferences::normalizeVariables(resolvent1, simpRes1); });
          if (simpRes1.length() == 0) {
            FO2Logger::logPhase("Empty clause derived from Resolution: UNSATISFIABLE");
            return FO2Result::UNSATISFIABLE;
          }
          if (FO2Logger::showsDebug()) {
            FO2Logger::logDebug("[FO2Solver] Generated resolvent: " + simpRes1.toStringWithSelection());
          }
          s2Monitor.checkGenerated(simpRes1, "resolution");
          profile.count("resolution_outputs"); enqueue(simpRes1);
        }

        // Swapping these same two pivots only renames the MGU's variables.
        // Generate their resolvent once; distinct pivot pairs are still visited.
      }
    }

    const size_t activeId = nextActiveId++;
    active.emplace(activeId, ActiveClause{given, selectedForFactoring, givenSignature, {}});
    ++env.statistics->activeClauses;
    env.statistics->finalActiveClauses = active.size();
    profile.measure("active_index", [&] { indexActive(activeId); });
    verifyActiveIndices();
    metrics.peakActive = std::max(metrics.peakActive, active.size()); profile.peak("peak_active", active.size());
  }

  if (!pendingClauses.empty()) {
    FO2Logger::logPhase("FO2 total iteration limit reached without complete saturation: UNKNOWN");
    return FO2Result::UNKNOWN;
  }

  FO2Logger::logPhase("Saturation Engine completed without empty clause: SATISFIABLE");
  return FO2Result::SATISFIABLE;
}

} // namespace FO2Fragment

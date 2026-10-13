/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable copyright laws.
 * It is distributed under the licence found at https://vprover.github.io/license.html
 */
#include "TPTPReplayProofPrinter.hpp"

#include "Debug/Assertion.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "SAT/SATLiteral.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/ClausificationRecording.hpp"
#include "Shell/FunctionDefinition.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Shell/Options.hpp"

#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <unordered_set>

namespace Kernel {

using namespace Lib;

namespace {
std::string replayUnitId(Unit* unit)
{
  return "f" + Lib::Int::toString(unit->number());
}

const Saturation::AvatarConversionExtra* avatarConversionExtra(Unit* origin)
{
  if (origin->inference().rule() != InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT) {
    return nullptr;
  }
  return static_cast<const Saturation::AvatarConversionExtra*>(env.proofExtra.find(origin));
}

bool isConstrainedRule(InferenceRule rule)
{
  return rule == InferenceRule::CONSTRAINED_RESOLUTION ||
         rule == InferenceRule::CONSTRAINED_SUPERPOSITION;
}

bool reversedEquality(Literal* source, Literal* target)
{
  return source->isEquality() && target->isEquality() && source->header() == target->header() &&
    source->eqArgSort() == target->eqArgSort() &&
    source->nthArgument(0)->sameContent(*target->nthArgument(1)) &&
    source->nthArgument(1)->sameContent(*target->nthArgument(0));
}
}

/** Print a term inside a generic annotation. Variables keep their printed
 * clause names. In higher-order problems every other term, including sorts,
 * is wrapped in `$thf(...)`: generic TPTP annotation terms cannot contain
 * lambdas, applications or arrow types directly. */
std::string tptpReplayTerm(TermList term)
{
  if (term.isVar() || !env.higherOrder()) { return term.toString(); }
  return "$thf(" + term.toString() + ")";
}

static std::string unifierAnnotation(const Shell::InferenceRecorder::InferenceInformation* information);
static std::string constraintsAnnotation(Unit* conclusion,
    const Shell::InferenceRecorder::InferenceInformation* information);
static std::string rewriteAnnotation(const Shell::InferenceRecorder::InferenceInformation* information);
static std::string literalPositionsAnnotation(
    Unit* conclusion, const Shell::InferenceRecorder::InferenceInformation* information);
static std::string subsumptionResolutionAnnotation(
    const Shell::InferenceRecorder::InferenceReplayAnnotation& replay);

InferenceStore::TPTPReplayProofPrinter::TPTPReplayProofPrinter(std::ostream& out, InferenceStore* is)
  : TPTPProofPrinter(out, is), _replay(env.options->replay())
{
  if (_replay) {
    _replayer = std::make_unique<Shell::InferenceReplayer>();
    _replayer->makeInferenceEngine(is->ordering);
  }
}

InferenceStore::TPTPReplayProofPrinter::~TPTPReplayProofPrinter() = default;

std::string formatTPTPReplayAnnotations(
    Unit* conclusion, const Shell::InferenceRecorder::InferenceReplayAnnotation& replay)
{
  if (replay.removedLiteralParent) {
    return subsumptionResolutionAnnotation(replay);
  }

  const auto* information = replay.information;
  std::vector<std::string> annotations = {
    unifierAnnotation(information),
    constraintsAnnotation(conclusion, information),
    rewriteAnnotation(information),
    literalPositionsAnnotation(conclusion, information)
  };
  std::string result;
  for (const auto& annotation : annotations) {
    if (annotation.empty()) { continue; }
    if (!result.empty()) { result += ','; }
    result += annotation;
  }
  return result;
}

static std::string unifierAnnotation(
    const Shell::InferenceRecorder::InferenceInformation* information)
{
  if (!information || information->premises.empty()) { return {}; }
  std::ostringstream out;
  out << "unifier([";
  for (unsigned bank = 0; bank < information->substitutionForBanksSub.size(); ++bank) {
    if (bank) { out << ','; }
    out << "subs(";
    if (bank < information->premises.size()) {
      out << replayUnitId(information->premises[bank]);
    } else {
      out << bank;
    }
    out << ",[";
    bool first = true;
    auto substitution = information->substitutionForBanksSub[bank];
    for (auto [variable, term] : Lib::iterTraits(substitution.items())) {
      if (!first) { out << ','; }
      first = false;
      out << "b(X" << variable << ',' << tptpReplayTerm(term) << ')';
    }
    out << "])";
  }
  out << "])";
  return out.str();
}

static std::string constraintsAnnotation(Unit* conclusion,
    const Shell::InferenceRecorder::InferenceInformation* information)
{
  // Constrained rules state their (possibly empty) constraint list explicitly,
  // so the checker need not distinguish "none" from "not recorded".
  if (!information ||
      (information->constraints.empty() && !isConstrainedRule(conclusion->inference().rule()))) {
    return {};
  }
  std::ostringstream out;
  out << "constraints([";
  bool first = true;
  for (Kernel::Literal* literal : information->constraints) {
    ASS(literal->isEquality() && literal->isNegative());
    if (!first) { out << ','; }
    first = false;
    auto [left, right] = literal->eqArgs();
    out << "disequality(" << tptpReplayTerm(literal->eqArgSort()) << ','
        << tptpReplayTerm(left) << ',' << tptpReplayTerm(right) << ')';
  }
  out << "])";
  return out.str();
}

static std::string rewriteAnnotation(
    const Shell::InferenceRecorder::InferenceInformation* information)
{
  if (!information || !information->hasRewrite) { return {}; }
  auto position = [&](const auto& literalPosition) {
    return "literal(" + replayUnitId(information->premises[literalPosition.premiseIndex]) + ',' +
           Lib::Int::toString(literalPosition.literalIndex) + ')';
  };
  return "rewrite([equality(" + position(information->rewriteEquality) + "),from(" +
         tptpReplayTerm(information->rewriteFrom) + "),to(" + tptpReplayTerm(information->rewriteTo) + ")])";
}

static std::string literalPositionsAnnotation(
    Unit* conclusion, const Shell::InferenceRecorder::InferenceInformation* information)
{
  if (!information) { return {}; }
  std::ostringstream out;
  auto printPosition = [&](const auto& position) {
    out << "literal(" << replayUnitId(information->premises[position.premiseIndex])
        << ',' << position.literalIndex << ')';
  };
  if (conclusion->inference().rule() == InferenceRule::FORWARD_LITERAL_REWRITING &&
      !information->literalPositions.empty()) {
    const auto& position = information->literalPositions[0];
    out << "rewritten_literal(literal(" << replayUnitId(information->premises[position.premiseIndex])
        << ',' << position.literalIndex << "))";
  }

  if (!information->literalPositions.empty()) {
    using PositionKind = Shell::InferenceRecorder::InferenceInformation::LiteralPositionKind;
    if (!out.str().empty()) { out << ','; }
    switch (information->literalPositionKind) {
    case PositionKind::REWRITTEN:
      out << (information->literalPositions.size() == 1 ? "rewritten_literal(" : "rewritten_literals([");
      break;
    case PositionKind::RESOLVED:
      out << "resolved_literals([";
      break;
    case PositionKind::REMOVED:
      out << "removed_literals(";
      break;
    case PositionKind::NONE:
      ASSERTION_VIOLATION;
    }
    bool first = true;
    for (const auto& position : information->literalPositions) {
      if (!first) { out << ','; }
      first = false;
      printPosition(position);
    }
    bool list = information->literalPositionKind == PositionKind::RESOLVED ||
                (information->literalPositionKind == PositionKind::REWRITTEN &&
                 information->literalPositions.size() != 1);
    out << (list ? "])" : ")");
  }
  return out.str();
}

static std::string subsumptionResolutionAnnotation(
    const Shell::InferenceRecorder::InferenceReplayAnnotation& replay)
{
  std::ostringstream out;
  if (replay.subsumptionUnifierParent) {
    out << "unifier([subs(" << replayUnitId(replay.subsumptionUnifierParent) << ",[";
    bool first = true;
    for (const auto& binding : replay.subsumptionBindings) {
      if (!first) { out << ','; }
      first = false;
      out << "b(X" << binding.variable << ',' << tptpReplayTerm(binding.term) << ')';
    }
    out << "])])";
  }
  if (out.tellp() > 0) { out << ','; }
  out << "removed_literals(literal(" << replayUnitId(replay.removedLiteralParent)
      << ',' << replay.removedLiteralIndex << "))";
  return out.str();
}

namespace {
TermList replaceOccurrenceIn(TermList term, TermList from, TermList to,
                             unsigned target, unsigned& seen, bool& done)
{
  if (done) { return term; }
  if (term == from) {
    if (seen++ == target) {
      done = true;
      return to;
    }
    return term;
  }
  if (term.isVar() || term.term()->isSort() || term.term()->isSpecial()) { return term; }
  Term* original = term.term();
  std::vector<TermList> args;
  bool changed = false;
  for (unsigned i = 0; i < original->arity(); ++i) {
    TermList arg = *original->nthArgument(i);
    args.push_back(replaceOccurrenceIn(arg, from, to, target, seen, done));
    changed |= args.back() != arg;
  }
  return changed ? TermList(Term::create(original, args.data())) : term;
}
} // namespace

Literal* replaceOccurrence(Literal* literal, TermList from, TermList to, unsigned occurrence)
{
  unsigned seen = 0;
  bool done = false;
  std::vector<TermList> args;
  for (unsigned i = 0; i < literal->arity(); ++i) {
    args.push_back(replaceOccurrenceIn(*literal->nthArgument(i), from, to, occurrence, seen, done));
  }
  return done ? Literal::create(literal, args.data()) : nullptr;
}

/**
 * Definition unfolding by a single definition `l = r`, recovered from the
 * parent and the natural (pre-selection) conclusion. Every rewritten
 * literal must be the parent literal with all occurrences of one instance
 * `l\sigma` replaced by `r\sigma`. Otherwise, if a single literal changed, a
 * single occurrence may be selected with `occurrence(n)`. Several used
 * definitions, nested unfolding or several instances get no certificate.
 */
std::string tptpDefinitionUnfoldingReplayAnnotation(Unit* conclusion)
{
  if (conclusion->inference().rule() != InferenceRule::DEFINITION_UNFOLDING || !conclusion->isClause()) {
    return "";
  }
  if (env.options->proofExtra() != Options::ProofExtra::REPLAY) { return ""; }
  const auto* extra = static_cast<const Shell::FunctionDefinitionExtra*>(env.proofExtra.find(conclusion));
  if (!extra) { return ""; }
  UnitIterator parents = conclusion->getParents();
  if (!parents.hasNext()) { return ""; }
  Unit* mainUnit = parents.next();
  if (!parents.hasNext()) { return ""; }
  // The definition is listed once per unfolded occurrence. Each position is
  // a separate substitution bank, all instantiated identically.
  Unit* definitionUnit = parents.next();
  unsigned definitionBanks = 1;
  while (parents.hasNext()) {
    if (parents.next() != definitionUnit) { return ""; }
    ++definitionBanks;
  }
  if (!mainUnit->isClause() || !definitionUnit->isClause()) { return ""; }
  Clause* main = mainUnit->asClause();
  Clause* definition = definitionUnit->asClause();
  const auto& natural = extra->naturalLiterals;
  if (definition->length() != 1 || !(*definition)[0]->isEquality() ||
      !(*definition)[0]->isPositive() || natural.size() != main->length()) {
    return "";
  }
  std::vector<unsigned> changed;
  for (unsigned i = 0; i < natural.size(); ++i) {
    if ((*main)[i] != natural[i]) { changed.push_back(i); }
  }
  if (changed.empty()) { return ""; }

  Literal* equation = (*definition)[0];
  for (unsigned side = 0; side < 2; ++side) {
    TermList from = equation->termArg(side);
    TermList to = equation->termArg(1 - side);
    if (from.isVar()) { continue; }
    std::vector<Substitution> candidates;
    if (from.isTerm() && from.term()->ground()) {
      candidates.emplace_back();
    } else {
      for (unsigned i : changed) {
        NonVariableNonTypeIterator subterms((*main)[i]);
        while (subterms.hasNext()) {
          Substitution candidate;
          if (MatchingUtils::matchTerms(from, TermList(subterms.next()), candidate)) {
            candidates.push_back(std::move(candidate));
          }
        }
      }
    }
    for (auto& candidate : candidates) {
      bool closed = true;
      VariableIterator variables(to);
      while (variables.hasNext()) {
        TermList value;
        closed &= candidate.findBinding(variables.next().var(), value);
      }
      if (!closed) { continue; }
      TermList fromInstance = SubstHelper::apply(from, candidate);
      TermList toInstance = SubstHelper::apply(to, candidate);
      bool allOccurrences = true;
      for (unsigned i = 0; i < natural.size() && allOccurrences; ++i) {
        allOccurrences = EqHelper::replace((*main)[i], fromInstance, toInstance) == natural[i];
      }
      int occurrence = -1;
      if (!allOccurrences && changed.size() == 1) {
        for (unsigned n = 0;; ++n) {
          Literal* single = replaceOccurrence((*main)[changed[0]], fromInstance, toInstance, n);
          if (!single) { break; }
          if (single == natural[changed[0]]) {
            occurrence = n;
            break;
          }
        }
      }
      if (!allOccurrences && occurrence < 0) { continue; }

      std::ostringstream out;
      std::vector<std::pair<unsigned, TermList>> bindings;
      for (auto [variable, term] : iterTraits(candidate.items())) { bindings.emplace_back(variable, term); }
      std::sort(bindings.begin(), bindings.end(),
                [](const auto& left, const auto& right) { return left.first < right.first; });
      out << "unifier([subs(" << replayUnitId(main) << ",[])";
      for (unsigned bank = 0; bank < definitionBanks; ++bank) {
        out << ",subs(" << replayUnitId(definition) << ",[";
        for (unsigned i = 0; i < bindings.size(); ++i) {
          if (i) { out << ','; }
          out << "b(X" << bindings[i].first << ',' << tptpReplayTerm(bindings[i].second) << ')';
        }
        out << "])";
      }
      out << "]),";
      out << (changed.size() == 1 ? "rewritten_literal(" : "rewritten_literals([");
      for (unsigned i = 0; i < changed.size(); ++i) {
        if (i) { out << ','; }
        out << "literal(" << replayUnitId(main) << ',' << changed[i] << ')';
      }
      out << (changed.size() == 1 ? ")" : "])");
      out << ",rewrite([equality(literal(" << replayUnitId(definition) << ",0)),from("
          << tptpReplayTerm(fromInstance) << "),to(" << tptpReplayTerm(toInstance) << ')';
      if (occurrence >= 0) { out << ",occurrence(" << occurrence << ')'; }
      out << "])";
      return out.str();
    }
  }
  return "";
}

std::string tptpClausificationReplayAnnotation(Unit* conclusion, bool replay)
{
  if (!replay || !conclusion->isClause() || conclusion->inference().rule() != InferenceRule::CLAUSIFY) { return ""; }
  const auto* stored = env.proofExtra.find(conclusion);
  if (!stored) { return ""; }
  const auto* extra = static_cast<const Shell::ClausificationExtra*>(stored);
  Clause* clause = conclusion->asClause();
  if (clause->length() != extra->occurrences.size()) { return ""; }
  std::vector<bool> used(extra->occurrences.size(), false);
  std::vector<unsigned> permutation, swapped;
  for (unsigned i = 0; i < clause->length(); ++i) {
    unsigned j = 0;
    bool reversed = false;
    for (; j < extra->occurrences.size(); ++j) {
      if (!used[j] && extra->occurrences[j].instantiated == (*clause)[i]) { break; }
    }
    if (j == extra->occurrences.size()) {
      for (j = 0; j < extra->occurrences.size(); ++j) {
        if (!used[j] && reversedEquality(extra->occurrences[j].instantiated, (*clause)[i])) { break; }
      }
      if (j == extra->occurrences.size()) { return ""; }
      reversed = true;
    }
    used[j] = true;
    permutation.push_back(j);
    if (extra->occurrences[j].flipped != reversed) { swapped.push_back(i); }
  }
  std::ostringstream out;
  if (extra->newcnf) {
    out << "newcnf([";
    for (unsigned i = 0; i < extra->newcnf->events.size(); ++i) {
      if (i) { out << ','; }
      out << extra->newcnf->events[i];
    }
    out << "],clause_index(" << extra->clauseIndex << "))";
  } else {
    out << "binder_mapping([";
    for (unsigned i = 0; i < extra->binders.size(); ++i) {
      if (i) { out << ','; }
      auto [source, target] = extra->binders[i];
      out << "b(X" << source << ",X" << target << ')';
    }
    out << "])";
  }
  auto indices = [&out](const char* name, const std::vector<unsigned>& values) {
    out << ',' << name << "([";
    for (unsigned i = 0; i < values.size(); ++i) {
      if (i) { out << ','; }
      out << values[i];
    }
    out << "])";
  };
  indices("literal_permutation", permutation);
  indices("swapped_equalities", swapped);
  return out.str();
}

std::string tptpAvatarConversionReplayAnnotation(Unit* origin)
{
  const auto* extra = avatarConversionExtra(origin);
  if (!extra) { return ""; }
  std::ostringstream out;
  out << "avatar_map([";
  bool first = true;
  for (const auto& mapping : extra->mappings) {
    if (!first) { out << ','; }
    first = false;
    SAT::SATLiteral positive(mapping.avatarVariable, true);
    out << "map(literal(" << replayUnitId(origin) << ',' << mapping.literalIndex << "),"
        << (mapping.positive ? "positive(" : "negative(")
        << Saturation::Splitter::getFormulaStringFromLiteral(positive) << "),"
        << replayUnitId(mapping.definition) << ')';
  }
  out << "])";
  return out.str();
}

std::vector<Unit*> tptpAvatarConversionReplayDefinitions(Unit* origin)
{
  std::vector<Unit*> definitions;
  if (const auto* extra = avatarConversionExtra(origin)) {
    std::unordered_set<Unit*> seen;
    for (const auto& mapping : extra->mappings) {
      if (seen.insert(mapping.definition).second) { definitions.push_back(mapping.definition); }
    }
  }
  return definitions;
}


std::string tptpRectificationReplayAnnotation(Unit* us, bool replay)
{
  if (!replay || us->inference().rule() != InferenceRule::RECTIFY) {
    return "";
  }
  const auto* info = Shell::InferenceRecorder::instance()->getRectificationReplayInformation(us->number());
  if (!info || info->scopes.empty()) {
    return "";
  }

  std::ostringstream result;
  // `postorder` makes scope association unambiguous for nested and sibling
  // quantifiers. `before`/`after` retain their declared binder order;
  // `substitution` is LeanChecker's combined occurrence map, not merely a
  // fresh-name map, so it captures permutations inside terms as well.
  result << "rectify([postorder([";
  bool firstScope = true;
  for (const auto& scope : info->scopes) {
    std::vector<std::string> entries;
    auto printBinders = [](const char* name, const std::vector<unsigned>& binders) {
      std::ostringstream result;
      result << name << "([";
      for (unsigned i = 0; i < binders.size(); ++i) {
        if (i) {
          result << ',';
        }
        result << "X" << binders[i];
      }
      result << "])";
      return result.str();
    };
    Substitution renaming = scope.renaming;
    std::vector<std::pair<unsigned, std::string>> bindings;
    for (auto [source, target] : iterTraits(renaming.items())) {
      if (scope.removed.find(source) != scope.removed.end() ||
          target == TermList::var(source)) {
        continue;
      }
      bindings.emplace_back(source,
        "b(X" + Int::toString(source) + "," + target.toString() + ")");
    }
    std::sort(bindings.begin(), bindings.end(),
      [](const auto& left, const auto& right) { return left.first < right.first; });
    // A fresh one-variable binder is alpha-equivalent and needs no proof
    // step. Retain a scope only if LeanChecker's combined substitution
    // records a genuine variable permutation or a binder was removed.
    if (bindings.empty() && scope.removed.empty()) {
      continue;
    }
    entries.push_back(printBinders("before", scope.sourceBinders));
    entries.push_back(printBinders("after", scope.targetBinders));
    if (!bindings.empty()) {
      std::ostringstream substitution;
      substitution << "substitution([";
      for (unsigned i = 0; i < bindings.size(); ++i) {
        if (i) {
          substitution << ',';
        }
        substitution << bindings[i].second;
      }
      substitution << "])";
      entries.push_back(substitution.str());
    }
    if (!scope.removed.empty()) {
      std::ostringstream removed;
      removed << "removed([";
      bool firstRemoved = true;
      for (unsigned variable : scope.removed) {
        if (!firstRemoved) {
          removed << ',';
        }
        firstRemoved = false;
        removed << "X" << variable;
      }
      removed << "])";
      entries.push_back(removed.str());
    }
    if (!firstScope) {
      result << ',';
    }
    firstScope = false;
    result << "scope([";
    for (unsigned i = 0; i < entries.size(); ++i) {
      if (i) {
        result << ',';
      }
      result << entries[i];
    }
    result << "])";
  }
  result << "])])";
  return firstScope ? "" : result.str();
}

struct AvatarSplitComponent {
  Unit* definition;
  Clause* clause;
};

struct AvatarSplitVariableTarget {
  Unit* definition;
  unsigned variable;
};

/**
 * Return the variable-disjoint literal components used by AVATAR splitting.
 * This is the part of Splitter::getComponents needed by the proof printer,
 * deliberately without its statistics side effects.
 */
static std::vector<std::vector<Literal*>> avatarSplitComponents(Clause* clause)
{
  std::vector<std::vector<Literal*>> result;
  if (clause->length() == 0) {
    return result;
  }

  std::vector<unsigned> parents(clause->length());
  for (unsigned i = 0; i < parents.size(); ++i) {
    parents[i] = i;
  }
  auto findRoot = [&parents](unsigned index) {
    while (parents[index] != index) {
      parents[index] = parents[parents[index]];
      index = parents[index];
    }
    return index;
  };
  auto merge = [&findRoot, &parents](unsigned first, unsigned second) {
    first = findRoot(first);
    second = findRoot(second);
    if (first != second) {
      parents[second] = first;
    }
  };

  std::map<unsigned, unsigned> masters;
  for (unsigned literalIndex = 0; literalIndex < clause->length(); ++literalIndex) {
    VariableIterator variables((*clause)[literalIndex]);
    while (variables.hasNext()) {
      unsigned variable = variables.next().var();
      auto [master, inserted] = masters.emplace(variable, literalIndex);
      if (!inserted) {
        merge(master->second, literalIndex);
      }
    }
  }

  std::map<unsigned, std::vector<Literal*>> components;
  for (unsigned literalIndex = 0; literalIndex < clause->length(); ++literalIndex) {
    components[findRoot(literalIndex)].push_back((*clause)[literalIndex]);
  }
  for (auto& [_, component] : components) {
    result.push_back(std::move(component));
  }
  return result;
}

/**
 * Recover the argument order used after the AVATAR-definition rewrites.
 *
 * The first premise is the original clause.  Each newly introduced
 * definition premise is a variant of one variable-disjoint component of
 * that clause.  Consequently the variant renaming tells us exactly which
 * definition variable is passed for each original-clause variable.  Unlike
 * LeanChecker, this does not need SATClauseExtra: the original clause's
 * split set already distinguishes old definitions from definitions added by
 * this split.  SplitDefinitionExtra remains necessary to get the component
 * clause behind a definition formula.
 */
std::string tptpAvatarSplitInstantiationReplayAnnotation(Unit* conclusion)
{
  if (conclusion->inference().rule() != InferenceRule::AVATAR_SPLIT_CLAUSE) {
    return "";
  }

  UnitIterator parents = conclusion->getParents();
  if (!parents.hasNext()) {
    return "";
  }
  Unit* originalUnit = parents.next();
  if (!originalUnit->isClause()) {
    return "";
  }
  Clause* original = originalUnit->asClause();

  std::set<unsigned> oldSplitVariables;
  if (!original->noSplits()) {
    for (SplitLevel split : iterTraits(original->splits()->iter())) {
      oldSplitVariables.insert(Saturation::Splitter::getLiteralFromName(split).var());
    }
  }

  std::vector<AvatarSplitComponent> newComponents;
  while (parents.hasNext()) {
    Unit* definition = parents.next();
    if (definition->inference().rule() != InferenceRule::AVATAR_DEFINITION) {
      return "";
    }
    // Ground definitions supply no arguments. In particular, a negative
    // ground component may have no SplitDefinitionExtra: its definition is
    // stored with the positive polarity. It must not prevent recovery of
    // the variable arguments supplied by the other definitions.
    if (!definition->isClause()) {
      Formula* formula = static_cast<FormulaUnit*>(definition)->formula();
      if (formula->connective() == IFF && formula->right()->connective() == LITERAL &&
          formula->right()->literal()->ground()) {
        continue;
      }
    }
    const auto* extra = env.proofExtra.find(definition);
    if (!extra) {
      return "";
    }
    const auto* splitDefinition = static_cast<const Saturation::SplitDefinitionExtra*>(extra);
    Clause* component = splitDefinition->component;
    if (!component || !component->isComponent() || component->noSplits()) {
      return "";
    }
    unsigned splitVariable =
      Saturation::Splitter::getLiteralFromName(component->splits()->sval()).var();
    if (!oldSplitVariables.contains(splitVariable)) {
      newComponents.push_back({definition, component});
    }
  }
  if (newComponents.empty()) {
    return "";
  }

  std::map<unsigned, AvatarSplitVariableTarget> instantiation;
  for (const auto& sourceComponent : avatarSplitComponents(original)) {
    if (sourceComponent.size() == 1 && sourceComponent[0]->ground()) {
      continue;
    }
    bool matched = false;
    for (const auto& targetComponent : newComponents) {
      if (sourceComponent.size() != targetComponent.clause->length()) {
        continue;
      }
      Substitution componentToOriginal;
      if (!MLVariant::isVariant(sourceComponent.data(), targetComponent.clause,
                                /* complementary */ false, &componentToOriginal)) {
        continue;
      }
      // MLVariant records component-variable -> original-variable.  Reverse
      // it to obtain the arguments supplied to the original clause after
      // rewriting by a component definition, as LeanChecker does.
      for (const auto& [targetVariable, sourceTerm] : iterTraits(componentToOriginal.items())) {
        if (!sourceTerm.isVar()) {
          return "";
        }
        unsigned sourceVariable = sourceTerm.var();
        auto [entry, inserted] = instantiation.emplace(
          sourceVariable, AvatarSplitVariableTarget{targetComponent.definition, targetVariable});
        if (!inserted &&
            (entry->second.definition != targetComponent.definition ||
             entry->second.variable != targetVariable)) {
          return "";
        }
      }
      matched = true;
      break;
    }
    if (!matched) {
      return "";
    }
  }
  if (instantiation.empty()) {
    return "";
  }

  std::ostringstream result;
  result << "post_rewrite_instantiation([";
  bool first = true;
  for (const auto& [sourceVariable, target] : instantiation) {
    if (!first) {
      result << ',';
    }
    first = false;
    // The bindings are ordered by the source variable, exactly as the
    // corresponding application of the first premise is built in
    // LeanChecker::avatarSplitClause.  `arg(fN,XM)` locates the
    // variable in the rewritten definition premise fN.
    result << "b(X" << sourceVariable << ",arg("
           << replayUnitId(target.definition) << ",X" << target.variable << "))";
  }
  result << "])";
  return result.str();
}


void InferenceStore::TPTPReplayProofPrinter::appendInferenceReplayAnnotations(
    Unit* unit, std::string& status,
    Shell::InferenceRecorder::InferenceReplayAnnotation& replay)
{
  auto append = [&status](const std::string& annotation) {
    if (annotation.empty()) { return; }
    if (!status.empty()) { status += ','; }
    status += annotation;
  };
  if (_replay) {
    replay = Shell::InferenceRecorder::inferenceReplayAnnotation(unit, *_replayer, true);
    append(formatTPTPReplayAnnotations(unit, replay));
    append(higherOrderReplayAnnotation(replay.information));
    append(tptpRectificationReplayAnnotation(unit, true));
    auto clausification = tptpClausificationReplayAnnotation(unit, true);
    append(clausification);
    if (!clausification.empty() && unit->inference().rule() == InferenceRule::CLAUSIFY) {
      const auto* extra = static_cast<const Shell::ClausificationExtra*>(env.proofExtra.find(unit));
      if (extra->newcnf) {
        if (!extra->newcnf->symbols.empty()) { append("status(esa)"); }
        for (const auto& [kind, name] : extra->newcnf->symbols) {
          if (_introducedCNFSymbols.insert(name).second) {
            append("new_symbols(" + kind + ",[" + name + "])");
          }
        }
        for (const auto& mapping : extra->newcnf->skolems) { append(mapping); }
      }
    }
    if (unit->inference().rule() == InferenceRule::FOOL_ELIMINATION && env.proofExtra.find(unit)) {
      const auto* fool = static_cast<const Shell::FOOLExtra*>(env.proofExtra.find(unit));
      std::string rewrites = "fool_rewrites([";
      for (unsigned i = 0; i < fool->rewrites.size(); ++i) {
        if (i) { rewrites += ','; }
        rewrites += fool->rewrites[i];
      }
      append(rewrites + "])");
    }
  }
  append(tptpDefinitionUnfoldingReplayAnnotation(unit));
  append(tptpAvatarSplitInstantiationReplayAnnotation(unit));
}

std::string InferenceStore::TPTPReplayProofPrinter::parentlessReplayAnnotation(
    Unit* unit, Shell::InferenceRecorder::InferenceReplayAnnotation& replay)
{
  if (!_replay) { return {}; }
  auto rule = unit->inference().rule();
  if ((rule == InferenceRule::FOOL_ITE_DEFINITION || rule == InferenceRule::FOOL_LET_DEFINITION ||
       rule == InferenceRule::FOOL_FORMULA_DEFINITION || rule == InferenceRule::FOOL_MATCH_DEFINITION) &&
      env.proofExtra.find(unit)) {
    const auto* fool = static_cast<const Shell::FOOLExtra*>(env.proofExtra.find(unit));
    std::string result = fool->definition;
    if (hasNewSymbols(unit)) { result = getNewSymbols("definition", unit) + ',' + result; }
    return result;
  }
  replay = Shell::InferenceRecorder::inferenceReplayAnnotation(unit, *_replayer, true);
  return higherOrderReplayAnnotation(replay.information);
}

/**
 * Format rule-specific evidence accepted by the common inference recorder.
 * A symbol introduced by Vampire (a Skolem witness, or the builtin choice and
 * difference operators) is announced by `new_symbols(kind,[name])` on the
 * first printed step that uses it; later steps reuse it.
 */
std::string InferenceStore::TPTPReplayProofPrinter::higherOrderReplayAnnotation(
    const Shell::InferenceRecorder::InferenceInformation* information)
{
  using Info = Shell::InferenceRecorder::InferenceInformation;
  if (!information) { return {}; }

  std::vector<std::string> parts;
  bool valid = true;
  auto symbolName = [](unsigned symbol) { return env.signature->getFunction(symbol)->name(); };
  auto introduce = [&](const char* kind, unsigned symbol) {
    if (_introducedSymbols.insert(symbol).second) {
      parts.push_back(std::string("new_symbols(") + kind + ",[" + symbolName(symbol) + "])");
    }
  };
  auto literalReference = [&](unsigned index) -> std::string {
    if (information->premises.size() == 1 && index < information->premises[0]->length()) {
      return "literal(" + replayUnitId(information->premises[0]) + "," + Int::toString(index) + ")";
    }
    valid = false;
    return {};
  };
  auto termList = [](const std::vector<TermList>& terms) {
    std::string result = "[";
    for (unsigned i = 0; i < terms.size(); ++i) {
      if (i) { result += ','; }
      result += tptpReplayTerm(terms[i]);
    }
    return result + "]";
  };

  if (const auto& witness = information->witness) {
    std::string literal = literalReference(witness->literalIndex);
    introduce("skolem", witness->symbol);
    parts.push_back(std::string(witness->kind == Info::WitnessKind::EXTENSIONALITY
                                  ? "extensionality_witness(" : "quantifier_witness(") +
                    literal + "," + symbolName(witness->symbol) + "," +
                    termList(witness->dependencies) + ")");
  }
  if (const auto& instance = information->quantifierInstance) {
    parts.push_back("quantifier_instance(" + literalReference(instance->literalIndex) + "," +
                    tptpReplayTerm(instance->term) + ")");
  }
  if (const auto& booleanCase = information->booleanCase) {
    parts.push_back("boolean_case(" + literalReference(booleanCase->literalIndex) + "," +
                    tptpReplayTerm(booleanCase->term) + "," +
                    (booleanCase->value ? "true" : "false") + ")");
  }
  if (const auto& axiom = information->axiom) {
    bool choice = axiom->kind == Info::AxiomKind::CHOICE;
    bool builtin = choice ? symbolName(axiom->symbol) == "vEPSILON"
                          : axiom->symbol == env.signature->getDiff();
    if (builtin) { introduce(choice ? "choice" : "extensionality", axiom->symbol); }
    parts.push_back(std::string(choice ? "choice_axiom(" : "extensionality_axiom(") +
                    symbolName(axiom->symbol) + "," + tptpReplayTerm(axiom->arguments[0]) + "," +
                    tptpReplayTerm(axiom->arguments[1]) + ")");
  }
  if (!valid) { return ""; }
  std::string result;
  for (const auto& part : parts) {
    if (!result.empty()) { result += ','; }
    result += part;
  }
  return result;
}

std::string InferenceStore::TPTPReplayProofPrinter::avatarConversionReplayAnnotation(Unit* origin) const
{
  if (env.options->proof() != Options::Proof::TSTP_AC) { return {}; }
  return tptpAvatarConversionReplayAnnotation(origin);
}

std::vector<Unit*> InferenceStore::TPTPReplayProofPrinter::avatarConversionReplayDefinitions(Unit* origin) const
{
  if (env.options->proof() != Options::Proof::TSTP_AC) { return {}; }
  return tptpAvatarConversionReplayDefinitions(origin);
}

void InferenceStore::TPTPReplayProofPrinter::addAdditionalPremises(Unit* unit, std::vector<Unit*>& todo)
{
  for (Unit* definition : avatarConversionReplayDefinitions(unit)) {
    todo.push_back(definition);
  }
}

InferenceStore::AbstractProofPrinter* InferenceStore::createTPTPReplayProofPrinter(std::ostream& out)
{
  return new TPTPReplayProofPrinter(out, this);
}

} // namespace Kernel

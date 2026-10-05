#include "InferenceRecorder.hpp"

#include "Indexing/DemodulationIndex.hpp"

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include <algorithm>
#include <cstddef>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Indexing;
namespace Shell {

InferenceRecorder *InferenceRecorder::_inst = nullptr;

InferenceRecorder *InferenceRecorder::instance()
{
  if (_inst != nullptr) {
    return _inst;
  }
  _inst = new InferenceRecorder();
  return _inst;
}

void InferenceRecorder::startRectifyRecording()
{
  _currentRectifyInference = std::make_unique<RectifyInferenceInformation>();
}

void InferenceRecorder::recordRectification(const std::vector<unsigned>& sourceBinders,
                                            const std::vector<unsigned>& targetBinders,
                                            const Substitution& renaming,
                                            const std::set<unsigned>& removed)
{
  if (!_currentRectifyInference) {
    return;
  }
  _currentRectifyInference->scopes.push_back({sourceBinders, targetBinders, renaming, removed});
}

void InferenceRecorder::endRectifyRecording(unsigned id)
{
  if (_currentRectifyInference) {
    _rectifyInferences[id] = std::move(_currentRectifyInference);
  }
}

const InferenceRecorder::RectifyInferenceInformation*
InferenceRecorder::getRectifyInferenceInformation(unsigned id) const
{
  auto entry = _rectifyInferences.find(id);
  return entry == _rectifyInferences.end() ? nullptr : entry->second.get();
}

void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *> premises,
                                              const RobSubstitution &recordedSubst)
{

  return populateSubstitutionsGen<RobSubstitution>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      [](const RobSubstitution &subst, const TermList &term, size_t bank) {
        return subst.apply(term, bank);
      });
}

void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *> premises,
                                              const ResultSubstitutionSP &recordedSubst)
{

  return populateSubstitutionsGen<ResultSubstitutionSP>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      [](ResultSubstitutionSP subst, const TermList &term, size_t bank) {
        return subst->applyTo(term, bank);
      });
}

TermList applyFunc(const SubstApplicator &subst, const TermList &term, size_t bank)
{
  return SubstHelper::apply(term, subst);
}
void InferenceRecorder::populateSubstitutions(std::vector<Substitution> &substMap,
                                              const std::unordered_map<unsigned int, unsigned int> &varMap,
                                              const std::vector<Clause *> premises,
                                              const SubstApplicator &recordedSubst)
{
  return populateSubstitutionsGen<SubstApplicator>(
      substMap,
      varMap,
      premises,
      recordedSubst,
      &applyFunc);
}

namespace {
unsigned literalPosition(Clause *clause, Literal *literal)
{
  for (unsigned i = 0; i < clause->length(); ++i) {
    if ((*clause)[i] == literal) {
      return i;
    }
  }
  ASS(false);
  return 0;
}
}

void InferenceRecorder::resolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst,
                                   Literal *queryLit, Literal *resultLit)
{
  ASS_EQ(premises.size(), 2);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst,
      InferenceInformation::LiteralPositionKind::RESOLVED,
      {{0, literalPosition(premises[0], queryLit)}, {1, literalPosition(premises[1], resultLit)}});
}

void InferenceRecorder::superposition(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst,
                                      bool eqIsResult, Literal *rewrittenLit)
{
  ASS_EQ(premises.size(), 2);
  recordGenericSubstitutionInference<ResultSubstitutionSP>(id, conclusion, premises, recordedSubst,
                                                                     [eqIsResult](ResultSubstitutionSP subst, const TermList &term, size_t bank) {
                                                                       if (bank == 1) {
                                                                         return subst->apply(term, eqIsResult);
                                                                       }
                                                                       else {
                                                                         return subst->apply(term, !eqIsResult);
                                                                       }
                                                                     },
                                                                     InferenceInformation::LiteralPositionKind::REWRITTEN,
                                                                     {{0, literalPosition(premises[0], rewrittenLit)}});
}

void InferenceRecorder::factoring(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst,
                                  Literal *removedLit)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst,
      InferenceInformation::LiteralPositionKind::REMOVED,
      {{0, literalPosition(premises[0], removedLit)}});
}

void InferenceRecorder::equalityFactoring(unsigned id, Clause *conclusion, const std::vector<Clause *> &premises,
                                          const RobSubstitution &recordedSubst)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst)
{
  ASS_EQ(premises.size(), 1);
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolutionDeletion(unsigned int id, Clause *conclusion, Clause *premise, EqResWithDeletion *appl)
{
  recordGenericSubstitutionInference<EqResWithDeletion*>(id, conclusion, {premise}, appl,
    [](EqResWithDeletion *subst, const TermList &term, size_t bank) {
    return subst->apply(term.var());
  });
}

void InferenceRecorder::forwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator *appl, const DemodulatorData *data,
                                            Literal *rewrittenLit)
{
  std::unordered_map<unsigned int, unsigned int> varMap;
  if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
    std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
    info->conclusion = conclusion;
    info->premises = premises;
    info->literalPositionKind = InferenceInformation::LiteralPositionKind::REWRITTEN;
    info->literalPositions = {{0, literalPosition(premises[0], rewrittenLit)}};
    // The matcher bindings below are for the indexed demodulator (the
    // second parent), not for the clause being rewritten.
    info->substitutionForBanksSub.resize(premises.size());

    // The replayed conclusion can be an alpha-variant of the original proof
    // step.  Values produced by `appl` use the replayed names, so translate
    // them back to the names of the printed conclusion.
    Substitution conclusionRenaming;
    for (auto [var, mappedVar] : varMap) {
      conclusionRenaming.bind(var, TermList::var(mappedVar));
    }
    // DemodulatorData stores the left-hand side and right-hand side after
    // normalizing variables in the left-hand side. Recreate that normalization
    // from the source equality, rather than trying to recover it from the RHS:
    // the RHS need not contain all variables of the demodulator.
    Literal* demodulator = data->clause->literals()[0];
    auto [left, right] = demodulator->eqArgs();
    TermList sort = demodulator->eqArgSort();
    Renaming normalization;
    auto matchesIndexedOrientation = [&](TermList lhs, TermList rhs) {
      normalization.reset();
      normalization.normalizeVariables(TypedTermList(lhs, sort));
      return normalization.apply(lhs) == data->term.untyped()
          && normalization.apply(rhs) == data->rhs
          && normalization.apply(sort) == data->term.sort();
    };
    bool foundOrientation = matchesIndexedOrientation(left, right)
      || matchesIndexedOrientation(right, left);
    if (!foundOrientation) {
      return;
    }

    // we create a custom substitution to apply the substitution only to variables coming from the demodulator
    // otherwise the substitution we get faults
    auto iter = data->clause->getVariableIterator();
    while (iter.hasNext()) {
      auto var = iter.next();
      TermList mappedVar = normalization.apply(TermList::var(var));
      ASS(mappedVar.isVar());
      TermList value = SubstHelper::apply(appl->apply(mappedVar.var()), conclusionRenaming);
      info->substitutionForBanksSub[1].bind(var, value);
    }

    _inferences[id] = std::move(info);
    _lastInferenceId = id;
    _hasLastInference = true;
  }
}

void InferenceRecorder::backwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator& appl)
{
  recordGenericSubstitutionToOneBank<SubstApplicator>(id, conclusion, premises, appl, 
	[](const SubstApplicator &subst, const TermList &term, size_t bank) {
      return subst.apply(term.var());
    }
  );
}

bool InferenceRecorder::isSameAsProofStep(Clause *clause, Clause *goal, std::unordered_map<unsigned int, unsigned int> &outVarMap)
{
  outVarMap.clear();

  if (clause->length() != goal->length()) {
    return false;
  }

  std::vector<bool> matchedGoalLiterals(goal->length(), false);
  for (unsigned i = 0; i < clause->length(); ++i) {
    bool found = false;
    for (unsigned j = 0; j < goal->length(); ++j) {
      if (!matchedGoalLiterals[j] && (*clause)[i] == (*goal)[j]) {
        matchedGoalLiterals[j] = true;
        found = true;
        break;
      }
    }
    if (!found) {
      break;
    }
  }
  if (std::all_of(matchedGoalLiterals.begin(), matchedGoalLiterals.end(), [](bool matched) { return matched; })) {
    return true;
  }

  if (clause->length() == 0) {
    return true;
  }

  //TODO do some simpler preprocessing here to save on runtime,
  //For now it works
  Clause *c = Clause::fromClause(clause);
  Clause *g = Clause::fromClause(goal);

  Inferences::DuplicateLiteralRemovalISE dlr;
  c = dlr.simplify(c);
  auto simpGoal = dlr.simplify(Clause::fromClause(g));

  if (c->length() != simpGoal->length()) {
    return false;
  }
  if (!MLVariant::isVariant(c, simpGoal)) {
    return false;
  }

  auto variables = [](Clause* cl) {
    std::unordered_set<unsigned> result;
    auto it = cl->getVariableIterator();
    while (it.hasNext()) {
      result.insert(it.next());
    }
    return result;
  };
  if (variables(c).size() != variables(simpGoal).size()) {
    return false;
  }

  static std::vector<LiteralList *> alts;

  alts.clear();
  alts.resize(c->length(), LiteralList::empty());

  //This can probably be optimized with an index
  for (unsigned bi = 0; bi < c->length(); ++bi) {
    Literal *baseLit = (*c)[bi];
    for (unsigned ii = 0; ii < simpGoal->length(); ++ii) {
      Literal *instLit = (*simpGoal)[ii];
      if (MatchingUtils::match(baseLit, instLit, false)) {
        LiteralList::push(instLit, alts[bi]);
      }
    }
    if (LiteralList::isEmpty(alts[bi])) {
      return false;
    }
  }

  MLMatcher matcher;
  // Both clauses have the same length and have already been checked as variants.
  // Preserve the literal-to-literal correspondence while extracting the variable
  // renaming; set matching could reuse one goal literal for multiple replayed ones.
  matcher.init(c, simpGoal, alts.data(), /*multiset=*/true);
  while (matcher.nextMatch()) {
    std::unordered_map<unsigned int, TermList> varToTermMap;
    matcher.getBindings(varToTermMap);
    bool isVariableRenaming = true;
    for (auto [var, term] : varToTermMap) {
      if(!term.isVar()){
        isVariableRenaming = false;
        break;
      }
    }
    if (!isVariableRenaming) {
      continue;
    }
    std::unordered_set<unsigned int> image;
    for (auto [var, term] : varToTermMap) {
      if (!image.insert(term.var()).second) {
        isVariableRenaming = false;
        break;
      }
    }
    if (!isVariableRenaming) {
      continue;
    }
    for (auto [var, term] : varToTermMap) {
      outVarMap[var] = term.var();
    }
    return true;
  }
  return false;
}

InferenceRecorder::InferenceRecorder()
{
}

InferenceRecorder::~InferenceRecorder()
{
}
} // namespace Shell

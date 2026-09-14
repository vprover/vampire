#include "InferenceRecorder.hpp"

#include "Indexing/DemodulationIndex.hpp"

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Shell/EqResWithDeletion.hpp"
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

void InferenceRecorder::equalityResolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst)
{
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolutionDeletion(unsigned int id, Clause *conclusion, EqResWithDeletion *appl)
{
  recordGenericSubstitutionInference<EqResWithDeletion*>(id, conclusion, {conclusion}, appl,
    [](EqResWithDeletion *subst, const TermList &term, size_t bank) {
    return subst->apply(term.var());
  });
}

bool hasVarSubstAndCompute(TermList &expectedTerm, TermList &haveTerm, Substitution &outVariableSwitch)
{
  bool haveProperSubst = false;
  if(expectedTerm.isVar()) {
    if (haveTerm.isVar()) {
      outVariableSwitch.bind(expectedTerm.var(), haveTerm);
      haveProperSubst = true;
    }
    return haveProperSubst;
  }
  
  if(haveTerm.isTerm() && expectedTerm.isTerm() && haveTerm.term()->arity()==0 && expectedTerm.term()->arity()==0) {
    return expectedTerm.term() == haveTerm.term();
  }

  if (MatchingUtils::matchTerms(expectedTerm, haveTerm)) {
    haveProperSubst = true;
    MatchingUtils::matchArgs(haveTerm.term(), expectedTerm.term(), outVariableSwitch);
    auto items = outVariableSwitch.items();
    while (items.hasNext()) {
      auto [var, termList] = items.next();
      if (!termList.isVar()) {
        haveProperSubst = false;
        break;
      }
    }
  }
  return haveProperSubst;
}

void InferenceRecorder::forwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator *appl, const DemodulatorData *data,
                                            TermList rhsS)
{
  std::unordered_map<unsigned int, unsigned int> varMap;
  if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
    std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
    info->conclusion = conclusion;
    info->premises = premises;
    info->substitutionForBanksSub.resize(1);
    Substitution varPermut;
    TermList rhsTerm = data->rhs;

    // It seems that qr.data->clause and qr.data->rhs can have different variable namings
    // To handle this we check if the rhs is on either side of the equality and then create a
    // variable permuation substitution to map the variables to the ones in the clause
    bool haveProperSubst = false;
    if (rhsTerm.isTerm()) {
      haveProperSubst = hasVarSubstAndCompute(rhsTerm, *(data->clause->literals()[0]->nthArgument(0)), varPermut);
      // check if this is the same as rhsS
      if (haveProperSubst) {
        TermList mappedRhs = SubstHelper::apply(*(data->clause->literals()[0]->nthArgument(0)), varPermut);
        // now apply real subst and check if it was actually the same
        mappedRhs = SubstHelper::apply(mappedRhs, *appl);
        if (!MatchingUtils::matchTerms(rhsS, mappedRhs)) {
          haveProperSubst = false;
        }
      }
      if (!haveProperSubst) {
		    varPermut.reset();
        haveProperSubst = hasVarSubstAndCompute(rhsTerm, *(data->clause->literals()[0]->nthArgument(1)), varPermut);
		    // we don't need to check rhsS again, because now it must be the other side
      }
    } else if (rhsTerm.isVar()) {
      if (data->clause->literals()[0]->nthArgument(0)->isVar()) {
        varPermut.bind(data->clause->literals()[0]->nthArgument(0)->var(),
                            TermList::var(rhsTerm.var()));
        haveProperSubst = true;
      }
      else if (data->clause->literals()[0]->nthArgument(1)->isVar()) {
        varPermut.bind(data->clause->literals()[0]->nthArgument(1)->var(),
                            TermList::var(rhsTerm.var()));
        haveProperSubst = true;
      }
      else {
        haveProperSubst = false;
      }
    }
    ASS(haveProperSubst)

    // we create a custom substitution to apply the substitution only to variables coming from the demodulator
    // otherwise the substitution we get faults
    info->substitutionForBanksSub.resize(1);
    auto iter = data->clause->getVariableIterator();
    while (iter.hasNext()) {
      auto var = iter.next();
      TermList mappedVar = varPermut.apply(var);
      ASS(mappedVar.isVar());
      info->substitutionForBanksSub[0].bind(var, appl->apply(mappedVar.var()));
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

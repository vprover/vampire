#include "InferenceRecorder.hpp"

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include <cstddef>
#include <unordered_map>
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

void InferenceRecorder::resolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst)
{
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::superposition(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const ResultSubstitutionSP &recordedSubst, bool eqIsResult)
{
  recordGenericSubstitutionInference<ResultSubstitutionSP>(id, conclusion, premises, recordedSubst,
                                                                     [eqIsResult](ResultSubstitutionSP subst, const TermList &term, size_t bank) {
                                                                       if (bank == 1) {
                                                                         return subst->apply(term, eqIsResult);
                                                                       }
                                                                       else {
                                                                         return subst->apply(term, !eqIsResult);
                                                                       }
                                                                     });
}

void InferenceRecorder::factoring(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst)
{
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolution(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const RobSubstitution &recordedSubst)
{
  recordGenericSubstitutionInference(id, conclusion, premises, recordedSubst);
}

void InferenceRecorder::equalityResolutionDeletion(unsigned int id, Clause *conclusion, Clause *premise, EqResWithDeletion *appl)
{
  recordGenericSubstitutionInference<EqResWithDeletion*>(id, conclusion, {premise}, appl,
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
  if (isSameAsProofStep(conclusion, _currentGoal, premises, varMap)) {
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
    DHMap<unsigned int, TermList> sorts;
    auto dataTerm = data->term;
    if (dataTerm.isVar()) {
      if (data->rhs.isTerm()) {
        ALWAYS(sorts.insert(dataTerm.var(), SortHelper::getResultSort(data->rhs.term())));
      } else {
        ALWAYS(sorts.insert(dataTerm.var(), data->clause->literals()[0]->twoVarEqSort()));
      }
    } else {
      auto term = dataTerm.term();
      SortHelper::collectVariableSorts(term,sorts);
    }

    for (const auto& [var, sort] : iterTraits(sorts.items())) {
      auto newTerm = SubstHelper::apply((*appl)(var), varPermut);
      info->substitutionForBanksSub[0].bind(varPermut.apply(var).var(), newTerm);
    }

    _inferences[id] = std::move(info);
    _lastInferenceId = id;
  }
}

void InferenceRecorder::backwardDemodulation(unsigned int id, Clause *conclusion, const std::vector<Clause *> &premises, const SubstApplicator& appl)
{
  recordGenericSubstitutionToOneBank<SubstApplicator>(id, conclusion, premises, appl, 
	[](const SubstApplicator &subst, const TermList &term, size_t bank) {
      return subst(term.var());
    }
  );
}

bool InferenceRecorder::isSameAsProofStep(Clause *clause, Clause *goal, const std::vector<Clause *> &premises, std::unordered_map<unsigned int, unsigned int> &outVarMap)
{
  auto parents = goal->getParents();
  unsigned parentCounter = 0;
  if(parents.hasNext()) {
    auto parent = parents.next();
    if(parent->number() != premises[parentCounter]->number()){
      return false;
    }
    parentCounter++;
  }

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
  matcher.init(c, simpGoal, alts.data());
  while (matcher.nextMatch()) {
    std::unordered_map<unsigned int, TermList> varToTermMap;
    bool found = true;
    matcher.getBindings(varToTermMap);
    for (auto [var, term] : varToTermMap) {
      if(!term.isVar()){
        outVarMap.clear();
        found = false;
        continue;
      }
      outVarMap[var] = term.var();
    }
    if (found) {
      return true;
    }
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
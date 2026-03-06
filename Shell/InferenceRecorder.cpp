#include "InferenceRecorder.hpp"

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/MLMatcher.hpp"

#include "Kernel/MLVariant.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Metaiterators.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/Rectify.hpp"
#include <cstddef>
#include <unordered_map>
#include <vector>
#include <set>

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
                                            TermList rhsS, TypedTermList trm)
{
  std::unordered_map<unsigned int, unsigned int> varMap;
  if (isSameAsProofStep(conclusion, _currentGoal, premises, varMap)) {
    std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
    Substitution variableMap = Substitution();
    for (auto [var, mappedVar] : varMap) {
      variableMap.bind(var, TermList::var(mappedVar));
    }
    info->conclusion = conclusion;
    info->premises = premises;
    info->substitutionForBanksSub.resize(1);
    Substitution variableSwapForClauseR;

    // qr.data->clause and qr.data->rhs have different variable namings since the demoldulation code normalizes the variables
    // To handle this we check if the rhs is on either side of the equality and then create a
    // variable permuation substitution to map the variables to the ones in the clause
    auto x = Literal::createEquality(true, data->term, data->rhs, data->term.sort());
    MLVariant::isVariant(&x, data->clause, false, &variableSwapForClauseR);

    Substitution variableSwapForClause;
    for(auto [var, term] : iterTraits(variableSwapForClauseR.items())){
      variableSwapForClause.bind(term.var(), TermList::var(var));
    }
  
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

    
    Substitution substFixingNormalization;
    auto foundTerm = SubstHelper::apply(data->term, *appl);
    MatchingUtils::matchTerms(foundTerm, trm, substFixingNormalization);
    //std::cout << data->rhs << std::endl;
    //std::cout << data->term << std::endl;
    //std::cout << premises[0]->toString() << std::endl;
    //std::cout << premises[1]->toString() << std::endl;
    //std::cout << data->clause->toString() << std::endl;
    //std::cout << rhsS << std::endl;
    //std::cout << data->clause->toString() << std::endl;
    //std::cout << trm << std::endl;
    //std::cout << foundTerm << std::endl;
    //std::cout << substFixingNormalization << std::endl;
    //std::cout << variableSwapForClause << std::endl;
    //std::cout << variableMap << std::endl;
    for (const auto& [var, sort] : iterTraits(sorts.items())) {
      auto newTerm = (*appl)(var);
      //std::cout << var << ": " << newTerm << std::endl;
      info->substitutionForBanksSub[0].bind(variableSwapForClause.apply(var).var(), 
        SubstHelper::apply(newTerm, substFixingNormalization));
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

void InferenceRecorder::rectify(Formula* f, VList* vs, Substitution renaming, std::set<unsigned> unusedVars)
{
  
  std::unique_ptr<RectifyInferenceExtra> extra = std::make_unique<RectifyInferenceExtra>();

  Kernel::Substitution substVariablesInQuantifier;
  auto quantifierIter = f->vars()->iter();
  auto argIter = vs->iter();
  std::vector<unsigned> originalVars;
  std::vector<unsigned> rectifiedVars;
  while(quantifierIter.hasNext()) {
    auto v = quantifierIter.next();
    if(unusedVars.find(v) == unusedVars.end()){
      originalVars.push_back(v);
    }
  }
  while(argIter.hasNext()) {
    rectifiedVars.push_back(argIter.next());
  }
  //ASS(originalVars.size() == rectifiedVars.size());
  std::sort(originalVars.begin(), originalVars.end());
  std::sort(rectifiedVars.begin(), rectifiedVars.end());
  
  for(size_t i = 0; i < originalVars.size(); i++) {
    substVariablesInQuantifier.bind(rectifiedVars[i], TermList::var(originalVars[i]));
  }
  //std::cout << substVariablesInFormula << std::endl;
  //std::cout << substVariablesInQuantifier << std::endl;
  Substitution combinedSubst;
  for(auto v : iterTraits(f->vars()->iter())) {
    combinedSubst.bind(v, substVariablesInQuantifier.apply(renaming.apply(v).var()));
  }
  //std::cout << "Combined" << combinedSubst << std::endl;
  static_cast<RectifyInferenceExtra*>(_currentRecording.get())->
    renamings.emplace_back(f, combinedSubst);

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
  
  
  //if(!isVariant){
  //  return false;
  //}
  //for (auto [var, term] : iterTraits(subst.items())) {
  //  if (!term.isVar()) {
  //    return false;
  //  }
  //  outVarMap[var] = term.var();
  //}
  //return isVariant;
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
    if(!found){
      continue;
    }
    std::set<unsigned> inputs;
    std::set<unsigned> outputs;
    //Check if we have a permutation
    for (auto [var, term] : varToTermMap) {
      inputs.insert(var);
      outputs.insert(term.var());
    }
    if (inputs.size() != outputs.size()) {
      found = false;
    }
    if(outputs.size() != _currentGoal->varCnt()){
      found = false;
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
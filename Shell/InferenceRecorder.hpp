#ifndef __INFERENCE_RECORDER__
#define __INFERENCE_RECORDER__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include <memory>
#include <unordered_map>
#include <type_traits>
#include <vector>
#include <set>

/** A class which can record information about inference steps. 
    It is intended to be used in conjunction with ProofReplay.
    
    How to record a new inference step:
    (0) If the inference step needs more detail than a few substitutions, create a new class inheriting from GenericInferenceInformation to hold the necessary information.
    1) Add a new method to the class with the appropriate parameters for the inference step
    2) Write a hook (that is triggered when the environment is configured for recording) for the inference step in the relevant inference code. (Search for similar code e.g. in Resolution code)
    3) In the hook, the new method is called with the parameters that suffice to get necessary information about the performed inference.

  */

namespace Shell {
class InferenceRecorder {
public:
  class GenericInferenceInformation {
    public:
      /** Base type for information captured about a recorded inference step. */
      virtual ~GenericInferenceInformation() = default;
  };

  class InferenceInformation : public GenericInferenceInformation {
  public:
    Kernel::Clause *conclusion;
    std::vector<Kernel::Clause *> premises;
    std::vector<Kernel::Substitution> substitutionForBanksSub;
    Kernel::Substitution* substitutionForConclusionVars;
  };

  class RectifyInferenceInformation : public GenericInferenceInformation {
    public:
      //New formula, original formula, and the renaming from the new formula to the original formula.
      std::vector<std::pair<Kernel::Formula*, std::pair<Kernel::Formula*, Kernel::Substitution>>> renamings;
  };

  /** Returns the lazily initialized recorder singleton. */
  static InferenceRecorder *instance();

  /** Records a resolution inference when it matches the current proof step. */
  void resolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::ResultSubstitutionSP &recordedSubst);
  void superposition(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::ResultSubstitutionSP &recordedSubst, bool eqIsResult);
  void factoring(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  void equalityResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  void equalityResolutionDeletion(unsigned int id, Clause *conclusion, Clause *premise, EqResWithDeletion *appl);
  void equalityFactoring(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  void forwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator *appl, const Indexing::DemodulatorData *data,
                           TermList rhsS, TypedTermList trm);
  void backwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator &appl);
  void rectify(Formula* f, Formula* newFormula, VSList* vs, Substitution renaming, std::set<unsigned> unusedVars);

  /** Starts capturing rectification-specific inference data. */
  void startRectifyRecording(){
    _currentRecording = std::make_unique<RectifyInferenceInformation>();
  }

  /** Stores the most recently recorded rectification metadata under the given id. */
  void endRectifyRecording(unsigned int id){
    _lastInferenceId = id;
    _inferences[id] = std::move(_currentRecording);
  }

  //void unitResultingResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Unit *> &premises, const std::vector<Indexing::ResultSubstitutionSP> &substitutions);

  /** Sets the clause currently considered the proof goal. */
  void setCurrentGoal(Kernel::Clause *goal)
  {
    _currentGoal = goal;
    _lastInferenceId = 0;
  }

  bool hasRecordedInference() const
  {
    return _lastInferenceId != 0;
  }

  /** Returns the last recorded concrete inference payload, if available. */
  const InferenceInformation *getLastRecordedInferenceInformation() const
  {
    auto it = _inferences.find(_lastInferenceId);
    if (it != _inferences.end())
      return static_cast<const InferenceInformation *>(it->second.get());
    return nullptr;
  }

  /** Returns the last recorded payload as a generic inference record, if available. */
  const GenericInferenceInformation *getGenericLastInferenceInformation() const
  {
    auto it = _inferences.find(_lastInferenceId);
    if (it != _inferences.end())
      return it->second.get();
    return nullptr;
  }

  virtual ~InferenceRecorder();

  // non-copyable, non-movable
  InferenceRecorder(const InferenceRecorder &) = delete;
  InferenceRecorder &operator=(const InferenceRecorder &) = delete;
  InferenceRecorder(InferenceRecorder &&) = delete;
  InferenceRecorder &operator=(InferenceRecorder &&) = delete;
  
private:
  /** Constructs the singleton-owned recorder object. */
  InferenceRecorder();

  static InferenceRecorder *_inst;

  /** Builds a substitution that remaps variables according to the recorded proof step. */
  Substitution buildVariableSubstitutionFromMap(const std::unordered_map<unsigned int, unsigned int> &varMap);

  /** Checks whether the replayed clause matches the current proof step. */
  bool isSameAsProofStep(Kernel::Clause *c, Kernel::Clause *goal, const std::vector<Kernel::Clause *> &premises, std::unordered_map<unsigned int, unsigned int> &outVarMap);

  template <typename T>
  /** Populates the substitution in one bank   */
  void populateSubstitutionsMergeOneBank(std::vector<Kernel::Substitution> &substMap,
                                     const std::unordered_map<unsigned int, unsigned int> &varMap,
                                     const std::vector<Clause *> &premises,
                                     const T &recordedSubst,
                                     std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal.
    Substitution variableSubst = buildVariableSubstitutionFromMap(varMap);

    substMap.resize(1);
    std::vector<unsigned> vars;
    for (size_t bank = 0; bank < premises.size(); bank++) {
      auto iter = premises[bank]->getVariableIterator();
      while (iter.hasNext()) {
        vars.push_back(variableSubst.apply(iter.next()).var());
      }
    }
    for (unsigned v : vars) {
      TermList x = applyFunc(recordedSubst, TermList::var(v), 0);
      substMap[0].bind(v,SubstHelper::apply(x,variableSubst));
    }
  }

  template <typename T, typename ApplyFunc>
  /** Populates per-bank substitutions using the supplied apply function. */
  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> &premises,
                             const T &recordedSubst,
                             ApplyFunc applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal.
    Substitution variableSubst = buildVariableSubstitutionFromMap(varMap);
    substMap.resize(premises.size());

    for (size_t bank = 0; bank < premises.size(); bank++) {
      auto iter = premises[bank]->getVariableIterator();
      std::vector<unsigned> vars;
      while (iter.hasNext()) {
        unsigned int var = variableSubst.apply(iter.next()).var();
        vars.push_back(var);
      }
      for (unsigned v : iterTraits( premises[bank]->getVariableIterator())) {
        TermList x = applyFunc(recordedSubst, TermList::var(v), bank);
        substMap[bank].bind(v, SubstHelper::apply(x, variableSubst));
      }
    }
  }

  template <typename PopulateFn>
  /** Stores inference information only when the replayed step matches the goal. */
  void recordInferenceIfMatchingStep(unsigned int id,
                                     Kernel::Clause *conclusion,
                                     const std::vector<Kernel::Clause *> &premises,
                                     PopulateFn populateFn)
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (!isSameAsProofStep(conclusion, _currentGoal, premises, varMap)) {
      return;
    }
    if(hasRecordedInference()){
      //check if varMap is not the identity mapping, if so we can skip this inference
      bool identity = true;
      for(auto [var, mappedVar] : varMap){
        if(var != mappedVar){
          identity = false;
          break;
        }
      }
      if(!identity){
        return;
      }
    }
    std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
    info->conclusion = conclusion;
    info->premises = premises;
    populateFn(*info, varMap);
    Substitution* variableSubst = new Substitution(buildVariableSubstitutionFromMap(varMap));
    info->substitutionForConclusionVars = variableSubst;
    _inferences[id] = std::move(info);
    _lastInferenceId = id;
  }

  template <typename T>
  /** Records a substitution-based inference with a custom apply function. */
  void recordGenericSubstitutionInference(unsigned int id,
                                          Kernel::Clause *conclusion,
                                          const std::vector<Kernel::Clause *> &premises,
                                          const T &recordedSubst,
                                          std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    recordInferenceIfMatchingStep(id, conclusion, premises, [&](InferenceInformation &info, const std::unordered_map<unsigned int, unsigned int> &varMap) {
      populateSubstitutions<T, decltype(applyFunc)>(info.substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
    });
  }

  template <typename T>
  /** Resolves the recorded substitution function for the supported substitution type. */
  TermList applySuitableSubstitutionFunction(const T &subst, const TermList &term, size_t bank){
    if constexpr (std::is_same_v<T, RobSubstitution>) {
      return subst.apply(term, bank);
    }
    else if constexpr (std::is_same_v<T, Indexing::ResultSubstitutionSP>) {
      return subst->applyTo(term, bank);
    }
    else {
      return SubstHelper::apply(term, subst);
    }
  }

  template <typename T>
  /** Records a substitution-based inference using the default apply function for the type. */
  void recordGenericSubstitutionInference(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst)
  {
    recordInferenceIfMatchingStep(id, conclusion, premises, [&](InferenceInformation &info, const std::unordered_map<unsigned int, unsigned int> &varMap) {
      populateSubstitutions(info.substitutionForBanksSub, varMap, premises, recordedSubst, 
        [this](const T &subst, const TermList &term, size_t bank) {
          return applySuitableSubstitutionFunction(subst, term, bank);
        }
      );
    });
  }

  template <typename T>
  /** Records a substitution-based inference where all variables are collapsed into one bank. */
  void recordGenericSubstitutionToOneBank(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst, std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    recordInferenceIfMatchingStep(id, conclusion, premises, [&](InferenceInformation &info, const std::unordered_map<unsigned int, unsigned int> &varMap) {
      populateSubstitutionsMergeOneBank<T>(info.substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
    });
  }

  Kernel::Clause *_currentGoal = nullptr;
  std::unordered_map<unsigned int, std::unique_ptr<GenericInferenceInformation>> _inferences;
  unsigned int _lastInferenceId = 0;
  std::unique_ptr<GenericInferenceInformation> _currentRecording = nullptr;
};
} // namespace Shell

#endif // __INFERENCE_RECORDER__
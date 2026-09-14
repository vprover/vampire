#ifndef __INFERENCE_RECORDER__
#define __INFERENCE_RECORDER__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include <memory>
#include <unordered_map>
#include <utility>
#include <vector>

namespace Indexing { struct DemodulatorData; }

namespace Shell {
class InferenceRecorder {
public:
  class InferenceInformation {
  public:
    enum class LiteralPositionKind {
      NONE,
      REWRITTEN,
      RESOLVED,
      REMOVED
    };

    struct LiteralPosition {
      unsigned premiseIndex;
      unsigned literalIndex;
    };

    Kernel::Clause *conclusion;
    std::vector<Kernel::Clause *> premises;
    std::vector<Kernel::Substitution> substitutionForBanksSub;
    LiteralPositionKind literalPositionKind = LiteralPositionKind::NONE;
    std::vector<LiteralPosition> literalPositions;
  };

  // Returns the singleton instance (lazily initialized, thread-safe)
  static InferenceRecorder *instance();
  // Optional: destroy the singleton (if you need controlled teardown)
  // static void destroyInstance();

  void resolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::ResultSubstitutionSP &recordedSubst,
                  Kernel::Literal *queryLit, Kernel::Literal *resultLit);

  void superposition(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::ResultSubstitutionSP &recordedSubst,
                     bool eqIsResult, Kernel::Literal *rewrittenLit);

  void factoring(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst,
                 Kernel::Literal *removedLit);

  void equalityResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  
  void equalityResolutionDeletion(unsigned int id, Clause *conclusion, EqResWithDeletion *appl);

  void forwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator *appl, const Indexing::DemodulatorData *data,
                           TermList rhsS);

  void backwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator &appl);

  //void unitResultingResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Unit *> &premises, const std::vector<Indexing::ResultSubstitutionSP> &substitutions);

  void setCurrentGoal(Kernel::Clause *goal)
  {
    _currentGoal = goal;
    _hasLastInference = false;
  }

  const InferenceInformation *getLastRecordedInferenceInformation() const
  {
    if (!_hasLastInference) {
      return nullptr;
    }
    auto it = _inferences.find(_lastInferenceId);
    if (it != _inferences.end())
      return it->second.get();
    return nullptr;
  }

  ~InferenceRecorder();

  // non-copyable, non-movable
  InferenceRecorder(const InferenceRecorder &) = delete;
  InferenceRecorder &operator=(const InferenceRecorder &) = delete;
  InferenceRecorder(InferenceRecorder &&) = delete;
  InferenceRecorder &operator=(InferenceRecorder &&) = delete;
  
private:
  InferenceRecorder();

  static InferenceRecorder *_inst;

  bool isSameAsProofStep(Kernel::Clause *c, Kernel::Clause *goal, std::unordered_map<unsigned int, unsigned int> &outVarMap);

  template <typename T>
  void populateSubstitutionsGen(std::vector<Kernel::Substitution> &substMap,
                                const std::unordered_map<unsigned int, unsigned int> &varMap,
                                const std::vector<Clause *> premises,
                                const T &recordedSubst,
                                std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal
    Substitution variableSubst = Substitution();
    for (auto [var, mappedVar] : varMap) {
      variableSubst.bind(var, TermList::var(mappedVar));
    }

    substMap.resize(premises.size());
    for (size_t bank = 0; bank < premises.size(); bank++) {
      auto iter = premises[bank]->getVariableIterator();
      while (iter.hasNext()) {
        unsigned int var = iter.next();
        TermList x = applyFunc(recordedSubst, TermList::var(var), bank);
        TermList mapped = SubstHelper::apply(x, variableSubst);
        if (mapped != TermList::var(var)) {
          substMap[bank].bind(var, mapped);
        }
      }
    }
  }

  template <typename T>
  void populateSubstitutionsMergeOneBank(std::vector<Kernel::Substitution> &substMap,
                                     const std::unordered_map<unsigned int, unsigned int> &varMap,
                                     const std::vector<Clause *> premises,
                                     const T &recordedSubst,
                                     std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal
    Substitution variableSubst = Substitution();
    for (auto [var, mappedVar] : varMap) {
      variableSubst.bind(var, TermList::var(mappedVar));
    }

    substMap.resize(1);
    for (size_t bank = 0; bank < premises.size(); bank++) {
      auto iter = premises[bank]->getVariableIterator();
      while (iter.hasNext()) {
        unsigned int var = iter.next();
        TermList x = applyFunc(recordedSubst, TermList::var(var), 0);
        TermList mapped = SubstHelper::apply(x, variableSubst);
        if (mapped != TermList::var(var)) {
          substMap[0].bind(var, mapped);
        }
      }
    }
  }

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const RobSubstitution &recordedSubst);

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const Indexing::ResultSubstitutionSP &recordedSubst);

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const SubstApplicator &recordedSubst);

  template <typename T>
  void recordGenericSubstitutionInference(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst, std::function<TermList(const T &, const TermList &, size_t)> applyFunc,
                                          InferenceInformation::LiteralPositionKind literalPositionKind = InferenceInformation::LiteralPositionKind::NONE,
                                          std::vector<InferenceInformation::LiteralPosition> literalPositions = {})
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      populateSubstitutionsGen<T>(info->substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
      info->literalPositionKind = literalPositionKind;
      info->literalPositions = std::move(literalPositions);
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
      _hasLastInference = true;
    }
    // Do nothing if not same as proof step
  };

  template <typename T>
  void recordGenericSubstitutionInference(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst,
                                          InferenceInformation::LiteralPositionKind literalPositionKind = InferenceInformation::LiteralPositionKind::NONE,
                                          std::vector<InferenceInformation::LiteralPosition> literalPositions = {})
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
      // std::cout << conclusion->toNiceString() << std::endl;
      // std::cout << _currentGoal->toNiceString() << std::endl;
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      populateSubstitutions(info->substitutionForBanksSub, varMap, premises, recordedSubst);
      info->literalPositionKind = literalPositionKind;
      info->literalPositions = std::move(literalPositions);
      // for(auto& subst : info->substitutionForBanksSub){
      //	std::cout << subst << std::endl;
      // }
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
      _hasLastInference = true;
    }
    // Do nothing if not same as proof step
  };

  template <typename T>
  void recordGenericSubstitutionToOneBank(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst, std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, varMap)) {
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      populateSubstitutionsMergeOneBank<T>(info->substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
      _hasLastInference = true;
    }
    // Do nothing if not same as proof step
  };

  

  Kernel::Clause *_currentGoal = nullptr;
  std::unordered_map<unsigned int, std::unique_ptr<InferenceInformation>> _inferences;
  unsigned int _lastInferenceId = 0;
  bool _hasLastInference = false;
};
} // namespace Shell

#endif // __INFERENCE_RECORDER__

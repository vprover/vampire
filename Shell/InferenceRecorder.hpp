/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __INFERENCE_RECORDER__
#define __INFERENCE_RECORDER__

#include "Forwards.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Renaming.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Lib/ScopedLet.hpp"
#include <initializer_list>
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>

namespace Indexing { struct DemodulatorData; }

namespace Shell {
class InferenceRecorder {
public:
  /** One non-null applicator per parent, in parent order. Used only during recording. */
  using Substitutions = std::initializer_list<const Kernel::SubstApplicator*>;

  /** Map original demodulator variables through the index normalization. */
  struct DemodulationApplicator : Kernel::SubstApplicator {
    /** subst uses normalized index variables. Check valid() before applying or reading lhs/rhs. */
    DemodulationApplicator(const Kernel::SubstApplicator& subst,
                          const Indexing::DemodulatorData& data);
    bool valid() const { return _valid; }
    Kernel::TermList apply(unsigned variable) const override;
    Kernel::TermList lhs, rhs;
  private:
    const Kernel::SubstApplicator& subst;
    Kernel::Renaming normalization;
    bool _valid;
  };

  static InferenceRecorder* instance();

  /** Parent banks: main (0), equality (1). lhs is the original equality LHS.
   * target belongs to the main premise.
   * constraintCount counts trailing conclusion literals. */
  void superposition(Kernel::Clause* conclusion, Kernel::Clause* main,
                     Kernel::Clause* equality, Substitutions substitutions, Kernel::Literal* rewrittenLiteral,
                     Kernel::Literal* equalityLiteral, Kernel::TermList lhs, Kernel::TermList target,
                     unsigned constraintCount);

  /** constraintCount counts leading conclusion literals; parent banks are left (0), right (1). */
  void resolution(Kernel::Clause* conclusion, Kernel::Clause* left,
                  Kernel::Clause* right, Substitutions substitutions,
                  Kernel::Literal* resolvedLeft, Kernel::Literal* resolvedRight,
                  unsigned constraintCount);

  void factoring(Kernel::Clause* conclusion, Kernel::Clause* premise,
                 Substitutions substitutions, Kernel::Literal* selectedLiteral, Kernel::Literal* removedLiteral);

  /** lhs gives the indexed rewrite orientation; target is the original
   * rewritten subterm. Parent banks are premise (0), equality (1). */
  void forwardDemodulation(Kernel::Clause* conclusion, Kernel::Clause* premise,
                           Kernel::Clause* equality, Substitutions substitutions,
                           Kernel::Literal* rewrittenLiteral,
                           Kernel::TermList lhs, Kernel::TermList target);

  /** Activate a temporary recorder for this replay. Restores the previous recorder on exit. */
  explicit InferenceRecorder(Kernel::Clause* goal);

  const Inferences::InferenceReplayInformation* information() const
  { return _information ? _information->findComponent<Inferences::InferenceReplayInformation>() : nullptr; }
  std::unique_ptr<Lib::InferenceExtra> takeInformation()
  { return std::move(_information); }

  InferenceRecorder(const InferenceRecorder&) = delete;
  InferenceRecorder& operator=(const InferenceRecorder&) = delete;

private:
  using InferenceInformation = Inferences::InferenceReplayInformation;
  using ConstraintInformation = Inferences::ConstraintInformation;
  // Candidate variable number -> recorded goal variable number.
  using VariableMap = std::unordered_map<unsigned, unsigned>;
  /** Return nullopt for a rejected candidate; keep the previous result.
   * outputRenaming, if supplied, receives the candidate-to-goal alpha-renaming. */
  std::optional<InferenceInformation> record(Kernel::Clause* conclusion, std::vector<Kernel::Clause*> premises,
              Substitutions substitutions, Kernel::Substitution* outputRenaming = nullptr);
  /** first/count select conclusion literals; renaming maps candidate variables to goal variables. */
  void recordConstraints(Kernel::Clause* candidate,
      ConstraintInformation& constraints, const Kernel::Substitution& renaming,
      unsigned first, unsigned count);
  /** varMap maps candidate variables to goal variables; empty means identity. */
  Kernel::Substitution goalAlphaRenaming(const VariableMap& varMap);
  /** renaming maps alpha-equivalent candidate variables to goal names.
   * Extend it for eliminated variables using freshVariable, the next unused
   * name above the goal's variables. Share both across parent banks. */
  Kernel::TermList alphaRenameToGoal(Kernel::TermList term,
      Kernel::Substitution& renaming, unsigned& freshVariable);
  /** On success, varMap contains the candidate-to-goal alpha-renaming;
   * an empty map means identity. */
  bool isSameAsProofStep(Kernel::Clause* clause, Kernel::Clause* goal, VariableMap& varMap);

  static InferenceRecorder* _active;
  Lib::ScopedLet<InferenceRecorder*> _activation;
  Kernel::Clause* _currentGoal;
  std::unique_ptr<Lib::InferenceExtra> _information;
};
}
#endif

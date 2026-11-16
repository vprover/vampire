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
#include "Kernel/Substitution.hpp"
#include <initializer_list>
#include <memory>
#include <unordered_map>
#include <vector>
#include <variant>

namespace Indexing { struct DemodulatorData; }

namespace Shell {
class InferenceRecorder {
public:
  struct LiteralPosition { unsigned premiseIndex; unsigned literalIndex; };

  struct RewriteInformation {
    LiteralPosition rewrittenLiteral;
    LiteralPosition equality;
    Kernel::TermList from;
    Kernel::TermList to;
  };
  struct ConstraintInformation {
    std::vector<Kernel::Literal*> literals;
  };
  struct ResolvedLiteralsInformation {
    LiteralPosition left;
    LiteralPosition right;
  };
  struct SuperpositionInformation {
    RewriteInformation rewrite;
    ConstraintInformation constraints;
  };
  struct ResolutionInformation {
    ResolvedLiteralsInformation resolvedLiterals;
    ConstraintInformation constraints;
  };
  struct FactoringInformation {
    LiteralPosition removedLiteral;
  };
  struct ForwardDemodulationInformation {
    RewriteInformation rewrite;
  };

  /** Clauses and literals are borrowed; substitutions are owned. */
  struct InferenceInformation {
    Kernel::Clause* conclusion;
    std::vector<Kernel::Clause*> premises;
    std::vector<Kernel::Substitution> substitutionForBanksSub;
    std::variant<SuperpositionInformation, ResolutionInformation,
                 FactoringInformation, ForwardDemodulationInformation> details;
  };

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

  /** Parent banks: main (0), equality (1). from uses bank 0; to uses bank 1.
   * constraintCount counts trailing conclusion literals. */
  void superposition(Kernel::Clause* conclusion, Kernel::Clause* main,
                     Kernel::Clause* equality, Substitutions substitutions, Kernel::Literal* rewrittenLiteral,
                     Kernel::Literal* equalityLiteral, Kernel::TermList from,
                     Kernel::TermList to, unsigned constraintCount);

  /** constraintCount counts leading conclusion literals; parent banks are left (0), right (1). */
  void resolution(Kernel::Clause* conclusion, Kernel::Clause* left,
                  Kernel::Clause* right, Substitutions substitutions,
                  Kernel::Literal* resolvedLeft, Kernel::Literal* resolvedRight,
                  unsigned constraintCount);

  void factoring(Kernel::Clause* conclusion, Kernel::Clause* premise,
                 Substitutions substitutions, Kernel::Literal* removedLiteral);

  /** lhs/rhs give the indexed rewrite orientation; parent banks are premise (0), equality (1). */
  void forwardDemodulation(Kernel::Clause* conclusion, Kernel::Clause* premise,
                           Kernel::Clause* equality, Substitutions substitutions,
                           Kernel::Literal* rewrittenLiteral,
                           Kernel::TermList lhs, Kernel::TermList rhs);

  /** Clear the previous result. goal is borrowed and must outlive recording. */
  void setCurrentGoal(Kernel::Clause* goal)
  {
    _currentGoal = goal;
    _lastInference.reset();
  }

  /** Borrowed result, or nullptr. Invalidated by a new accepted candidate or setCurrentGoal(). */
  const InferenceInformation* getLastRecordedInferenceInformation() const
  { return _lastInference.get(); }

  InferenceRecorder(const InferenceRecorder&) = delete;
  InferenceRecorder& operator=(const InferenceRecorder&) = delete;

private:
  InferenceRecorder() = default;
  // Candidate variable number -> recorded goal variable number.
  using VariableMap = std::unordered_map<unsigned, unsigned>;
  /** Return nullptr for a rejected candidate; keep the previous result.
   * outputRenaming, if supplied, receives the candidate-to-goal alpha-renaming. */
  InferenceInformation* record(Kernel::Clause* conclusion, std::vector<Kernel::Clause*> premises,
              Substitutions substitutions, Kernel::Substitution* outputRenaming = nullptr);
  /** first/count select conclusion literals; renaming maps candidate variables to goal variables. */
  void recordConstraints(const InferenceInformation& info,
      ConstraintInformation& constraints, const Kernel::Substitution& renaming,
      unsigned first, unsigned count);
  /** rewrittenLiteral belongs to parent 0; equality to parent 1.
   * fromBank/toBank identify the substitutions for from/to. */
  void recordRewrite(const InferenceInformation& info, RewriteInformation& rewrite,
      Kernel::Literal* rewrittenLiteral, Kernel::Literal* equality,
      Kernel::TermList from, unsigned fromBank, Kernel::TermList to, unsigned toBank);
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

  Kernel::Clause* _currentGoal = nullptr;
  std::unique_ptr<InferenceInformation> _lastInference;
};
}
#endif

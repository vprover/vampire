/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ProofExtra.hpp
 * Various objects that include "extra information" about an inference,
 * e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#ifndef __Inferences_ProofExtra__
#define __Inferences_ProofExtra__

#include <memory>
#include <optional>
#include <vector>

#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"

namespace Inferences {

/** Abstraction constraints in goal variables, in recorded order. */
struct ConstraintInformation {
  std::vector<Kernel::Literal*> literals;
  void output(std::ostream& out) const;
};

/** Proof clauses and substitutions, ordered by parent bank.
 * Repeated parents have separate banks. Maps translate parent variables into
 * the goal's namespace, freshening variables absent from the conclusion. */
struct InferenceReplayInformation {
  Kernel::Clause* conclusion;
  std::vector<Kernel::Clause*> premises;
  std::vector<Kernel::Substitution> substitutionForBanksSub;
  std::optional<ConstraintInformation> constraints;

  void output(std::ostream& out) const;
};

/** Search extras acquire replay metadata when the recorded step is replayed. */
struct ReplayableInferenceExtra : InferenceExtra {
  std::unique_ptr<InferenceReplayInformation> replay;

  const InferenceReplayInformation* replayInformation() const override {
    return replay.get();
  }

protected:
  void outputReplay(std::ostream& out) const;
};

/** Main uses bank 0; Other uses bank 1, or bank 0 for unary inferences. */
enum class ReferenceTag { Main, Other };

/** Parent literal with an optional zero-based index in its clause. */
template<ReferenceTag Tag>
struct LiteralReference {
  explicit LiteralReference(Kernel::Literal* reference,
      std::optional<unsigned> position = std::nullopt)
    : reference(reference), position(position) {}

  Kernel::Literal* literal() const { return reference; }
  void output(std::ostream& out) const {
    out << (Tag == ReferenceTag::Main ? "main" : "other")
        << "=(" << reference->toString() << ')';
    if (position) { out << '@' << *position; }
  }

  Kernel::Literal* reference;
  std::optional<unsigned> position;
};

/** Parent term with an optional index of its containing literal.
 * Main is the rewrite target; Other is the equality LHS. */
template<ReferenceTag Tag>
struct TermListReference {
  explicit TermListReference(Kernel::TermList reference,
      std::optional<unsigned> position = std::nullopt)
    : reference(reference), position(position) {}

  Kernel::TermList term() const { return reference; }
  void output(std::ostream& out) const {
    out << (Tag == ReferenceTag::Main ? "main" : "other") << "=(" << reference << ')';
    if (position) { out << '@' << *position; }
  }

  Kernel::TermList reference;
  std::optional<unsigned> position;
};

/** Main/other denote retained/removed literals in factoring, rewritten/equality
 * literals in superposition, and left/right resolved literals in resolution. */
struct LiteralPairInformation {
  LiteralPairInformation(Kernel::Literal* main, Kernel::Literal* other)
    : main(main), other(other) {}

  LiteralReference<ReferenceTag::Main> main;
  LiteralReference<ReferenceTag::Other> other;
  void output(std::ostream& out) const;
};

/** Rewrite operands retain their original parent variables. */
struct RewriteInformation {
  RewriteInformation(Kernel::TermList lhs, Kernel::TermList target)
    : target(target),lhs(lhs) {}

  TermListReference<ReferenceTag::Main> target;
  TermListReference<ReferenceTag::Other> lhs;
  void output(std::ostream& out) const;
};

/** Condition and answer literals for synthesis's if-then-else answer. */
struct SynthesisInferenceExtra {
  Kernel::Literal* condition = nullptr;
  Kernel::Literal* thenLit = nullptr;
  Kernel::Literal* elseLit = nullptr;

  bool empty() const { return !condition && !thenLit && !elseLit; }
  void output(std::ostream& out) const;
};

struct LiteralInferenceExtra : ReplayableInferenceExtra {
  explicit LiteralInferenceExtra(Kernel::Literal* selected) : selectedLiteral(selected) {}

  LiteralReference<ReferenceTag::Main> selectedLiteral;
  void output(std::ostream& out) const override;
};

struct TwoLiteralInferenceExtra : ReplayableInferenceExtra {
  TwoLiteralInferenceExtra(Kernel::Literal* main, Kernel::Literal* other,
      Kernel::Literal* condition = nullptr, Kernel::Literal* thenLit = nullptr,
      Kernel::Literal* elseLit = nullptr)
    : literals(main, other), synthesisExtra{condition, thenLit, elseLit} {}

  LiteralPairInformation literals;
  SynthesisInferenceExtra synthesisExtra;
  void output(std::ostream& out) const override;
};

struct RewriteInferenceExtra : ReplayableInferenceExtra {
  RewriteInferenceExtra(Kernel::TermList lhs, Kernel::TermList target)
    : rewrite(lhs, target) {}

  RewriteInformation rewrite;
  void output(std::ostream& out) const override;
};

struct TwoLiteralRewriteInferenceExtra : ReplayableInferenceExtra {
  TwoLiteralRewriteInferenceExtra(Kernel::Literal* main, Kernel::Literal* other,
      Kernel::TermList lhs, Kernel::TermList target,
      Kernel::Literal* condition = nullptr, Kernel::Literal* thenLit = nullptr,
      Kernel::Literal* elseLit = nullptr)
    : literals(main, other), rewrite(lhs, target),
      synthesisExtra{condition, thenLit, elseLit} {}

  LiteralPairInformation literals;
  RewriteInformation rewrite;
  SynthesisInferenceExtra synthesisExtra;
  void output(std::ostream& out) const override;
};

}

#endif

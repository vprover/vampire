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

#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"

namespace Inferences {

/** Main uses bank 0; Other uses bank 1, or bank 0 for unary inferences. */
enum class ReferenceTag { Main, Other };

/** Borrowed literal with an optional replay literal index.
 * Main/Other denote retained/removed literals in factoring, rewritten/equality
 * literals in superposition, and left/right resolved literals in resolution. */
template<ReferenceTag Tag>
struct LiteralReferenceInferenceExtra : public InferenceExtra {
  explicit LiteralReferenceInferenceExtra(Kernel::Literal* reference,
      std::optional<unsigned> position = std::nullopt)
    : reference(reference), position(position) {}

  Kernel::Literal* literal() const { return reference; }
  void output(std::ostream& out) const override {
    out << (Tag == ReferenceTag::Main ? "main" : "other")
        << "=(" << reference->toString() << ')';
    if (position) {
      out << '@' << *position;
    }
  }

  Kernel::Literal* reference; ///< Borrowed parent literal.
  std::optional<unsigned> position; ///< Zero-based literal index, if replayed.
};

/** Borrowed term in its original parent variables, with an optional source-literal index.
 * Main is the target; Other is the equality LHS. */
template<ReferenceTag Tag>
struct TermReferenceInferenceExtra : public InferenceExtra {
  explicit TermReferenceInferenceExtra(Kernel::TermList reference,
      std::optional<unsigned> position = std::nullopt)
    : reference(reference), position(position) {}

  Kernel::TermList term() const { return reference; }
  void output(std::ostream& out) const override {
    out << (Tag == ReferenceTag::Main ? "main" : "other") << "=(" << reference << ')';
    if (position) {
      out << '@' << *position;
    }
  }

  Kernel::TermList reference; ///< Borrowed term handle.
  std::optional<unsigned> position; ///< Zero-based containing-literal index, if replayed.
};

/** Main selected literal. */
using LiteralInferenceExtra = LiteralReferenceInferenceExtra<ReferenceTag::Main>;
/** Side or removed literal. */
using OtherLiteralInferenceExtra = LiteralReferenceInferenceExtra<ReferenceTag::Other>;
/** Equality side used as the rewrite source. */
using RewriteLhsInferenceExtra = TermReferenceInferenceExtra<ReferenceTag::Other>;
/** Rewrite target; equality factoring uses the other equality's RHS. */
using RewriteTargetInferenceExtra = TermReferenceInferenceExtra<ReferenceTag::Main>;

/** Borrowed condition and answer literals for synthesis's if-then-else answer. */
struct SynthesisInferenceExtra : public InferenceExtra {
  SynthesisInferenceExtra(Kernel::Literal* condition, Kernel::Literal* thenLit, Kernel::Literal* elseLit)
    : condition(condition), thenLit(thenLit), elseLit(elseLit) {}

  void output(std::ostream& out) const override;
  Kernel::Literal* condition; ///< Branch condition.
  Kernel::Literal* thenLit; ///< Answer when condition holds.
  Kernel::Literal* elseLit; ///< Answer otherwise.
};

// Composition and factories.

/** Own components by value; each provides output(std::ostream&).
 * Runtime type lookup descends into nested InferenceExtra components.
 * Use unique component types: lookup returns the first match. */
template<class... Parts>
class CompositeInferenceExtra : public InferenceExtra {
public:
  explicit CompositeInferenceExtra(Parts... parts) : _parts(std::move(parts)...) {}

  using InferenceExtra::findComponent;

  template<class Part> Part& get() {
    return const_cast<Part&>(std::as_const(*this).template get<Part>());
  }
  template<class Part> const Part& get() const {
    auto* part = InferenceExtra::findComponent<Part>();
    ASS(part);
    return *part;
  }

  const void* findComponent(const void* type) const override {
    if (type == Lib::inferenceExtraType<CompositeInferenceExtra>()) { return this; }
    const void* found = nullptr;
    auto findPart = [&](const auto& part) {
      if (found) { return; }
      using Part = std::decay_t<decltype(part)>;
      if (type == Lib::inferenceExtraType<Part>()) { found = &part; }
      else if constexpr (std::is_base_of_v<InferenceExtra, Part>) {
        found = part.findComponent(type);
      }
    };
    std::apply([&](const auto&... parts) { (findPart(parts), ...); }, _parts);
    return found;
  }

  void output(std::ostream& out) const override {
    bool first = true;
    auto outputPart = [&](const auto& part) {
      if (!first) { out << ','; }
      first = false;
      part.output(out);
    };
    std::apply([&](const auto&... parts) { (outputPart(parts), ...); }, _parts);
  }

private:
  std::tuple<Parts...> _parts; ///< Owned parts, in output order.
};

/** Main and Other selected literals. */
using TwoLiteralInferenceExtra = CompositeInferenceExtra<LiteralInferenceExtra, OtherLiteralInferenceExtra>;
/** Target and equality LHS in Main/Other order, with optional source positions. */
using RewriteInferenceExtra = CompositeInferenceExtra<RewriteTargetInferenceExtra, RewriteLhsInferenceExtra>;
/** Selected literals and rewrite operands. */
using LiteralRewriteExtra = CompositeInferenceExtra<TwoLiteralInferenceExtra, RewriteInferenceExtra>;

/** Build a Main/Other literal pair with optional source positions. */
inline TwoLiteralInferenceExtra twoLiteralExtra(Kernel::Literal* main, Kernel::Literal* other,
    std::optional<unsigned> mainPosition = std::nullopt,
    std::optional<unsigned> otherPosition = std::nullopt)
{
  return TwoLiteralInferenceExtra(LiteralInferenceExtra(main, mainPosition),
      OtherLiteralInferenceExtra(other, otherPosition));
}

/** Build lhs/target operands; positions locate their respective source literals. */
inline RewriteInferenceExtra rewriteExtra(Kernel::TermList lhs, Kernel::TermList target,
    std::optional<unsigned> equality = std::nullopt,
    std::optional<unsigned> rewrittenLiteral = std::nullopt)
{
  return RewriteInferenceExtra(RewriteTargetInferenceExtra(target, rewrittenLiteral),
      RewriteLhsInferenceExtra(lhs, equality));
}

// Replay metadata and rule-specific details.

/** Borrowed proof clauses and owned substitutions, ordered by parent bank.
 * Repeated parents have separate banks. Maps translate parent variables into
 * the goal's namespace, freshening variables absent from the conclusion. */
struct InferenceReplayInformation {
  Kernel::Clause* conclusion; ///< Original proof goal.
  std::vector<Kernel::Clause*> premises; ///< Parents in bank order.
  std::vector<Kernel::Substitution> substitutionForBanksSub; ///< Owned map for each parent bank.

  void output(std::ostream& out) const;
};

/** Borrowed abstraction constraints in goal variables; empty if none were produced. */
struct ConstraintInformation {
  std::vector<Kernel::Literal*> literals; ///< Constraints in recorded order.
  void output(std::ostream& out) const;
};

}

#endif

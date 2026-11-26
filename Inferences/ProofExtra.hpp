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


#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"

#include <utility>
#include <vector>

namespace Inferences {

// inferences that use one literal from their main premise
struct LiteralInferenceExtra : public InferenceExtra {
  LiteralInferenceExtra(Kernel::Literal *selected) : selectedLiteral(selected) {}

  void output(std::ostream &out) const override;

  // the literal from the main premise
  Kernel::Literal *selectedLiteral;
};

// inferences that use one literal from their side premise
struct TwoLiteralInferenceExtra : public InferenceExtra {

  struct SynthesisExtra {
    SynthesisExtra(Kernel::Literal *conditionLiteral, Kernel::Literal *thenLiteral, Kernel::Literal* elseLiteral) : condition(conditionLiteral), thenLit(thenLiteral), elseLit(elseLiteral) {}
    Kernel::Literal *condition;
    Kernel::Literal *thenLit;
    Kernel::Literal *elseLit;
  };

  TwoLiteralInferenceExtra(Kernel::Literal *selected, Kernel::Literal *other, Kernel::Literal *condition = nullptr, Kernel::Literal* thenLit = nullptr, Kernel::Literal* elseLit = nullptr)
    : selectedLiteral(selected), otherLiteral(other), synthesisExtra(condition, thenLit, elseLit) {}

  void output(std::ostream &out) const override;

  // selected literal
  LiteralInferenceExtra selectedLiteral;
  // the literal from the side premise
  Kernel::Literal *otherLiteral;
  // synthesis information: condition and branch literals for if-then-else
  SynthesisExtra synthesisExtra;
};

struct RewriteInferenceExtra : public InferenceExtra {
  RewriteInferenceExtra(Kernel::TermList lhs, Kernel::TermList target)
    : lhs(lhs), rewritten(target) {}

  void output(std::ostream &out) const override;

  // the LHS used to rewrite with
  Kernel::TermList lhs;
  // the rewritten term
  Kernel::TermList rewritten;
};

struct TwoLiteralRewriteInferenceExtra : public InferenceExtra {
  TwoLiteralRewriteInferenceExtra(
    Kernel::Literal *selected,
    Kernel::Literal *other,
    Kernel::TermList lhs,
    Kernel::TermList rewritten,
    Kernel::Literal *condition = nullptr,
    Kernel::Literal *thenLit = nullptr,
    Kernel::Literal *elseLit = nullptr)
    : selected(selected, other, condition, thenLit, elseLit), rewrite(lhs, rewritten) {}
  void output(std::ostream &out) const override;

  // selected literals
  TwoLiteralInferenceExtra selected;
  // rewrite information
  RewriteInferenceExtra rewrite;
};

/**
 * Induction hyperresolution: for every premise, the images in the conclusion
 * of the premise's variables. Applying them makes the conclusion a
 * propositional consequence of the instantiated premises.
 */
struct InductionHyperresolutionExtra : public InferenceExtra {
  using Bindings = std::vector<std::pair<unsigned, Kernel::TermList>>;
  std::vector<std::pair<Kernel::Unit*, Bindings>> substitutions;

  void output(std::ostream &out) const override;
};

/**
 * A term algebra inference on one literal of its single premise: the
 * literal's index and, for generating injectivity, the index of the
 * constructor argument among the term arguments.
 */
struct TermAlgebraLiteralExtra : public InferenceExtra {
  TermAlgebraLiteralExtra(unsigned literal, unsigned argument = 0) : literal(literal), argument(argument) {}
  unsigned literal;
  unsigned argument;

  void output(std::ostream &out) const override;
};
} // namespace Inferences

#endif
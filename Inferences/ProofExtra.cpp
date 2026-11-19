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
 * @file ProofExtra.cpp
 * Various objects that include "extra information" about an inference,
 * e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#include "ProofExtra.hpp"
#include "Kernel/Clause.hpp"

namespace Inferences {

void ReplayableInferenceExtra::outputReplay(std::ostream& out) const {
  if (replay) { out << ','; replay->output(out); }
}

void LiteralPairInformation::output(std::ostream& out) const {
  main.output(out);
  out << ',';
  other.output(out);
}

void RewriteInformation::output(std::ostream& out) const {
  target.output(out);
  out << ',';
  lhs.output(out);
}

void LiteralInferenceExtra::output(std::ostream& out) const {
  selectedLiteral.output(out);
  outputReplay(out);
}

void TwoLiteralInferenceExtra::output(std::ostream& out) const {
  literals.output(out);
  if (synthesisExtra) { out << ','; synthesisExtra->output(out); }
  outputReplay(out);
}

void RewriteInferenceExtra::output(std::ostream& out) const {
  rewrite.output(out);
  outputReplay(out);
}

void TwoLiteralRewriteInferenceExtra::output(std::ostream& out) const {
  literals.output(out);
  out << ',';
  rewrite.output(out);
  if (synthesisExtra) { out << ','; synthesisExtra->output(out); }
  outputReplay(out);
}

void InferenceReplayInformation::output(std::ostream& out) const {
  out << "conclusion=" << conclusion->number() << ",parents=[";
  for (unsigned bank = 0; bank < premises.size(); ++bank) {
    if (bank) { out << ','; }
    out << premises[bank]->number() << ':' << substitutionForBanksSub[bank];
  }
  out << ']';
  if (constraints) { out << ','; constraints->output(out); }
}

void SynthesisInferenceExtra::output(std::ostream& out) const {
  if (condition) {
    out << "condition=(" << condition->toString() << ')';
  }
  if (thenLit) {
    if (condition) { out << ','; }
    out << "thenLit=(" << thenLit->toString() << ',' << thenLit << ')';
  }
  if (elseLit) {
    if (condition || thenLit) { out << ','; }
    out << "elseLit=(" << elseLit->toString() << ',' << elseLit << ')';
  }
}

void ConstraintInformation::output(std::ostream& out) const {
  out << "constraints=[";
  for (unsigned i = 0; i < literals.size(); ++i) {
    if (i) { out << ','; }
    out << *literals[i];
  }
  out << ']';
}

} // namespace Inferences

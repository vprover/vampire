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

namespace Inferences {

void LiteralInferenceExtra::output(std::ostream &out) const {
  out << "selected=(" << selectedLiteral->toString() << ')';
}

void TwoLiteralInferenceExtra::output(std::ostream &out) const {
  selectedLiteral.output(out);
  out << ",other=(" << otherLiteral->toString() << ')';
  if (synthesisExtra.condition) {
    out << ",condition=(" << synthesisExtra.condition->toString() << ")";
  }
  if (synthesisExtra.thenLit) {
    out << ",thenLit=(" << synthesisExtra.thenLit->toString() << "," << synthesisExtra.thenLit << ")";
  }
  if (synthesisExtra.elseLit) {
    out << ",elseLit=(" << synthesisExtra.elseLit->toString() << "," << synthesisExtra.elseLit << ")";
  }
}

void RewriteInferenceExtra::output(std::ostream &out) const {
  out << "lhs=" << lhs << ",target=" << rewritten;
}

void TwoLiteralRewriteInferenceExtra::output(std::ostream &out) const {
  selected.output(out);
  out << ',';
  rewrite.output(out);
}
 
}// namespace Inferences
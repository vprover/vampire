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
  LiteralInferenceExtra::output(out);
  out << ",other=(" << otherLiteral->toString() << ')';
}

void RewriteInferenceExtra::output(std::ostream &out) const {
  out << "side=" << reversed;
}

void RewriteIntoInferenceExtra::output(std::ostream &out) const {
  TwoLiteralInferenceExtra::output(out);
  out << ',';
  RewriteInferenceExtra::output(out);
  out << ",rewritten=" << rewritten;
}

} // namespace Inferences

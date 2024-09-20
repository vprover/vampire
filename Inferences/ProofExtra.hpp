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

namespace Inferences {

// inferences that use one literal from their main premise
struct LiteralInferenceExtra : virtual public InferenceExtra {
  LiteralInferenceExtra(Kernel::Literal *selected) : selectedLiteral(selected) {}

  virtual void output(std::ostream &out) const override;

  // the literal from the main premise
  Kernel::Literal *selectedLiteral;
};

// inferences that use one literal from their side premise
struct TwoLiteralInferenceExtra : public LiteralInferenceExtra {
  TwoLiteralInferenceExtra(Kernel::Literal *selected, Kernel::Literal *other)
    : LiteralInferenceExtra(selected), otherLiteral(other) {}

  virtual void output(std::ostream &out) const override;

  // the literal from the side premise
  Kernel::Literal *otherLiteral;
};

struct RewriteInferenceExtra : virtual public InferenceExtra {
  RewriteInferenceExtra(bool reversed) : reversed(reversed) {}

  virtual void output(std::ostream &out) const override;

  // if true, rewrite RHS to LHS
  bool reversed;
};

struct RewriteIntoInferenceExtra : public TwoLiteralInferenceExtra, public RewriteInferenceExtra {
  RewriteIntoInferenceExtra(
    Kernel::Literal *selected,
    Kernel::Literal *other,
    bool reversed,
    Kernel::TermList rewritten
  ) :
    TwoLiteralInferenceExtra(selected, other),
    RewriteInferenceExtra(reversed),
    rewritten(rewritten) {}

  virtual void output(std::ostream &out) const override;

  // the rewritten term
  Kernel::TermList rewritten;
};

}

#endif

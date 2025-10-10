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
 * @file ToPlaceholders.hpp
 */

#ifndef __ToPlaceholders__
#define __ToPlaceholders__


#include "Kernel/TermTransformer.hpp"
#include "Shell/Options.hpp"

using namespace Kernel;

// replaces higher-order subterms (subterms with variable heads e.g., X a b &
// lambda terms) with a special polymorphic constant we call a "placeholder".
// Depending on the mode functional and Boolean subterms may also be replaced
class ToPlaceholders : public TermTransformer
{
public:
  ToPlaceholders();

  TermList replace(TermList term);
  TermList transformSubterm(TermList t) override;

  void onTermEntry(Term* t) override {
    if (t->isApplication())
      _nextIsPrefix = true;
  }

  void onTermExit(Term* t) override {
    _nextIsPrefix = false;
  }

private:
  bool _nextIsPrefix;
  bool _topLevel;
  Shell::Options::FunctionExtensionality _mode;
};

#endif // __ToPlaceholders__

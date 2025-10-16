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

#include <optional>

using namespace Kernel;

/**
* Replaces higher-order subterms (subterms with variable heads e.g., X a b and
* lambda terms) with a special polymorphic constant we call a "placeholder".
*
* If the value of the FunctionExtensionality option is ABSTRACTION, functional and Boolean subterms are also be replaced
*
* See also tHOL_ToPlaceholders.cpp for accompanying unit tests of this class.
*/
class ToPlaceholders : public TermTransformer
{
public:
  explicit ToPlaceholders(std::optional<Shell::Options::FunctionExtensionality> funcExtMode);

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

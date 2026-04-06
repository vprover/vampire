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
 * @file SubtermReplacer.hpp
 */

#ifndef __SubtermReplacer__
#define __SubtermReplacer__

#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

/**
 * The class SubtermReplacer allows to replace all occurrences of one subterm by another.
 *
 * In contrast to EqHelper::replace free de Bruijn indices of the new subterm can be automatically
 * lifted in order to avoid name capture.
 *
 * See also tHOL_SubtermReplacer.cpp for accompanying unit tests of this class.
 */
class SubtermReplacer : public TermTransformer {
public:
  SubtermReplacer(TermList what, TermList by, bool liftFree);

  TermList replace(TermList t) {
    return transform(t);
  }

  TermList transformSubterm(TermList t) override;

  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;

private:
  TermList _what;
  TermList _by;

  bool _liftFreeIndices; // true if need to lift free indices in _by
  int _shiftBy = 0; // the amount to shift a free index by
};

#endif // __SubtermReplacer__

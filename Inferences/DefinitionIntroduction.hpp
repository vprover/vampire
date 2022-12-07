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
 * @file DefinitionIntroduction.hpp
 */

#ifndef __DefinitionIntroduction__
#define __DefinitionIntroduction__

#include "InferenceEngine.hpp"

namespace Inferences
{

class DefinitionIntroduction: public GeneratingInferenceEngine {
public:
  CLASS_NAME(DefinitionIntroduction);
  USE_ALLOCATOR(DefinitionIntroduction);

  ClauseIterator generateClauses(Clause *cl) override;

private:
  void process(Clause *cl);
  void process(Term *t);
  void introduceDefinitionFor(Term *t);
  Term *lgg(Term *left, Term *right);

  struct Entry {
    Term *term;
    unsigned count;
  };
  DHSet<Term *> _defined;
  Stack<Stack<Entry>> _entries;
  Stack<Clause *> _definitions;
};

}

#endif

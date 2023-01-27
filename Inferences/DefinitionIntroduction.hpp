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
#include "Indexing/Index.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences
{

class DefinitionIntroduction: public GeneratingInferenceEngine, public Index {
public:
  CLASS_NAME(DefinitionIntroduction);
  USE_ALLOCATOR(DefinitionIntroduction);

  void attach(SaturationAlgorithm *salg) override {
    CALL("DefinitionIntroduction::attach")
    GeneratingInferenceEngine::attach(salg);
    attachContainer(salg->getPassiveClauseContainer());
    reset = false;
  }

  void handleClause(Clause *cl, bool adding) override {
    CALL("DefinitionIntroduction::handleClause");
    if(reset)
      _definitions.reset();

    reset = false;
    if(adding)
      process(cl);
  }

  ClauseIterator generateClauses(Clause *cl) override {
    CALL("DefinitionIntroduction::generateClauses");
    reset = true;
    return pvi(decltype(_definitions)::Iterator(_definitions));
  }

private:
  void process(Clause *cl);
  void process(Term *t);
  void introduceDefinitionFor(Term *t);
  Term *lgg(Term *left, Term *right);

  struct Entry {
    Term *term;
    unsigned weight;
  };
  DHSet<Term *> _defined;
  Stack<Stack<Entry>> _entries;
  Stack<Clause *> _definitions;
  bool reset;
};

}

#endif

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
  void attach(SaturationAlgorithm *salg) override {
    GeneratingInferenceEngine::attach(salg);
    attachContainer(salg->getPassiveClauseContainer());
  }

  void handleClause(Clause *cl, bool adding) override {
    if(adding) {
      process(cl);
    }
  }

  ClauseIterator generateClauses(Clause *cl) override {
    return pvi(arrayIter(std::move(_definitions)));
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
  Lib::DHSet<Term *> _defined;
  Lib::Stack<Lib::Stack<Entry>> _entries;
  Lib::Stack<Clause *> _definitions;
};

}

#endif

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

#include <unordered_set>
#include <vector>

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
  // handle clauses, perhaps introducing a new definition
  void process(Clause *cl);
  // handle all terms in a clause
  void process(Term *t);
  // introduce a new definition for `t`
  void introduceDefinitionFor(Term *t);

  struct Entry {
    // definition to be introduced
    Term *term;
    // total weight of terms covered by the definition
    unsigned weight;
  };

  // keep track of terms already named to avoid defining them multiple times
  std::unordered_set<Term *> _defined;
  // buffer for generated clauses
  std::vector<Clause *> _definitions;

  /*
   * Not-yet-introduced candidate definitions, bucketed by function symbols.
   *
   * Each term in the passive set is either covered by an existing definition,
   * or has an entry which generalises it.
   * Each entry in the list is disjoint in the sense that their lgg is not a useful definition.
   */
  std::vector<std::vector<Entry>> _entries;
};

}

#endif

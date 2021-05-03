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
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __GeneralInduction__
#define __GeneralInduction__

#include <cmath>
#include <bitset>

#include "Forwards.hpp"

#include "Indexing/TermIndex.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/InductionSchemeGenerator.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class HeuristicGeneralizationIterator
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  HeuristicGeneralizationIterator(const OccurrenceMap& occ)
    : _occ(occ), _hasNext(true) {}

  inline bool hasNext()
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next()
  {
    CALL("HeuristicGeneralizationIterator::next()");
    ASS(_hasNext);

    auto temp = _occ;
    auto it = _occ.begin();
    while (it != _occ.end()) {
      // auto nsb = it->second.num_set_bits();
      // if (nsb == 1 || nsb == it->second.num_bits() - 1) {
        if (it->second.next()) {
          it->second.set_bits();
          break;
        }
        it->second.reset_bits();
      // }
      it++;
    }
    if (it == _occ.end()) {
      _hasNext = false;
    }
    return temp;
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
};

class InductionGeneralizationIterator
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  /* Based on a map of advanceterms to bit vectors of necessary occurrences
   * and number of all occurrences, enumerates all possible generalizations
   * as bit vectors. 
   */
  InductionGeneralizationIterator(const OccurrenceMap& occ)
    : _occ(occ), _hasNext(true) {}

  inline bool hasNext()
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next()
  {
    CALL("InductionGeneralizationIterator::next()");
    ASS(_hasNext);

    auto temp = _occ;
    auto it = _occ.begin();
    while (it != _occ.end()) {
      if (it->second.next()) {
        break;
      }
      it->second.reset_bits();
      it++;
    }
    if (it == _occ.end()) {
      _hasNext = false;
    }
    return temp;
  }

  inline vstring toString()
  {
    vstringstream str;
    for (const auto& kv : _occ) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString() << " ";
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
};

class GeneralInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(GeneralInduction);
  USE_ALLOCATOR(GeneralInduction);

  GeneralInduction(InferenceRule rule)
    : _splitter(0),
      _rule(rule) {}

  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  class InductionClauseIterator
    : public ClauseIterator
  {
  public:
    InductionClauseIterator() = default;
    DECL_ELEMENT_TYPE(Clause*);

    inline bool hasNext() { return _clauses.isNonEmpty(); }
    inline OWN_ELEMENT_TYPE next() { 
      return _clauses.pop();
    }

    Stack<Clause*> _clauses;
  };

  void process(InductionClauseIterator& it, Clause* premise, Literal* literal);
  void generateClauses(
    const Shell::InductionScheme& scheme,
    const OccurrenceMap& occurrences,
    const SLQueryResult& mainLit,
    const vset<pair<Literal*,Clause*>>& sideLits,
    ClauseStack& clauses);
  vmap<TermList, TermList> skolemizeCase(const InductionScheme::Case& c);
  bool alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
    const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res);
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> selectMainSidePairs(Literal* literal, Clause* premise);

  Splitter* _splitter;
  InferenceRule _rule;
  DHMap<Literal*, vset<Literal*>> _done;
  DemodulationSubtermIndex* _index;
};

}

#endif /*__GeneralInduction__*/

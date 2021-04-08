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

  HeuristicGeneralizationIterator(bool includeEmpty, const OccurrenceMap& occ)
    : _occ(occ), _it(_occ.begin()) {}

  inline bool hasNext()
  {
    return _it->second.hasNext();
  }

  inline OWN_ELEMENT_TYPE next()
  {
    CALL("HeuristicGeneralizationIterator::next()");
    ASS(hasNext());

    auto temp = _occ;
    _it->second.next();
    // check whether we were already at all 1
    if (hasNext()) {
      // all 1 is the next if the heuristics apply
      _it->second.set_bits();
      auto nsb = _it->second.num_set_bits();
      // if they don't apply, we invalidate the iterator
      if (nsb != 1 && nsb != _it->second.num_bits() - 1) {
        _it->second.next();
      }
      _it++;
      if (_it == _occ.end()) {
        _it = _occ.begin();
      }
    }
    return temp;
  }

private:
  OccurrenceMap _occ;
  OccurrenceMap::iterator _it;
};

class InductionGeneralizationIterator
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  /* Based on a map of advanceterms to bit vectors of necessary occurrences
   * and number of all occurrences, enumerates all possible generalizations
   * as bit vectors. 
   */
  InductionGeneralizationIterator(bool includeEmpty, const OccurrenceMap& occ)
    : _occ(occ), _it(_occ.begin())
  {
    if (!includeEmpty) {
      _it->second.next();
      _it++;
      if (_it == _occ.end()) {
        _it = _occ.begin();
      }
    }
  }

  inline bool hasNext()
  {
    return _it->second.hasNext();
  }

  inline OWN_ELEMENT_TYPE next()
  {
    CALL("InductionGeneralizationIterator::next()");
    ASS(hasNext());

    auto temp = _occ;
    _it->second.next();
    _it++;
    if (_it == _occ.end()) {
      _it = _occ.begin();
    }
    return temp;
  }

  inline vstring toString()
  {
    vstringstream str;
    for (const auto& kv : _occ) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString();
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  OccurrenceMap::iterator _it;
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
      Clause* c = _clauses.pop();
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] generate " << c->toString() << endl; 
        env.endOutput();
      }
      return c; 
    }

    Stack<Clause*> _clauses;
  };

  void process(InductionClauseIterator& it, Clause* premise, Literal* literal);
  void generateClauses(
    const Shell::InductionScheme& scheme,
    const OccurrenceMap& occurrences,
    const SLQueryResult& mainLit,
    const vvector<SLQueryResult>& sideLits,
    ClauseStack& clauses);
  vmap<TermList, TermList> skolemizeCase(const InductionScheme::Case& c);

  Splitter* _splitter;
  InferenceRule _rule;
};

}

#endif /*__GeneralInduction__*/

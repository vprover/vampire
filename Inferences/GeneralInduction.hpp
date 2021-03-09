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
  : public IteratorCore<OccurrenceMap>
{
public:
  CLASS_NAME(HeuristicGeneralizationIterator);
  USE_ALLOCATOR(HeuristicGeneralizationIterator);
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
  : public IteratorCore<OccurrenceMap>
{
public:
  CLASS_NAME(InductionGeneralizationIterator);
  USE_ALLOCATOR(InductionGeneralizationIterator);
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

private:
  OccurrenceMap _occ;
  OccurrenceMap::iterator _it;
};

class InductionGeneralization {
public:
  CLASS_NAME(InductionGeneralization);
  USE_ALLOCATOR(InductionGeneralization);
  DECL_RETURN_TYPE(InductionIterator);

  /* Based on a map of terms to bit vectors of necessary occurrences
   * and number of all occurrences, enumerates all possible generalizations
   * as bit vectors. 
   */
  InductionGeneralization(bool includeEmpty)
      : _includeEmpty(includeEmpty) {}

  OWN_RETURN_TYPE operator()(pair<InductionScheme, OccurrenceMap> p)
  {
    CALL("InductionGeneralization()");

    return pvi(pushPairIntoRightIterator(p.first,
      vi(new HeuristicGeneralizationIterator(_includeEmpty, p.second))));
  }

  bool next(OccurrenceMap& m);

private:
  bool _includeEmpty;
};

class InductionFormulaIterator
  : public IteratorCore<Clause*>
{
public:
  CLASS_NAME(InductionFormulaIterator);
  USE_ALLOCATOR(InductionFormulaIterator);
  DECL_ELEMENT_TYPE(Clause*);

  InductionFormulaIterator(
    const Shell::InductionScheme& scheme,
    const OccurrenceMap& occurrences,
    const vvector<SLQueryResult>& lits,
    const InferenceRule& rule,
    Splitter* splitter);

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next()
  {
    CALL("InductionFormulaIterator::next()");

    Clause* c = _clauses.pop();
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl; 
      env.endOutput();
    }
    return c; 
  }

private:
  Stack<Clause*> _clauses;
};

class InductionFormulaGenerator
{
public:
  CLASS_NAME(InductionFormulaGenerator);
  USE_ALLOCATOR(InductionFormulaGenerator);
  DECL_RETURN_TYPE(ClauseIterator);

  InductionFormulaGenerator(const vvector<SLQueryResult>& lits, const InferenceRule& rule, Splitter* splitter)
    : _lits(lits), _rule(rule), _splitter(splitter) {}
  
  OWN_RETURN_TYPE operator()(pair<InductionScheme, OccurrenceMap> p)
  {
    CALL("InductionFormulaGenerator()");

    return vi(new InductionFormulaIterator(p.first, p.second, _lits, _rule, _splitter));
  }

private:
  vvector<SLQueryResult> _lits;
  InferenceRule _rule;
  Splitter* _splitter;
};

class GeneralInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(GeneralInduction);
  USE_ALLOCATOR(GeneralInduction);

  GeneralInduction(
    Shell::InductionSchemeGenerator* schemeGenerator,
    InductionGeneralization* generalization,
    InferenceRule rule)
    : _schemeGenerator(schemeGenerator),
      _generalization(generalization),
      _splitter(0),
      _rule(rule) {}

  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  ClauseIterator process(Clause* premise, Literal* literal);

  Shell::InductionSchemeGenerator* _schemeGenerator;
  InductionGeneralization* _generalization;
  Splitter* _splitter;
  InferenceRule _rule;
};

}

#endif /*__GeneralInduction__*/

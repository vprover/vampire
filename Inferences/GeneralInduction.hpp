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
 * @file GeneralInduction.hpp
 * Defines class GeneralInduction
 *
 */

#ifndef __GeneralInduction__
#define __GeneralInduction__

#include "Forwards.hpp"

#include "Kernel/TermTransformer.hpp"

#include "Shell/InductionSchemeGenerator.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class NoGeneralizationIterator
  : public IteratorCore<OccurrenceMap>
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  NoGeneralizationIterator(const OccurrenceMap& occ)
    : _occ(occ), _hasNext(true) {}

  inline bool hasNext() override
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next() override
  {
    CALL("NoGeneralizationIterator::next()");
    ASS(_hasNext);

    auto it = _occ._m.begin();
    while (it != _occ._m.end()) {
      it->second.set_bits();
      it++;
    }
    _hasNext = false;
    return _occ;
  }

  inline vstring toString()
  {
    vstringstream str;
    for (const auto& kv : _occ._m) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString() << " ";
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
};

class GeneralizationIterator
  : public IteratorCore<OccurrenceMap>
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  GeneralizationIterator(const OccurrenceMap& occ, bool heuristic, bool hasFixOccurrences)
    : _occ(occ), _hasNext(true), _heuristic(heuristic), _hasFixOccurrences(hasFixOccurrences)
  {
    if (!_hasFixOccurrences) {
      // eliminate all 0s
      for (auto& o : _occ._m) {
        if (!o.second.num_set_bits()) {
          ALWAYS(o.second.next());
        }
      }
    }
  }

  inline bool hasNext() override
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next() override
  {
    CALL("GeneralizationIterator::next()");
    ASS(_hasNext);

    auto temp = _occ;
    auto it = _occ._m.begin();
    while (it != _occ._m.end()) {
      if (it->second.next()) {
        // heuristic gives only active occurrences
        // then and all occurrences, so we set all bits
        // immediately after returning only the actives
        if (_heuristic) {
          it->second.set_bits();
        }
        break;
      }
      it->second.reset_bits();
      if (!_hasFixOccurrences) {
        // eliminate all 0s as in ctor
        if (!it->second.num_set_bits()) {
          ALWAYS(it->second.next());
        }
      }
      it++;
    }
    if (it == _occ._m.end()) {
      _hasNext = false;
    }
    return temp;
  }

  inline vstring toString() const
  {
    vstringstream str;
    for (const auto& kv : _occ._m) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString() << " ";
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
  bool _heuristic;
  bool _hasFixOccurrences;
};

/**
 * Replaces occurrences of terms with variables to get a generalized literal
 */
class TermOccurrenceReplacement : public TermTransformer {
public:
  TermOccurrenceReplacement(const InductionTerms& r, const OccurrenceMap& occ, Literal* lit)
    : _r(r), _o(occ), _lit(lit) {}
  Literal* transformLit() { return transform(_lit); }
  TermList transformSubterm(TermList trm) override;

private:
  const InductionTerms& _r; // term to replace -> variable mapping
  OccurrenceMap _o;
  Literal* _lit;
};

/**
 * Replaces terms with terms such that the replacement terms within the
 * same sort occur sorted from left to right within the resulting literal
 */
class TermMapReplacement : public TermTransformer {
public:
  TermMapReplacement(const DHMap<TermList, vvector<Term*>>& m, const InductionTerms& r)
    : _m(m), _r(r), _ord(), _curr()
  {
    auto it = _m.items();
    while (it.hasNext()) {
      auto kv = it.next();
      _curr.insert(make_pair(kv.first, 0));
    }
  }
  TermList transformSubterm(TermList trm) override;

private:
  const DHMap<TermList, vvector<Term*>>& _m;
  const InductionTerms& _r;
  vmap<Term*, unsigned> _ord;
  vmap<TermList, unsigned> _curr;
};

class GeneralInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(GeneralInduction);
  USE_ALLOCATOR(GeneralInduction);

  GeneralInduction(const vvector<InductionSchemeGenerator*> gen, InferenceRule rule)
    : _gen(gen),
      _splitter(0),
      _rule(rule) {}

  ~GeneralInduction() {
    for (auto& gen : _gen) {
      delete gen;
    }
    _gen.clear();
  }

  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

#if VDEBUG
  void setTestIndices(Stack<Index*> const& indices) override {
    _index = (TermIndex*)indices[0];
  }
#endif

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
    Literal* mainLit, SLQueryResult mainQuery,
    vvector<pair<Literal*,SLQueryResult>> sideLitQrPairs,
    ClauseStack& clauses);
  bool alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
    const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res);
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> selectMainSidePairs(Literal* literal, Clause* premise);

  vvector<InductionSchemeGenerator*> _gen;
  Splitter* _splitter;
  InferenceRule _rule;
  DHMap<Literal*, vset<Literal*>> _done;
  TermIndex* _index;
};

}

#endif /*__GeneralInduction__*/

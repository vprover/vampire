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

#ifndef __Induction__
#define __Induction__

#include <cmath>

#include "Forwards.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/TermTransformer.hpp"
#include "Kernel/Theory.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

#include "InductionHelper.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

using IndexToLiteralMap = vunordered_map<unsigned,Literal*>;
using ClauseIndexToLiteralMap = vunordered_map<Clause*, IndexToLiteralMap>;

class TermReplacement : public TermTransformer {
public:
  TermReplacement(Term* o, TermList r) : _o(o), _r(r) {} 
  TermList transformSubterm(TermList trm) override;
protected:
  Term* _o;
  TermList _r;
};

class SkolemSquashingTermReplacement : public TermReplacement {
public:
  SkolemSquashingTermReplacement(Term* o, TermList r, unsigned& var)
    : TermReplacement(o, r), _v(var) {}
  TermList transformSubterm(TermList trm) override;
private:
  unsigned& _v;               // fresh variable counter supported by caller
  DHMap<Term*, unsigned> _tv; // maps terms to their variable replacement
};

class LiteralSubsetReplacement : TermTransformer {
public:
  LiteralSubsetReplacement(Literal* lit, Term* o, TermList r, const unsigned maxSubsetSize)
      : _lit(lit), _o(o), _r(r), _maxSubsetSize(maxSubsetSize) {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
    _maxIterations = pow(2, _occurrences);
  }

  // Returns transformed lit for the first 2^(_occurences) - 1 calls, then returns nullptr.
  // Sets rule to INDUCTION_AXIOM if all occurrences were transformed, otherwise sets rule
  // to GEN_INDUCTION_AXIOM.
  Literal* transformSubset(InferenceRule& rule);

  List<pair<Literal*, InferenceRule>>* getListOfTransformedLiterals(InferenceRule rule);

protected:
  virtual TermList transformSubterm(TermList trm);

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  unsigned _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  unsigned _occurrences;
  const unsigned _maxOccurrences = 20;
  Literal* _lit;
  Term* _o;
  TermList _r;
  const unsigned _maxSubsetSize;
};

struct InductionContext {
  InductionContext() = default;
  InductionContext(Term* t, Literal* l, Clause* cl)
    : _indTerm(t)
  {
    insert(cl, cl->getLiteralPosition(l), l);
  }

  static void insert(ClauseIndexToLiteralMap& cls, Clause* cl, unsigned index, Literal* lit) {
    // this constructs an empty inner map if cl is not yet mapped
    auto node = cls.emplace(cl, IndexToLiteralMap()).first;
    // check insertion into inner map was successful
    ALWAYS(node->second.emplace(index, lit).second);
  }

  void insert(Clause* cl, unsigned index, Literal* lit) {
    insert(_cls, cl, index, lit);
  }

  Formula* getFormula(TermList r, bool opposite, ClauseIndexToLiteralMap* copy = nullptr) const;
  Formula* getFormulaWithSquashedSkolems(TermList r, bool opposite, unsigned& var,
    VList** varList = nullptr, ClauseIndexToLiteralMap* copy = nullptr) const;
  bool isSingleLiteral() const {
    if (_cls.size() > 1) {
      return false;
    }
    return _cls.begin()->second.size() == 1;
  }
  bool hasInductionLiteral() const {
    for (const auto& kv : _cls) {
      for (const auto& kvInner : kv.second) {
        if (InductionHelper::isInductionLiteral(kvInner.second)) {
          return true;
        }
      }
    }
    return false;
  }

  vstring toString() const {
    vstringstream str;
    str << *_indTerm << endl;
    for (const auto& kv : _cls) {
      str << *kv.first << endl;
      for (const auto& kvInner : kv.second) {
        str << kvInner.first << " " << *kvInner.second << endl;
      }
    }
    return str.str();
  }

  Term* _indTerm;
  ClauseIndexToLiteralMap _cls;
private:
  Formula* getFormula(TermReplacement& tr, bool opposite, ClauseIndexToLiteralMap* copy = nullptr) const;
};

class ContextSubsetReplacement
  : public TermTransformer, public IteratorCore<InductionContext> {
public:
  ContextSubsetReplacement(InductionContext context);

  bool hasNext() override {
    return _iteration+1 < _maxIterations;
  }
  InductionContext next() override;

protected:
  TermList transformSubterm(TermList trm) override;

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  unsigned _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  InductionContext _context;
  TermList _r;
};


class Induction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Induction);
  USE_ALLOCATOR(Induction);

  Induction() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _comparisonIndex = static_cast<LiteralIndex*>(indices[0]);
    _structInductionTermIndex = static_cast<TermIndex*>(indices[1]);
  }
#endif // VDEBUG

private:
  // The following pointers can be null if int induction is off.
  LiteralIndex* _comparisonIndex = nullptr;
  TermIndex* _inductionTermIndex = nullptr;
  TermIndex* _structInductionTermIndex = nullptr;
};

class InductionClauseIterator
{
public:
  // all the work happens in the constructor!
  InductionClauseIterator(Clause* premise, InductionHelper helper, const Options& opt, TermIndex* structInductionTermIndex)
      : _helper(helper), _opt(opt), _structInductionTermIndex(structInductionTermIndex)
  {
    processClause(premise);
  }

  CLASS_NAME(InductionClauseIterator);
  USE_ALLOCATOR(InductionClauseIterator);
  DECL_ELEMENT_TYPE(Clause*);

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next() { 
    return _clauses.pop();
  }

private:
  void processClause(Clause* premise);
  void processLiteral(Clause* premise, Literal* lit);
  void processIntegerComparison(Clause* premise, Literal* lit);

  // Clausifies the hypothesis, resolves it against the conclusion/toResolve,
  // and increments relevant statistics.
  void produceClauses(Formula* hypothesis, InferenceRule rule, const ClauseIndexToLiteralMap& toResolve, RobSubstitution* subst = nullptr);

  // Calls generalizeAndPerformIntInduction(...) for those induction literals from inductionTQRsIt,
  // which are non-redundant with respect to the indTerm, bounds, and increasingness.
  // Note: indTerm is passed to avoid recomputation.
  void performIntInductionOnEligibleLiterals(Term* origTerm, Term* indTerm, TermQueryResultIterator inductionTQRsIt, bool increasing, TermQueryResult bound1, DHMap<Term*, TermQueryResult>& bounds2);
  // Calls generalizeAndPerformIntInduction(...) for those bounds from lowerBound, upperBound
  // (and the default bound) which are non-redundant with respect to the origLit, origTerm,
  // and increasingness.
  // Note: indLits and indTerm are passed to avoid recomputation.
  void performIntInductionForEligibleBounds(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, DHMap<Term*, TermQueryResult>& bounds1, DHMap<Term*, TermQueryResult>& bounds2);
  // If indLits is empty, first fills it with either generalized origLit, or just by origLit itself
  // (depending on whether -indgen is on).
  // Then, performs int induction for each induction literal from indLits using bound1
  // (and optionalBound2 if provided) as bounds.
  // Note: indLits may be created in this method, but it needs to be destroyed outside of it.
  void generalizeAndPerformIntInduction(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, TermQueryResult& bound1, TermQueryResult* optionalBound2);

  void performIntInduction(const InductionContext& context, InferenceRule rule, bool increasing, const TermQueryResult& bound1, TermQueryResult* optionalBound2);

  void performStructInductionOne(const InductionContext& context, InferenceRule rule);
  void performStructInductionTwo(const InductionContext& context, InferenceRule rule);
  void performStructInductionThree(const InductionContext& context, InferenceRule rule);

  bool notDone(Literal* lit, Term* t);
  bool notDoneInt(Literal* lit, Term* t, bool increasing, Term* bound1, Term* optionalBound2, bool fromComparison);

  Stack<Clause*> _clauses;
  InductionHelper _helper;
  const Options& _opt;
  TermIndex* _structInductionTermIndex;
};

};

#endif /*__Induction__*/

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
#include <functional>
#include <map>

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Theory.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/FunctionDefinitionHandler.hpp"

#include "InductionHelper.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;
using namespace Shell;

/**
 * This class is similar to @b NonVariableNonTypeIterator and is
 * used to iterate over terms in active positions inside a literal.
 * (active positions: https://doi.org/10.1007/978-3-319-66167-4_10)
 * The active positions are given by a @b FunctionDefinitionHandler
 * instance.
 */
class ActiveOccurrenceIterator
  : public Lib::IteratorCore<Term*>
{
public:
  ActiveOccurrenceIterator(Literal* lit, FunctionDefinitionHandler& fnDefHandler)
  : _stack(8), _fnDefHandler(fnDefHandler)
  {
    _stack.push(lit);
    ASS(lit->ground());
    ActiveOccurrenceIterator::next();
  }

  bool hasNext() override { return !_stack.isEmpty(); }
  Term* next() override;
private:
  Lib::Stack<Term*> _stack;
  FunctionDefinitionHandler& _fnDefHandler;
};

/**
 * Hash used to make hashing over shared terms deterministic.
 */
struct SharedTermHash {
  static bool equals(Term* t1, Term* t2) { return t1==t2; }
  static unsigned hash(Term* t) { return t->getId(); }
};

/**
 * Hash used to make hashing over clauses deterministic.
 */
struct StlClauseHash {
  std::size_t operator()(Clause* c) const { return std::hash<unsigned>()(c->number()); }
};

/**
 * This function replaces the induction terms given in @b ts
 * with static placeholders, so that already generated induction
 * formulas can be easily detected. We allow multiple induction terms,
 * so we have to index the placeholders as well with @b i.
 */
Term* getPlaceholderForTerm(const std::vector<Term*>& ts, unsigned i);

/**
 * Term transformer class that replaces
 * terms according to the mapping @b _m.
 */
class TermReplacement : public TermTransformer {
public:
  TermReplacement(const std::map<Term*, TermList>& m) : _m(m) {}
  TermList transformSubterm(TermList trm) override;
protected:
  std::map<Term*,TermList> _m;
};

/**
 * Same as @b TermReplacement, except we replace non-sort Skolems
 * with variables, used for strengthening induction hypotheses.
 */
class SkolemSquashingTermReplacement : public TermReplacement {
public:
  SkolemSquashingTermReplacement(const std::map<Term*, TermList>& m, unsigned& var)
    : TermReplacement(m), _v(var) {}
  TermList transformSubterm(TermList trm) override;
  Lib::DHMap<Term*, unsigned, SharedTermHash> _tv; // maps terms to their variable replacement
private:
  unsigned& _v; // fresh variable counter supported by caller
};

/**
 * Class representing an induction. This includes:
 * - induction terms in @b _indTerms,
 * - selected literals from clauses in @b _cls,
 *   which are inducted upon.
 */
struct InductionContext {
  explicit InductionContext(std::vector<Term*>&& ts)
    : _indTerms(ts) {}
  explicit InductionContext(const std::vector<Term*>& ts)
    : _indTerms(ts) {}
  InductionContext(const std::vector<Term*>& ts, Literal* l, Clause* cl)
    : InductionContext(ts)
  {
    insert(cl, l);
  }

  void insert(Clause* cl, Literal* lit) {
    // this constructs an empty inner map if cl is not yet mapped
    auto node = _cls.emplace(cl, LiteralStack()).first;
    node->second.push(lit);
  }

  // These two functions should be only called on objects where
  // all induction term occurrences actually inducted upon are
  // replaced with placeholders (e.g. with ContextReplacement).
  Formula* getFormula(const std::vector<TermList>& r, bool opposite, Substitution* subst = nullptr) const;
  Formula* getFormulaWithSquashedSkolems(const std::vector<TermList>& r, bool opposite, unsigned& var,
    VList** varList = nullptr, Substitution* subst = nullptr) const;

  std::string toString() const {
    std::stringstream str;
    for (const auto& indt : _indTerms) {
      str << *indt << std::endl;
    }
    for (const auto& kv : _cls) {
      str << *kv.first << std::endl;
      for (const auto& lit : kv.second) {
        str << *lit << std::endl;
      }
    }
    return str.str();
  }

  std::vector<Term*> _indTerms;
  // One could induct on all literals of a clause, but if a literal
  // doesn't contain the induction term, it just introduces a couple
  // of tautologies and duplicate literals (a hypothesis clause will
  // be of the form ~L v L v C, other clauses L v L v C). So instead,
  // we only store the literals we actually induct on. An alternative
  // would be storing indices but then we need to pass around the
  // clause as well.
  std::unordered_map<Clause*, LiteralStack, StlClauseHash> _cls;
private:
  /**
   * Creates a formula which corresponds to the conjunction of disjunction
   * of selected literals for each clause in @b _cls, where we apply the term
   * replacement @b tr on each literal. Opposite means we get the negated
   * formula, i.e. each literal is negated and conjunction and disjunction
   * are switched.
   */
  Formula* getFormula(TermReplacement& tr, bool opposite) const;
};

/**
 * Gives @b InductionContext instances with
 * induction terms replaced with placeholders.
 */
class ContextReplacement
  : public TermReplacement, public Lib::IteratorCore<InductionContext> {
public:
  ContextReplacement(const InductionContext& context);

  bool hasNext() override {
    return !_used;
  }
  InductionContext next() override;

protected:
  InductionContext _context;
  bool _used;
};

/**
 * Same as @b ContextReplacement but replaces only active occurrences
 * of induction terms, given by a @b FunctionDefinitionHandler instance.
 */
class ActiveOccurrenceContextReplacement
  : public ContextReplacement {
public:
  ActiveOccurrenceContextReplacement(const InductionContext& context, FunctionDefinitionHandler& fnDefHandler);
  InductionContext next() override;
  bool hasNonActive() const { return _hasNonActive; }

protected:
  TermList transformSubterm(TermList trm) override;

private:
  FunctionDefinitionHandler& _fnDefHandler;
  std::vector<unsigned> _iteration;
  std::vector<unsigned> _matchCount;
  bool _hasNonActive;
};

/**
 * Same as @b ContextReplacement but iterates over all non-empty
 * subsets of occurrences of the induction terms and replaces
 * only the occurrences in these subsets with placeholder terms.
 */
class ContextSubsetReplacement
  : public ContextReplacement {
public:
  ContextSubsetReplacement(const InductionContext& context, const unsigned maxSubsetSize);

  bool hasNext() override;
  InductionContext next() override;

protected:
  TermList transformSubterm(TermList trm) override;

private:
  bool shouldSkipIteration() const;
  void stepIteration();
  // _iteration serves as a map of occurrences to replace
  std::vector<unsigned> _iteration;
  std::vector<unsigned> _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  std::vector<unsigned> _matchCount;
  const unsigned _maxOccurrences = 1 << 20;
  const unsigned _maxSubsetSize;
  bool _ready;
  bool _done;
};

/**
 * The induction inference.
 */
class Induction
: public GeneratingInferenceEngine
{
  using TermIndex = Indexing::TermIndex<TermLiteralClause>;
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise) override;

#if VDEBUG
  void setTestIndices(const Lib::Stack<Index*>& indices) override {
    _comparisonIndex = static_cast<LiteralIndex<LiteralClause>*>(indices[0]);
    _inductionTermIndex = static_cast<TermIndex*>(indices[1]);
    _structInductionTermIndex = static_cast<TermIndex*>(indices[2]);
  }
#endif // VDEBUG

private:
  // The following pointers can be null if int induction is off.
  LiteralIndex<LiteralClause>* _comparisonIndex = nullptr;
  TermIndex* _inductionTermIndex = nullptr;
  TermIndex* _structInductionTermIndex = nullptr;
  InductionFormulaIndex _formulaIndex;
  InductionFormulaIndex _recFormulaIndex;
};

/**
 * Helper class that generates all induction clauses for
 * a premise and serves as an iterator for these clauses.
 */
class InductionClauseIterator
{
  using TermIndex               = Indexing::TermIndex<TermLiteralClause>;
public:
  // all the work happens in the constructor!
  InductionClauseIterator(Clause* premise, InductionHelper helper, SaturationAlgorithm* salg,
    TermIndex* structInductionTermIndex, InductionFormulaIndex& formulaIndex)
      : _helper(helper), _opt(salg->getOptions()), _structInductionTermIndex(structInductionTermIndex),
      _formulaIndex(formulaIndex), _fnDefHandler(salg->getFunctionDefinitionHandler())
  {
    processClause(premise);
  }

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

  ClauseStack produceClauses(Formula* hypothesis, InferenceRule rule, const InductionContext& context);
  void resolveClauses(InductionContext context, InductionFormulaIndex::Entry* e, const TermLiteralClause* bound1, const TermLiteralClause* bound2);
  void resolveClauses(const ClauseStack& cls, const InductionContext& context, Substitution& subst, bool applySubst = false);

  void performFinIntInduction(const InductionContext& context, const TermLiteralClause& lb, const TermLiteralClause& ub);
  void performInfIntInduction(const InductionContext& context, bool increasing, const TermLiteralClause& bound);

  struct DefaultBound { TypedTermList term; };
  using Bound = Lib::Coproduct<TermLiteralClause, DefaultBound>;
  void performIntInduction(const InductionContext& context, InductionFormulaIndex::Entry* e, bool increasing, Bound bound1, const TermLiteralClause* optionalBound2);

  void performIntInduction(const InductionContext& context, InductionFormulaIndex::Entry* e, bool increasing, TermLiteralClause const& bound1, const TermLiteralClause* optionalBound2)
  { performIntInduction(context, e, increasing, Bound::variant<0>(bound1), optionalBound2); }

  void performStructInductionOne(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performStructInductionTwo(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performStructInductionThree(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performRecursionInduction(const InductionContext& context, const InductionTemplate* templ, const std::vector<Term*>& typeArgs, InductionFormulaIndex::Entry* e);

  /**
   * Whether an induction formula is applicable (or has already been generated)
   * is determined by its conclusion part, which is resolved against the literals
   * and bounds we induct on. From this point of view, an integer induction formula
   * can have one lower bound and/or one upper bound. This function wraps this
   * information by adding the bounds and querying the index with the resulting context.
   *
   * TODO: default bounds are now stored as special cases with no bounds (this makes
   * the resolve part easier) but this means some default bound induction formulas
   * are duplicates of normal formulas.
   */
  bool notDoneInt(InductionContext context, Literal* bound1, Literal* bound2, InductionFormulaIndex::Entry*& e);

  /**
   * If the integer induction literal is a comparison, and the induction term is
   * one of its arguments, the other argument should not be allowed as a bound
   * (such inductions are useless and can lead to redundant literals in the
   * induction axiom).
   */
  bool isValidBound(const InductionContext& context, const Bound& bound);
  bool isValidBound(const InductionContext& context, const TermLiteralClause& bound)
  { return isValidBound(context, Bound(bound)); }

  Lib::Stack<Clause*> _clauses;
  InductionHelper _helper;
  const Options& _opt;
  TermIndex* _structInductionTermIndex;
  InductionFormulaIndex& _formulaIndex;
  FunctionDefinitionHandler& _fnDefHandler;
};

};

#endif /*__Induction__*/

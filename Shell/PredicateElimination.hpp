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
 * @file PredicateElimination.hpp
 * Defines class PredicateElimination.
 */

#ifndef __PredicateElimination__
#define __PredicateElimination__

#include "Forwards.hpp"

#include "Kernel/Problem.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/ClauseCodeTree.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Predicate elimination for preprocessing of clausified problems,
 * after Khasidashvili and Korovin: "Predicate Elimination for Preprocessing
 * in First-Order Theorem Proving" (SAT 2016).
 *
 * A predicate P which occurs at most once in every clause (is "non-self-referential")
 * can be eliminated by replacing the clauses S_P and S_~P (those containing P positively,
 * respectively, negatively) by all the pairwise resolvents on P. In the presence
 * of equality (or theories), the resolvents need to be computed via (virtual) flattening
 * of the P-literals, i.e. C \/ P(ts) and D \/ ~P(ss) yield C \/ D' \/ t1 != s1' \/ ... \/ tn != sn'
 * (with D \/ ~P(ss) renamed apart), simplified by the equality substitution rule
 * (x != t \/ C ==> C[t/x], when x not in t). Without equality/theories it is
 * sound (and avoids introducing equality) to use an mgu instead and drop
 * the non-unifiable pairs.
 *
 * Elimination steps are subject to clause-growth limits estimated
 * SAT-style as |S_P|*|S_~P| resolvents replacing |S_P|+|S_~P| clauses.
 */
class PredicateElimination {
public:
  /**
   * @param forceEquationally  force the flattening-based resolvent computation even on
   *        problems without equality/theories (required under FMB, whose model
   *        reconstruction cannot rely on the Herbrand-interpretation argument
   *        that justifies the mgu mode)
   * @param totalLimit  an elimination step is admissible only if the estimated
   *        number of clauses afterwards does not exceed the initial number times this factor
   * @param useSubsumption  keep the clause set forward-inter-subsumed and
   *        subsumption-resolved
   */
  PredicateElimination(bool forceEquationally, float totalLimit, bool useSubsumption)
      : _forceEquationally(forceEquationally),
        _totalLimit(totalLimit), _useSubsumption(useSubsumption) {}

  void apply(Kernel::Problem &prb);

private:
  struct PredInfo {
    Lib::DHSet<Clause *> pos; // S_P: clauses in which P occurs exactly once, positively
    Lib::DHSet<Clause *> neg; // S_~P: dtto, negatively
    unsigned blockers = 0;    // number of clauses in which P occurs more than once
    bool eliminated = false;
  };

  // options
  const bool _forceEquationally;
  const float _totalLimit;
  const bool _useSubsumption;

  // clause set state
  ClauseStack _all;     // all clauses ever seen, in insertion order
  Lib::DHSet<Clause *> _deleted; // those of _all that have been eliminated
  Lib::DArray<PredInfo> _preds;
  size_t _curTotal = 0;
  size_t _origTotal = 0;
  bool _equational = false;
  bool _modified = false;
  bool _keptDisequality = false;       // some resolvent kept a residual disequality
  bool _keptVarVarDisequality = false; // ... between two variables

  template<bool add>
  void handleClause(Clause *cl);

  bool eligible(unsigned pred) const;
  double estimatedTotalAfter(unsigned pred) const;
  bool admissible(unsigned pred) const;
  int pickCandidate() const;

  void eliminate(Problem &prb, unsigned pred);
  Literal *findPredLiteral(Clause *cl, unsigned pred, bool polarity) const;

  // resolvent construction; nullptr means no clause results (tautology / non-unifiable pair)
  Clause *buildResolvent(Clause *c, Literal *plitC, Clause *d, Literal *plitD);
  Clause *buildResolventMgu(Clause *c, Literal *plitC, Clause *d, Literal *plitD);
  Clause *buildResolventEq(Clause *c, Literal *plitC, Clause *d, Literal *plitD);
  Clause *assembleClause(LiteralStack &lits, Clause *c, Clause *d);

  // model reconstruction
  void recordElimination(Problem &prb, unsigned pred, ClauseStack const &posCls, ClauseStack const &negCls);

  // forward subsumption (and subsumption resolution) machinery, only used with _useSubsumption;
  // the backward direction (new clauses simplifying older ones) is left as future work
  // a whole-clause index, which also performs the multi-literal matching for us
  Indexing::ClauseCodeTree<false> _ct; // only populated when _useSubsumption
  // simplify cl against the indexed clause set (to fixpoint): returns nullptr if cl
  // is subsumed, otherwise cl itself or a subsumption-resolution descendant of it
  Clause *forwardSimplify(Clause *cl);
  // one round: true means subsumed; otherwise replacement is set to the
  // subsumption resolution conclusion (or nullptr, if nothing applied)
  bool forwardSubsumedOrResolved(Clause *cl, Clause *&replacement);
  void indexInsert(Clause *cl);
  void indexRemove(Clause *cl);
};

} // namespace Shell

#endif /* __PredicateElimination__ */

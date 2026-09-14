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
 * With multiOccurrence enabled, the self-referentiality condition is relaxed to:
 * 1) P never occurs both positively and negatively in a single clause, and
 * 2) clauses with more than one occurrence of P sit on at most one polarity side,
 *    i.e. every clause of S_P has exactly one P-literal, or every clause of S_~P does.
 * Calling the (possibly) multi-occurrence side the nuclei and the (necessarily)
 * single-occurrence side the satellites, the replacement clauses are then all the
 * hyper-resolvents: a nucleus with k occurrences of P is resolved against a k-tuple
 * of satellites, over all |S_satellite|^k ordered tuples (the same satellite may be
 * picked twice, in which case two variable-disjoint variants of it are used).
 * Condition 2) is what makes the P-resolution closure finite: resolving a clause with
 * two positive occurrences against one with two negative occurrences would yield a
 * clause violating condition 1), which could then keep resolving with itself.
 * It is also what keeps the model reconstruction possible, the definition of P having
 * to be built from the satellite side (see definitionBody, which does it in either
 * direction, the multiplicities deciding which one).
 * Note that no factoring is needed: the resolvent obtained by first factoring
 * P(s) \/ P(t) is an instance (modulo duplicate literal removal) of a hyper-resolvent,
 * and is therefore subsumed by it.
 *
 * Elimination steps are subject to clause-growth limits estimated SAT-style as
 * sum over nuclei of |S_satellite|^k resolvents replacing |S_P|+|S_~P| clauses
 * (which is just |S_P|*|S_~P| when all the multiplicities k are 1).
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
   * @param multiOccurrence  also eliminate predicates occurring more than once
   *        in a clause, as long as conditions 1) and 2) above hold
   */
  PredicateElimination(bool forceEquationally, float totalLimit, bool useSubsumption,
                       bool multiOccurrence)
      : _forceEquationally(forceEquationally),
        _totalLimit(totalLimit), _useSubsumption(useSubsumption),
        _multiOccurrence(multiOccurrence) {}

  void apply(Kernel::Problem &prb);

private:
  struct PredInfo {
    // S_P: clauses in which P occurs only positively, mapped to the number of occurrences;
    // S_~P: dtto, negatively (clauses with both polarities are counted as blockers instead)
    Lib::DHMap<Clause *, unsigned, UnitHash, UnitNumberHash> pos;
    Lib::DHMap<Clause *, unsigned, UnitHash, UnitNumberHash> neg;
    unsigned blockers = 0; // number of clauses in which P occurs both positively and negatively
    unsigned posMulti = 0; // number of clauses of pos with more than one occurrence
    unsigned negMulti = 0; // dtto, for neg
    bool eliminated = false;
    bool rprSkipped = false;  // under randomized preprocessing: picked but skipped, never to be reconsidered
  };

  // options
  const bool _forceEquationally;
  const float _totalLimit;
  const bool _useSubsumption;
  const bool _multiOccurrence;

  // clause set state
  ClauseStack _all;     // all clauses ever seen, in insertion order
  Lib::DHSet<Clause *, UnitHash, UnitNumberHash> _deleted; // those of _all that have been eliminated
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
  /** which side carries the (possible) multi-occurrence clauses, i.e. plays the nuclei;
   * the satellites, all with exactly one occurrence, then come from the other side */
  bool posIsNucleus(unsigned pred) const { return _preds[pred].negMulti == 0; }

  /** the number of hyper-resolvents when at least one side does have multiplicities;
   * out of line, and out of estimatedTotalAfter's body, only to keep that one inlinable */
  double multiOccurrenceResolvents(PredInfo const &info, double sp, double sn) const;
  /**
   * Estimate the clause count after eliminating @b pred. This sits in the innermost loop of
   * pickCandidate, which rescans the whole signature on every elimination round, so the
   * overwhelmingly common all-multiplicities-are-1 case must stay just a few loads and a
   * multiply -- and must stay small enough for the compiler to inline it.
   */
  double estimatedTotalAfter(unsigned pred) const
  {
    const PredInfo &info = _preds[pred];
    double sp = info.pos.size();
    double sn = info.neg.size();
    // an overflow to infinity below simply makes the step inadmissible, which is what we want
    double resolvents = (info.posMulti == 0 && info.negMulti == 0)
                            ? sp * sn
                            : multiOccurrenceResolvents(info, sp, sn);
    return (double)_curTotal - sp - sn + resolvents;
  }
  bool admissible(unsigned pred) const;
  int pickCandidate() const;

  void eliminate(Problem &prb, unsigned pred);
  /** the indices of the literals of @b cl with the given predicate and polarity */
  void collectPredLiterals(Clause *cl, unsigned pred, bool polarity, Lib::Stack<unsigned> &idxs) const;
  Literal *findPredLiteral(Clause *cl, unsigned pred, bool polarity) const;

  // (hyper-)resolvent construction; nullptr means no clause results (tautology / non-unifiable tuple).
  // choice[j] picks, out of sats/satLits, the satellite whose (unique) pred-literal gets
  // resolved against (*nucleus)[nucIdxs[j]]; the same satellite may be picked more than once
  Clause *buildResolvent(Clause *nucleus, Lib::Stack<unsigned> const &nucIdxs,
                         ClauseStack const &sats, LiteralStack const &satLits,
                         Lib::DArray<unsigned> const &choice);
  Clause *buildResolventMgu(Clause *nucleus, Lib::Stack<unsigned> const &nucIdxs,
                            ClauseStack const &sats, LiteralStack const &satLits,
                            Lib::DArray<unsigned> const &choice);
  Clause *buildResolventEq(Clause *nucleus, Lib::Stack<unsigned> const &nucIdxs,
                           ClauseStack const &sats, LiteralStack const &satLits,
                           Lib::DArray<unsigned> const &choice);
  Clause *assembleClause(LiteralStack &lits, Clause *nucleus,
                         ClauseStack const &sats, Lib::DArray<unsigned> const &choice);

  // model reconstruction
  void recordElimination(Problem &prb, unsigned pred, ClauseStack const &posCls, ClauseStack const &negCls);
  /** the shared body of the two model reconstruction directions (see above);
   * @param fromPos selects the primal (built from S_P) or the dual (from S_~P) one */
  Formula *definitionBody(unsigned pred, ClauseStack const &cls, bool fromPos);

  // forward subsumption (and subsumption resolution) machinery, only used with _useSubsumption;
  // the backward direction (new clauses simplifying older ones) is left as future work
  // a whole-clause index, which also performs the multi-literal matching for us
  Indexing::ClauseCodeTree _ct; // only populated when _useSubsumption
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

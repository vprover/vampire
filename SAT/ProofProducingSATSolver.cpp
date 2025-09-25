/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/*
 * ProofProducingSATSolver.cpp
 * This file half-implements a binary DRAT decoder and a RUP checker,
 * in order to reconstruct CaDiCaL proofs. You can read more about it in e.g.
 *
 * "The DRAT format and DRAT-trim checker", Heule.
 * https://arxiv.org/abs/1610.06229
 */

#include <deque>
#include <fstream>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "SATClause.hpp"
#include "CadicalInterfacing.hpp"
#include "ProofProducingSATSolver.hpp"

namespace SAT {

// which watched literal are we watching?
enum Which {
  W1,
  W2
};

// a 2-watched-literal structure
struct Watched {
  // the clause
  SATClause *cl;
  // which literals are we watching? indexes into `cl`
  unsigned watch[2];

  SATLiteral watching(Which which) { return (*cl)[watch[which]]; }
};

// a gadget for doing reverse unit propagations with respect to a known set of clauses
// and subsequently reporting which were necessary to derive a certain RUP clause
class ReverseUnitPropagator {
public:
  // load some set of premises
  ReverseUnitPropagator(SATClauseList *initial) {
    for(SATClause *cl : iterTraits(initial->iter()))
      addClause(cl);
  }

  // if a conflict is detected, this is set to the (non-zero) conflict variable
  unsigned conflict = 0;

  // add a clause to the known set
  void addClause(SATClause *cl) {
    // no need to do anything if we already have a conflict
    if(conflict)
      return;

    // special-case units
    if(cl->length() == 1)
      return propagate_because<false>((*cl)[0], cl);

    // initially watch the first two literals, which may not be correct
    Watched w { cl, {0, 1} };

    // correct the watched literals
    for(Which which : {W1, W2})
      // if a watched literal is not satisfied, update the watch
      if(set(w.watching(which).opposite()) && !update_watch(w, which)) {
        // if that fails, can propagate
        propagate_all<false>();
        return;
      }

    // TODO could not be a shared_ptr if we need more efficiency,
    // would just have to remember to delete it from the watched lists on destruction
    auto shared = std::make_shared<Watched>(w);
    _watch[w.watching(W1).opposite()].push_back(shared);
    _watch[w.watching(W2).opposite()].push_back(shared);
  }

  // from the literals in `hint` derive a RUP clause from the known set
  // the returned clause will have its premises set and be a subset of `hint`
  SATClause *rup(SATLiteralStack &hint) {
    // should be no pending propagations
    ASS(_queue.empty())

    // if there was a conflict previously, we should restore it later
    unsigned restore_conflict = conflict;

    // final literals that will be in the learned clause
    SATLiteralStack lits;

    // loop through the hint and propagate each literal's negation
    for(SATLiteral l : hint) {
      if(conflict)
        break;
      lits.push(l);
      propagate_because<true>(l.opposite(), nullptr);
    }
    // should have found a conflict at some point, otherwise CaDiCaL is misbehaving
    // this is the part that is likely to fail if CaDiCaL starts producing "true RATs" at some point
    ASS(conflict)
    auto cl = SATClause::fromStack(lits);

    // now work out which premises were needed from the justifications on the trail
    SATClauseList *premises = nullptr;
    std::unordered_set<SATLiteral> done;
    // start from the conflict: both polarities should be on the trail
    std::vector<SATLiteral> todo = {SATLiteral(conflict, false), SATLiteral(conflict, true)};
    while(!todo.empty()) {
      SATLiteral next = todo.back();
      todo.pop_back();
      if(!done.insert(next).second)
        continue;

      ASS(set(next))
      SATClause *justification = _justification[next];
      if(justification) {
        SATClauseList::push(justification, premises);
        for(SATLiteral l : justification->iter())
          if(l != next && !done.count(l.opposite()))
            todo.push_back(l.opposite());
      }
    }

    // undo the propagations done for this clause, they won't apply to the next clause
    for(SATLiteral l : _undo)
      ALWAYS(_justification.erase(l))
    _undo.clear();
    conflict = restore_conflict;

    // PropInference takes ownership of `premises`
    cl->setInference(new PropInference(premises));
    return cl;
  }

private:
  // is a particular literal set?
  bool set(SATLiteral l) const { return _justification.count(l); }

  // update a 2-watched structure to watch non-falsified literals
  // propagate if not possible
  bool update_watch(Watched &watched, Which which) {
    // invariant
    ASS_NEQ(watched.watch[W1], watched.watch[W2])
    // should have something to do
    ASS(set(watched.watching(which).opposite()))

    SATClause *cl = watched.cl;
    // find a new watch literal in cl that is not falsified...
    for(unsigned w = 0; w < cl->length(); w++)
      if(
        // ...but it should be neither of the current literals...
        w != watched.watch[W1] && w != watched.watch[W2] &&
        !set((*cl)[w].opposite())
      ) {
        // ...found it!
        watched.watch[which] = w;
        return true;
      }

    // ...failed, which means we detected a unit propagation
    _queue.push_back({(*cl)[watched.watch[1 - which]], cl});
    return false;
  }

  // enqueue `l` for propagation because of `cl`
  // `duringQuery` is
  // - false if called when adding a unit clause to the known set
  // - true if called during a RUP query
  template<bool duringQuery>
  void propagate_because(SATLiteral l, SATClause *cl) {
    ASS(_queue.empty())
    _queue.push_back({l, cl});
    propagate_all<duringQuery>();
  }

  // propagate all remaining literals in `_queue` until fixpoint
  template<bool duringQuery>
  void propagate_all() {
    while(!_queue.empty()) {
      auto [l, cl] = _queue.front();
      _queue.pop_front();
      if(set(l))
        continue;

      _justification[l] = cl;
      if(duringQuery)
        _undo.push_back(l);

      if(set(l.opposite())) {
        // conflict
        conflict = l.var();
        _queue.clear();
        return;
      }

      auto &lookup = _watch[l];
      std::vector<std::shared_ptr<Watched>> watched_clauses = std::move(lookup);
      lookup.clear();
      for(const auto &watched : watched_clauses) {
        Which which = watched->watching(W1) == l.opposite() ? W1 : W2;
        // 1. If no propagation, move the clause to a new watched literal.
        // 2. If there is a propagation during a query, keep the clause where it was -
        //    when the query is over the clause will be in the right place.
        if(update_watch(*watched, which) || duringQuery) {
          SATLiteral new_watch = watched->watching(which);
          _watch[new_watch.opposite()].push_back(watched);
        }
      }
    }
  }

  // two-watched literal structure
  std::unordered_map<SATLiteral, std::vector<std::shared_ptr<Watched>>> _watch;
  // propagation queue
  std::deque<std::pair<SATLiteral, SATClause *>> _queue;
  // a map from propagated literals to the clause that propagated them
  std::unordered_map<SATLiteral, SATClause *> _justification;
  // after a query, undo these justifications
  std::vector<SATLiteral> _undo;
};

SATClause *ProofProducingSATSolver::proof() {
#if VDEBUG
  for(SATClause *cl : iterTraits(_addedClauses->iter()))
    // should not be an empty clause in the input (?)
    ASS(cl->length())
#endif

  // for justifying steps in the proof that CaDiCaL will give us
  ReverseUnitPropagator rupper(_addedClauses);

  // open a binary DRAT stream
  std::ifstream drat(CadicalInterfacing::drat(_addedClauses));

  // the last read byte
  char byte;
  // buffer for the last DRAT clause
  SATLiteralStack lits;

  // rupper.conflict may happen _well_ before the end of the DRAT stream, so this is worth checking
  while(!rupper.conflict && drat.read(&byte, 1)) {
    char header = byte;
    ASS(header == 'a' || header == 'd')

    // DRAT's variable-length literal BS
    unsigned mapped = 0, place = 1;
    lits.reset();
    while(drat.read(&byte, 1) && byte) {
      // TODO we totally ignore 'd' for deletion - should we?
      if(header != 'a')
        continue;
      uint8_t bits = byte;
      bool more_bytes = bits & 0b10000000;
      bits &= 0b01111111;
      mapped += place * int(bits);
      if(!more_bytes) {
        lits.push((mapped % 2 ? -1 : 1) * int(mapped / 2));
        mapped = 0;
        place = 1;
      }
      else place <<= 7;
    }
    if(header != 'a')
      continue;

    SATClause *cl = rupper.rup(lits);
    rupper.addClause(cl);
  }

  // we should now have a conflict (or the DRAT proof was incomplete)
  // derive falsum from the known clauses
  ASS(rupper.conflict)
  lits.reset();
  return rupper.rup(lits);
}

}

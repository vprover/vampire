/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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

enum Which {
  W1,
  W2
};

struct Watched {
  SATClause *cl;
  unsigned watch[2];

  SATLiteral watching(Which which) { return (*cl)[watch[which]]; }
};

class RUPper {
public:
  RUPper(SATClauseList *initial) {
    for(SATClause *cl : iterTraits(initial->iter()))
      addClause(cl);
  }

  // if a conflict is detected, this is set to the (non-zero) conflict variable
  unsigned conflict = 0;

  void addClause(SATClause *cl) {
    if(conflict)
      return;

    std::cout << "add: " << *cl << '\n';
    // special-case units
    if(cl->length() == 1) {
      _queue.push_back({(*cl)[0], cl});
      propagate<false>();
      return;
    }

    // initially watch the first two literals, which may not be correct
    Watched w { cl, {0, 1} };

    // correct the watched literals
    for(Which which : {W1, W2})
      // if a watched literal is not satisfied, update the watch
      if(set(w.watching(which).opposite()) && !update_watch<false>(w, which)) {
        // if that fails, can propagate
        propagate<false>();
        return;
      }

    auto shared = std::make_shared<Watched>(w);
    _watch[w.watching(W1).opposite()].push_back(shared);
    _watch[w.watching(W2).opposite()].push_back(shared);
  }

  SATClauseList *rup(SATLiteralStack &hint) {
    SATClauseList *result = nullptr;
    ASS(!conflict)
    for(SATLiteral l : hint)
      _queue.push_back({l.opposite(), nullptr});
    propagate<true>();
    // TODO could notice that some literals aren't used and derive a shorter proof clause
    ASS(conflict)

    std::unordered_set<SATLiteral> done;
    std::vector<SATLiteral> todo = {SATLiteral(conflict, false), SATLiteral(conflict, true)};
    while(!todo.empty()) {
      SATLiteral next = todo.back();
      todo.pop_back();
      done.insert(next);

      ASS(set(next))
      SATClause *justification = _justification[next];
      if(justification) {
        SATClauseList::push(justification, result);
        for(SATLiteral l : justification->iter())
          if(l != next && !done.count(l.opposite()))
            todo.push_back(l.opposite());
      }
    }

    for(SATLiteral l : _undo)
      ALWAYS(_justification.erase(l))
    _undo.clear();
    conflict = 0;

    return result;
  }

private:
  bool set(SATLiteral l) const { return _justification.count(l); }

  // TODO move to Watched
  template<bool duringQuery>
  bool update_watch(Watched &watched, Which which) {
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

  template<bool duringQuery>
  void propagate() {
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

      // TODO don't insert a new entry here
      auto &lookup = _watch[l];
      std::vector<std::shared_ptr<Watched>> watched_clauses = std::move(lookup);
      lookup.clear();
      for(const auto &watched : watched_clauses) {
        Which which = watched->watching(W1) == l.opposite() ? W1 : W2;
        // 1. If no propagation, move the clause to a new watched literal.
        // 2. If there is a propagation during a query, keep the clause where it was -
        //    when the query is over the clause will be in the right place.
        if(update_watch<duringQuery>(*watched, which) || duringQuery) {
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


void ProofProducingSATSolver::proof() {
  // TODO deal with the empty-clause case
  RUPper rupper(_addedClauses);

  std::ifstream drat(CadicalInterfacing::drat(_addedClauses));
  char byte;
  SATLiteralStack lits;
  while(!rupper.conflict && drat.read(&byte, 1)) {
    char header = byte;
    ASS(header == 'a' || header == 'd')

    unsigned mapped = 0, place = 1;
    lits.reset();
    while(drat.read(&byte, 1) && byte) {
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

    if(header == 'a') {
      SATClauseList *parents = rupper.rup(lits);
      auto cl = SATClause::fromStack(lits);
      for(SATClauseList *current = parents; current; current = current->tail())
        std::cout << *current->head() << '\n';
      std::cout << "---------------------------------------------------------\n";
      std::cout << *cl << "\n\n\n";
      rupper.addClause(cl);
      // TODO check rup to get parents
    }
    // TODO deletion
  }

  ASS(rupper.conflict)
}

}

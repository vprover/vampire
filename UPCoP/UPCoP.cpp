/*
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file UPCoP.cpp
 * main UPCoP procedures
 */

#include "UPCoP.hpp"

#include <algorithm>
#include "cadical.hpp"

#include "Debug/Assertion.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Backtrackable.hpp"

std::ostream &log() { return std::cout << "% "; }

// some data about a copy of a clause in the matrix
struct Copy {
  // SAT variable representing selecting this clause
  int var;
  // range of literal positions this clause occupies
  unsigned start, end;
};

// some data about a literal in the matrix
struct Position {
  // the literal at this position in the matrix
  Literal *literal;
  // the clause copy this index belongs to, indexing into `Matrix::copies`
  unsigned copy;
  // possible connections to this literal
  std::vector<unsigned> connections;

  Position(Literal *literal, unsigned copy)
    : literal(literal), copy(copy) {}
};

// a connection between two literals
struct Connection {
  // SAT variable representing making this connection
  int var;
  // the positions connected, indexing into `Matrix::positions`
  unsigned positions[2];
};

enum class Action {
  CONNECT,
  SELECT,
  UNUSED
};

// used to determine what a SAT variable means
struct Demux {
  // what does this do?
  Action action;
  // index into something depending on `action`
  unsigned index;
};

// something to keep in the term index
struct Indexed {
  // the indexed literal
  Literal *literal;
  // index into `Matrix::positions`
  unsigned position;

  // machinery for LiteralSubstitutionTree
  Literal *key() const { return literal; }
  bool operator==(const Indexed &other) const
  { return position == other.position; }
  bool operator<(const Indexed &other) const
  { return position < other.position; }
  bool operator>(const Indexed &other) const
  { return position > other.position; }
};

std::ostream &operator<<(std::ostream &out, Indexed indexed) {
  return out << indexed.literal->toString() << " at position " << indexed.position;
}

struct Matrix {
  // clause copies
  std::vector<Copy> copies;
  // literal positions
  std::vector<Position> positions;
  // connections
  std::vector<Connection> connections;
  // SAT variable information
  std::vector<Demux> demux;

  // number of first-order variables used so far
  unsigned offset = 0;

  // literal index
  Indexing::LiteralSubstitutionTree<Indexed> index;

  Matrix() {
    // offset all entries by one as SAT variable 0 is unused
    demux.push_back({Action::UNUSED, 0});
  }

  // get a pair of literals corresponding to a SAT variable
  std::pair<Literal *, Literal *> connection_literals(int assigned) {
    ASS_G(assigned, 0)
    ASS(demux[assigned].action == Action::CONNECT);
    unsigned index = demux[assigned].index;
    const Connection &connection = connections[index];
    ASS_EQ(connection.var, assigned)
    Literal *k = positions[connection.positions[0]].literal;
    Literal *l = positions[connection.positions[1]].literal;
    return {k, l};
  }

  // increase the number of copies of `cl` by one
  int amplify(CaDiCaL::Solver &solver, Clause *cl) {
    log() << "amplify: " << cl->toString() << '\n';

    // the position in `copies` that this clause will occupy
    unsigned copy_index = copies.size();
    // the start of the literal positions that this clause will occupy
    unsigned position_start = positions.size();

    // variable renaming applied to clause to produce fresh variables
    Renaming renaming(offset);

    // first pass: insert literals, find connections to others
    for(unsigned i = 0; i < cl->length(); i++) {
      // normalise `l` to get `renamed`
      Literal *l = (*cl)[i];
      renaming.normalizeVariables(l);
      Literal *renamed = renaming.apply(l);
      Position position(renamed, copy_index);

      // the position this literal will occupy
      unsigned position_index = positions.size();

      // all the previous possible connections
      auto unifiers = index.getUnifications(
        l,
        /*complementary=*/true,
        /*retrieveSubstitutions=*/false
      );
      while(unifiers.hasNext()) {
        // the new connection
        unsigned other_index = unifiers.next().data->position;

        // add demux
        int var = demux.size();
        unsigned connection_index = connections.size();
        demux.push_back({Action::CONNECT, connection_index});
        solver.add_observed_var(var);
        solver.phase(-var);

        // add connection
        connections.push_back({var, {other_index, position_index}});

        // add the new connection to both positions
        positions[other_index].connections.push_back(connection_index);
        position.connections.push_back(connection_index);
      }
      positions.emplace_back(std::move(position));
    }
    // the end of the literal positions
    unsigned position_end = positions.size();

    // bump offset for the next clause
    offset = renaming.nextVar();

    // second pass: insert literals into the index
    for(unsigned i = 0; i < cl->length(); i++) {
      Literal *literal = (*cl)[i];
      unsigned position = position_start + i;
      Indexed indexed { literal, position };
      index.insert(indexed);
    }

    // create selectors and demux
    int selector = demux.size();
    demux.push_back({Action::SELECT, copy_index});
    solver.phase(-selector);
    copies.push_back({selector, position_start, position_end});

    return selector;
  }
};

struct Propagator: public CaDiCaL::ExternalPropagator {
  // the matrix
  Matrix &matrix;
  // current substitution
  RobSubstitution substitution;
  // trail of SAT variables: only contains positive connections
  std::vector<int> trail;
  // reason/conflict clause, if any
  std::vector<int> reason;

  // create a decision level on construction, backtrack a decision level on destruction
  struct Level {
    // parent propagator
    Propagator &propagator;
    // for the trail
    unsigned trail;
    // for the substitution
    std::unique_ptr<BacktrackData> substitution;

    // allow moves, setting `substitution` to be nullptr
    Level(Level &&) = default;

    Level(Propagator &propagator) :
      propagator(propagator),
      trail(propagator.trail.size()),
      substitution(new BacktrackData())
    {
      propagator.substitution.bdRecord(*substitution);
    }

    ~Level() {
      // have been moved-from, ignore
      if(!substitution)
        return;

      ASS_LE(trail, propagator.trail.size())
      propagator.trail.resize(trail);
      substitution->backtrack();
      propagator.substitution.bdDone();
    }
  };

  // decision levels
  std::vector<Level> levels;

  Propagator(Matrix &matrix) : matrix(matrix) {}

  ~Propagator() {
    // undo substitutions in order
    while(!levels.empty())
      levels.pop_back();
  }

  void notify_assignment(int assigned, bool fixed) final {
    // do nothing on variables assigned false
    // also do nothing when there is a conflict but we didn't tell CaDiCaL yet
    if(assigned < 0 || !reason.empty())
      return;

    auto [k, l] = matrix.connection_literals(assigned);
    if(!substitution.unify(TermList(k), 0, TermList(l), 0)) {
      compute_reason(assigned);
      return;
    }
    trail.push_back(assigned);
  }

  // fill out `reason` given that `assigned` caused a unification failure
  void compute_reason(int assigned) {
    // conflicting literal guaranteed to be a reason
    reason.push_back(-assigned);

    while(true) {
      RobSubstitution attempt;
      for(int assigned : reason) {
        auto [k, l] = matrix.connection_literals(-assigned);
        if(!attempt.unify(TermList(k), 0, TermList(l), 0))
          // `reason` contradictory, exit
          return;
      }

      // will always exit since the trail as a whole cannot be unified
      for(int assigned : trail) {
        auto [k, l] = matrix.connection_literals(assigned);
        if(!attempt.unify(TermList(k), 0, TermList(l), 0)) {
          // this index definitely necessary
          reason.push_back(-assigned);
          break;
        }
      }
    }
  }

  void notify_new_decision_level() final {
    levels.emplace_back(*this);
  }

  void notify_backtrack(size_t level) final {
    reason.clear();
    while(levels.size() > level)
      levels.pop_back();
  }

  bool cb_check_found_model(const std::vector<int> &model) final {
    return true;
  }

  bool cb_has_external_clause() final { return !reason.empty(); }

  int cb_add_external_clause_lit() final {
    if(reason.empty())
      return 0;
    int lit = reason.back();
    reason.pop_back();
    return lit;
  }
};

MainLoopResult UPCoP::runImpl() {
  CaDiCaL::Solver solver;
  Matrix matrix;
  Propagator propagator(matrix);
  solver.connect_external_propagator(&propagator);
  log() << env.options->inputFile() << '\n';

  // add initial clauses and add start constraint
  UnitList::Iterator units(_prb.units());
  while(units.hasNext()) {
    Clause *cl = units.next()->asClause();
    int selector = matrix.amplify(solver, cl);
    if(cl->inference().derivedFromGoal()) {
      solver.add(selector);
    }
  }
  solver.add(0);

  // add connection-implies-selector constraints
  for(const Connection &connection : matrix.connections) {
    for(unsigned position : connection.positions) {
      solver.add(-connection.var);
      solver.add(matrix.copies[matrix.positions[position].copy].var);
      solver.add(0);
    }
  }

  // add fully-connected constraints
  for(const Copy &copy : matrix.copies)
    for(unsigned index = copy.start; index < copy.end; index++) {
      solver.add(-copy.var);
      for(unsigned connection : matrix.positions[index].connections)
        solver.add(matrix.connections[connection].var);
      solver.add(0);
    }

  int result = solver.solve();
  log() << "result: " << result << '\n';
  return Statistics::REFUTATION_NOT_FOUND;
}

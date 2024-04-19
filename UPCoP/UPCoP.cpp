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
template<typename T>
std::ostream &operator<<(std::ostream &out, const std::vector<T> &v) {
  out << '[';
  if(!v.empty())
    out << v[0];
  for(unsigned i = 1; i < v.size(); i++)
    out << ' ' << v[i];
  out << ']';
  return out;
}

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
  // did we make this connection?
  bool made;
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
        connections.push_back({var, {other_index, position_index}, false});

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
    solver.add_observed_var(selector);
    solver.phase(-selector);
    demux.push_back({Action::SELECT, copy_index});
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
    // do nothing when:
    // - variable is assigned false
    // - when there is a conflict but we didn't tell CaDiCaL yet
    // - when it's not a variable representing a connection
    if(assigned < 0 || !reason.empty() || matrix.demux[assigned].action != Action::CONNECT)
      return;

    auto [k, l] = matrix.connection_literals(assigned);
    if(!substitution.unify(TermList(k), 0, TermList(l), 0)) {
      compute_unification_reason(assigned);
      return;
    }
    trail.push_back(assigned);
  }

  // fill out `reason` given that `assigned` caused a unification failure
  void compute_unification_reason(int assigned) {
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
    ASS(reason.empty())

    auto path = find_path(model);
    // no path found, we're done
    if(path.empty())
      return true;

    // set `made` field in connections for later
    for(Connection &connection : matrix.connections)
      connection.made = false;
    for(int assigned : model)
      if(assigned > 0 && matrix.demux[assigned].action == Action::CONNECT)
        matrix.connections[matrix.demux[assigned].index].made = true;

    // iterate through all combinations (k > 1) of the path
    ASS_G(path.size(), 1)
    std::vector<bool> combination(path.size(), false);
    for(unsigned k = 2; k <= path.size(); k++) {
      // set the first k bits 1, rest 0
      for(unsigned i = 0; i < path.size(); i++) combination[i] = false;
      for(unsigned i = 0; i < k; i++) combination[i] = true;

      // iterate through all n-choose-k combinations by moving the bits around
      while(true) {
        // check whether this combination is a reason for the open path
        std::vector<unsigned> subpath;
        for(unsigned i = 0; i < path.size(); i++)
          if(combination[i])
            subpath.push_back(path[i]);
        if(compute_connection_reason(subpath))
          return false;

        // find the first set bit
        unsigned start = 0;
        while(!combination[start]) start++;
        // find the rightmost bit in this cluster of ones
        unsigned end = start + 1;
        while(end < path.size() && combination[end]) end++;
        ASS(combination[start])
        ASS(!combination[end])
        ASS_LE(end - start, k)

        // all the ones are at the end, done here
        if(end == path.size())
          break;

        unsigned ones = end - start;
        // move the rightmost bit over one position
        combination[end - 1] = false;
        combination[end] = true;
        // reset all the other bits to the start
        for(unsigned i = start; i < end - 1; i++) combination[i] = false;
        for(unsigned i = 0; i < ones - 1; i++) combination[i] = true;
      }
    }

    // ought to have found a reason by now
    ASSERTION_VIOLATION
  }

  // find a path through the matrix, empty if there is no path
  std::vector<unsigned> find_path(const std::vector<int> &model) {
    // auxiliary CaDiCaL used to find the path
    // TODO could do proof reconstruction here with Vampire's SAT solver
    CaDiCaL::Solver pathfinder;

    // selected clauses computed from `model`
    std::vector<unsigned> selected;

    for(int assigned : model) {
      if(assigned < 0)
        continue;

      auto [action, index] = matrix.demux[assigned];
      if(action == Action::SELECT) {
        selected.push_back(index);
        const Copy &copy = matrix.copies[index];
        // at least one literal from every clause
        for(unsigned i = copy.start; i < copy.end; i++)
          // variables offset by 1 as 0 unusable
          pathfinder.add(i + 1);
        pathfinder.add(0);
      }
      else {
        const Connection &connection = matrix.connections[index];
        // both sides of a connection cannot be selected
        for(auto position : connection.positions)
          // variables offset by 1 as 0 unusable
          pathfinder.add(-(position + 1));
        pathfinder.add(0);
      }
    }

    // no path exists
    if(pathfinder.solve() == CaDiCaL::UNSATISFIABLE)
      return std::vector<unsigned>();

    // read the path off pathfinder's model
    std::vector<unsigned> path;
    for(unsigned index : selected) {
      const Copy &copy = matrix.copies[index];
      for(unsigned i = copy.start; i < copy.end; i++)
        if(pathfinder.val(i + 1) == i + 1) {
          path.push_back(i);
          break;
        }
    }
    return path;
  }

  // set `reason` and return true if `subpath` is a reason why we don't have a proof
  bool compute_connection_reason(std::vector<unsigned> &subpath) {
    ASS(reason.empty())

    // given the copies in the subpath...
    std::vector<unsigned> copies;
    for(unsigned position : subpath) {
      unsigned copy = matrix.positions[position].copy;
      copies.push_back(copy);
      reason.push_back(-matrix.copies[copy].var);
    }

    // some element in the subpath needs to connect to *something* more
    for(unsigned i = 0; i < subpath.size(); i++) {
      unsigned position_index = subpath[i];
      const Position &position = matrix.positions[position_index];
      for(unsigned connection_index : position.connections) {
        const Connection &connection = matrix.connections[connection_index];
        // the other end of the connection
        unsigned other = connection.positions[0] == position_index
          ? connection.positions[1]
          : connection.positions[0];
        unsigned other_copy = matrix.positions[other].copy;

        // ignore connections within the submatrix
        if(find(copies.begin(), copies.end(), other_copy) != copies.end())
          // but not on the subpath
          if(find(subpath.begin() + i + 1, subpath.end(), other) == subpath.end())
            continue;

        // check that we didn't already make the connection
        if(connection.made) {
          reason.clear();
          return false;
        }

        reason.push_back(connection.var);
      }
    }

    log() << reason << '\n';
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
  for(const Connection &connection : matrix.connections)
    for(unsigned position : connection.positions) {
      solver.add(-connection.var);
      solver.add(matrix.copies[matrix.positions[position].copy].var);
      solver.add(0);
    }

  // add fully-connected constraints
  for(const Copy &copy : matrix.copies)
    for(unsigned index = copy.start; index < copy.end; index++) {
      solver.add(-copy.var);
      for(unsigned connection : matrix.positions[index].connections)
        solver.add(matrix.connections[connection].var);
      solver.add(0);
    }

  if(solver.solve() == CaDiCaL::SATISFIABLE)
    log() << "SZS status Theorem\n";
  else
    log() << "SZS status Incomplete\n";

  return Statistics::REFUTATION_NOT_FOUND;
}

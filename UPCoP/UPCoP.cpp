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
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/SAT2FO.hpp"

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

template<typename T>
std::ostream &operator<<(std::ostream &out, const std::unordered_set<T> &s) {
  out << '{';
  if(!s.empty())
    out << *s.begin();
  for(auto &it = ++s.begin(); it != s.end(); it++)
    out << ' ' << *it;
  out << '}';
  return out;
}

// map every variable to X0
static struct {
  TermList apply(unsigned x) { return TermList(0, false); }
} X0;

// some data about a copy of a clause in the matrix
struct Copy {
  // original clause
  Clause *original;
  // SAT variable representing selecting this clause
  int var;
  // range of literal positions this clause occupies
  unsigned start, end;

  unsigned length() const { return end - start; }
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
    solver.add_observed_var(selector);
    solver.phase(-selector);
    demux.push_back({Action::SELECT, copy_index});
    copies.push_back({cl, selector, position_start, position_end});

    return selector;
  }
};

struct Propagator: public CaDiCaL::ExternalPropagator {
  // the matrix
  Matrix &matrix;
  // current substitution
  RobSubstitution substitution;
  // SAT variables for selected clauses so far
  std::vector<int> selected;
  // SAT variables for connections made so far
  std::vector<int> connections;
  // reason/conflict clause, if any
  std::vector<int> reason;
  // auxiliary SAT solver for finding paths
  MinisatInterfacing pathfinder;
  // bijection from (substituted, grounded) literals to SAT variables
  SAT2FO sat2fo;

  // create a decision level on construction, backtrack a decision level on destruction
  struct Level {
    // parent propagator
    Propagator &propagator;
    // where to reset `propagator.selected` to
    unsigned selected;
    // where to reset `propagator.connections` to
    unsigned connections;
    // for the substitution
    std::unique_ptr<BacktrackData> substitution;

    // allow moves, setting `substitution` to be nullptr
    Level(Level &&) = default;

    Level(Propagator &propagator) :
      propagator(propagator),
      selected(propagator.selected.size()),
      connections(propagator.connections.size()),
      substitution(new BacktrackData())
    {
      propagator.substitution.bdRecord(*substitution);
    }

    ~Level() {
      // have been moved-from, ignore
      if(!substitution)
        return;

      ASS_LE(selected, propagator.selected.size())
      propagator.selected.resize(selected);
      ASS_LE(connections, propagator.connections.size())
      propagator.connections.resize(connections);
      substitution->backtrack();
      propagator.substitution.bdDone();
    }
  };

  // decision levels
  std::vector<Level> levels;

  Propagator(Matrix &matrix) : matrix(matrix), pathfinder(*env.options) {}

  ~Propagator() {
    // undo substitutions in order
    while(!levels.empty())
      levels.pop_back();
  }

  void notify_assignment(int assigned, bool fixed) final {
    // should only get fixed assignments at decision level 0 (without chrono)
    ASS(!fixed || levels.empty())

    // do nothing when variable is assigned false,
    // or there is a conflict we didn't tell CaDiCaL about yet
    if(assigned < 0 || !reason.empty())
      return;

    auto [action, index] = matrix.demux[assigned];
    if(action == Action::SELECT)
      selected.push_back(assigned);
    else {
      ASS(action == Action::CONNECT)
      connections.push_back(assigned);
      // unify the literals corresponding to the connection
      auto [k, l] = matrix.connection_literals(assigned);
      if(!substitution.unify(TermList(k), 0, TermList(l), 0))
        // unification failed, learn a conflict clause
        compute_unification_reason(assigned);
    }
  }

  // fill out `reason` given that `assigned` caused a unification failure
  void compute_unification_reason(int assigned) {
    ASS(reason.empty())

    // conflicting literal guaranteed to be a reason
    reason.push_back(-assigned);

    while(true) {
      RobSubstitution attempt;
      for(int assigned : reason) {
        auto [k, l] = matrix.connection_literals(-assigned);
        if(!attempt.unify(TermList(k), 0, TermList(l), 0)) {
          // `reason` contradictory, exit
          //log() << "unification: " << reason << '\n';
          return;
        }
      }

      // will always exit since the totality of connections cannot be unified
      for(int assigned : connections) {
        auto [k, l] = matrix.connection_literals(assigned);
        if(!attempt.unify(TermList(k), 0, TermList(l), 0)) {
          // this index definitely necessary
          reason.push_back(-assigned);
          break;
        }
      }
      // TODO do this more efficiently, backtracking over attempts
    }
  }

  void notify_new_decision_level() final { levels.emplace_back(*this); }

  void notify_backtrack(size_t level) final {
    reason.clear();
    while(levels.size() > level)
      levels.pop_back();
  }

  bool cb_check_found_model(const std::vector<int> &model) final {
    ASS(reason.empty())

    // find a path through the fully-connected matrix
    auto path = find_path();
    ASS_G(path.size(), 0)

    // set of copies selected
    std::unordered_set<unsigned> members;
    for(int selected : selected) {
      // if we have selected these clauses...
      reason.push_back(-selected);
      members.insert(matrix.demux[selected].index);
    }

    // either there should be a connection on the path,
    // or there should be a connection outside the selected copies
    for(unsigned position_index : path) {
      const Position &position = matrix.positions[position_index];
      for(unsigned connection_index : position.connections) {
        const Connection &connection = matrix.connections[connection_index];
        auto [ki, ji] = connection.positions;
        ASS(position_index == ki || position_index == ji)

        // intra-path connection, no further questions
        if(path.count(ki) && path.count(ji)) {
          // avoid duplicate connections
          if(ki == position_index)
            reason.push_back(connection.var);
          continue;
        }

        unsigned other_position = ki == position_index ? ji : ki;
        unsigned other_copy = matrix.positions[other_position].copy;
        // connection from the path to somewhere else in the selected copies, skip
        if(members.count(other_copy))
          continue;

        reason.push_back(connection.var);
      }
    }

    //log() << "final: " << reason << '\n';
    return false;
  }

  // find a path through the matrix, returning the sequence of positions
  std::unordered_set<unsigned> find_path() {
    // grounded versions of the selected clauses
    std::vector<std::pair<const Copy &, Clause *>> grounded;
    // ground all selected clauses and feed them to `pathfinder`
    for(int selected : selected) {
      const Copy &copy = matrix.copies[matrix.demux[selected].index];
      // make a Vampire clause for grounding - useful for proof printing
      Clause *ground = new (copy.length()) Clause(
        copy.length(),
        NonspecificInference1(InferenceRule::INSTANTIATION, copy.original)
      );
      // don't ask
      ground->incRefCnt();

      // fill out `ground`
      for(unsigned i = 0; i < copy.length(); i++) {
        const Position &position = matrix.positions[copy.start + i];
        // apply the substitution
        Literal *substituted = substitution.apply(position.literal, 0);
        // map all remaining variables to X0
        // (just barely avoids sortedness problems)
        (*ground)[i] = SubstHelper::apply(substituted, X0);
      }
      grounded.push_back({copy, ground});

      // get a SAT version of `ground`
      SATClause *sat = sat2fo.toSAT(ground);
      pathfinder.ensureVarCount(sat2fo.maxSATVar());
      // tautology
      // TODO prevent this happening in the first place
      if(sat)
        pathfinder.addClause(sat);
    }

    // no path exists, we're done - emit a proof
    if(pathfinder.solve(UINT_MAX) == SATSolver::UNSATISFIABLE) {
      SATClause* refutation = pathfinder.getRefutation();
      UnitList* premises = SATInference::getFOPremises(refutation);
      Clause* empty = Clause::fromIterator(
        LiteralIterator::getEmpty(),
        FromSatRefutation(
          InferenceRule::AVATAR_REFUTATION,
          premises,
          pathfinder.getRefutationPremiseList()
        )
      );
      throw MainLoop::RefutationFoundException(empty);
    }

    // read the path off pathfinder's model
    std::unordered_set<unsigned> path;
    for(auto [copy, ground] : grounded)
      for(unsigned i = 0; i < ground->length(); i++) {
        SATLiteral lit = sat2fo.toSAT((*ground)[i]);
        if(
          ( lit.polarity() && pathfinder.getAssignment(lit.var()) == SATSolver::TRUE) ||
          (!lit.polarity() && pathfinder.getAssignment(lit.var()) == SATSolver::FALSE)
          // ignore don't-cares and assume they have the wrong polarity
        ) {
          path.insert(copy.start + i);
          break;
        }
      }
    return path;
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
  // chrono allows fixed assignments at non-zero decision levels - eek!
  solver.set("chrono", 0);

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

  // should throw if we find a proof
  ALWAYS(solver.solve() != CaDiCaL::SATISFIABLE)
  log() << "SZS status Incomplete\n";
  return Statistics::REFUTATION_NOT_FOUND;
}

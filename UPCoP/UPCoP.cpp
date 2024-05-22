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
  // possible connections with this literal
  std::vector<unsigned> connections;

  Position(Literal *literal, unsigned copy)
    : literal(literal), copy(copy) {}
};

// a connection between two literals
struct Connection {
  // the positions connected, indexing into `Matrix::positions`
  unsigned positions[2];
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

  Matrix() {
    // offset `connections` by 1 so it can be indexed by SAT variables
    connections.push_back({0, 0});
  }

  // number of first-order variables used so far
  unsigned offset = 0;

  // literal index
  Indexing::LiteralSubstitutionTree<Indexed> index;

  // get a pair of literals corresponding to a SAT variable
  std::pair<Literal *, Literal *> connection_literals(int assigned) const {
    ASS_G(assigned, 0)
    const Connection &connection = connections[assigned];
    Literal *k = positions[connection.positions[0]].literal;
    Literal *l = positions[connection.positions[1]].literal;
    return {k, l};
  }

  // increase the number of copies of `cl` by one
  void amplify(CaDiCaL::Solver &solver, Clause *cl) {
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

        // skip ground connections, they do nothing
        if(l->ground() && positions[other_index].literal->ground())
          continue;

        // add connection
        int connection = connections.size();
        solver.add_observed_var(connection);
        solver.phase(connection);
        connections.push_back({other_index, position_index});

        // add the new connection to both positions
        positions[other_index].connections.push_back(connection);
        position.connections.push_back(connection);
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

    // finally add the copy
    copies.push_back({cl, position_start, position_end});
  }
};

struct Propagator: public CaDiCaL::ExternalPropagator {
  // the matrix
  const Matrix &matrix;
  // current substitution
  RobSubstitution substitution;
  // connections made so far
  std::vector<int> connections;
  // if there is a reason/conflict clause to learn
  bool reason_set = false;
  // reason/conflict clause
  std::vector<int> reason;
  // random source
  std::mt19937 rng;

  // create a decision level on construction, backtrack a decision level on destruction
  struct Level {
    // parent propagator
    Propagator &propagator;
    // where to reset `propagator.connections` to
    unsigned connections;
    // for the substitution
    std::unique_ptr<BacktrackData> substitution;

    // allow moves, setting `substitution` to be nullptr
    Level(Level &&) = default;

    Level(Propagator &propagator) :
      propagator(propagator),
      connections(propagator.connections.size()),
      substitution(new BacktrackData())
    {
      propagator.substitution.bdRecord(*substitution);
    }

    ~Level() {
      // have been moved-from, ignore
      if(!substitution)
        return;

      ASS_LE(connections, propagator.connections.size())
      propagator.connections.resize(connections);
      substitution->backtrack();
      propagator.substitution.bdDone();
    }
  };

  // decision levels
  std::vector<Level> levels;

  Propagator(const Matrix &matrix) : matrix(matrix) {}

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
    if(assigned < 0 || reason_set)
      return;

    connections.push_back(assigned);
    // unify the literals corresponding to the connection
    auto [k, l] = matrix.connection_literals(assigned);
    if(!substitution.unify(TermList(k), 0, TermList(l), 0))
      // unification failed, learn a conflict clause
      compute_unification_reason(assigned);
  }

  // fill out `reason` given that `assigned` caused a unification failure
  void compute_unification_reason(int assigned) {
    ASS(!reason_set)
    ASS(reason.empty())

    reason_set = true;
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
    reason_set = false;
    reason.clear();
    while(levels.size() > level)
      levels.pop_back();
  }

  bool cb_check_found_model(const std::vector<int> &model) final {
    ASS(!reason_set)
    ASS(reason.empty())
    reason_set = true;

#if 0
    // ooooh stars pretty!
    auto &out = log();
    for(int assign : model)
      out << (assign < 0 ? ' ' : '*');
    out << '\n';
#endif

    // find a path through the fully-connected matrix
    auto path = find_path();
    ASS_EQ(path.size(), matrix.copies.size())

    // at least one connection must be made along this path
    for(unsigned position_index : path) {
      const Position &position = matrix.positions[position_index];
      for(unsigned var : position.connections) {
        const Connection &connection = matrix.connections[var];
        auto [k, l] = connection.positions;
        ASS(position_index == k || position_index == l)

        if(
          // connection along the path
          path.count(k) && path.count(l) &&
          // avoid duplicate connections
          k == position_index
        )
          reason.push_back(var);
      }
    }

    //log() << "final: " << reason << '\n';
    return false;
  }

  // find a path through the matrix, returning a set of positions
  std::unordered_set<unsigned> find_path() {
    // auxiliary SAT solver for finding paths
    MinisatInterfacing pathfinder(*env.options);
    // bijection from (substituted, grounded) literals to SAT variables
    SAT2FO sat2fo;

    // grounded versions of the selected clauses
    std::vector<Clause *> grounded;
    // SAT versions of `grounded`
    std::vector<SATClause *> sats;

    // ground all clauses and feed them to `pathfinder`
    for(const Copy &copy : matrix.copies) {
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
      grounded.push_back(ground);

      // get a SAT version of `ground`
      SATClause *sat = sat2fo.toSAT(ground);
      pathfinder.ensureVarCount(sat2fo.maxSATVar());
      // tautology: can happen even if tautologies eliminated
      // consider e.g. p(Y) | ~p(Z), which is grounded to p(X0) | ~p(X0)
      if(sat) {
        pathfinder.addClause(sat);
        sats.push_back(sat);
      }
    }

    // usually better to try lots of different paths
    pathfinder.randomizeForNextAssignment(sat2fo.maxSATVar());

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
    ASS_EQ(grounded.size(), matrix.copies.size())

    // to choose a random satisfied literal in clauses
    std::vector<unsigned> random_order;

    // read the path off pathfinder's model
    std::unordered_set<unsigned> path;
    for(unsigned i = 0; i < matrix.copies.size(); i++) {
      const Copy &copy = matrix.copies[i];
      Clause *ground = grounded[i];

      // randomise order of iteration
      random_order.clear();
      while(random_order.size() < ground->length())
        random_order.push_back(random_order.size());
      shuffle(random_order.begin(), random_order.end(), rng);

      for(unsigned j : random_order) {
        SATLiteral lit = sat2fo.toSAT((*ground)[j]);
        ASS_NEQ(pathfinder.getAssignment(lit.var()), SATSolver::DONT_CARE)
        if(
          ( lit.polarity() && pathfinder.getAssignment(lit.var()) == SATSolver::TRUE) ||
          (!lit.polarity() && pathfinder.getAssignment(lit.var()) == SATSolver::FALSE)
        ) {
          path.insert(copy.start + j);
          break;
        }
      }
    }

    // free clauses, we won't need them for a proof
    for(SATClause *cl : sats)
      cl->destroy();
    for(Clause *cl : grounded)
      cl->destroy();

    return path;
  }

  bool cb_has_external_clause() final { return reason_set; }

  int cb_add_external_clause_lit() final {
    reason_set = false;
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

  // add initial clauses
  UnitList::Iterator units(_prb.units());
  while(units.hasNext())
    matrix.amplify(solver, units.next()->asClause());

  // should throw if we find a proof
  ALWAYS(solver.solve() != CaDiCaL::SATISFIABLE)
  log() << "SZS status Incomplete\n";
  return Statistics::REFUTATION_NOT_FOUND;
}

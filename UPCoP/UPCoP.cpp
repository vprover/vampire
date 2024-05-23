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
#include "DP/SimpleCongruenceClosure.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Backtrackable.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/SAT2FO.hpp"
#include <cstdint>

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

// a rigid copy of a clause
struct Copy {
  // original clause
  Clause *original = nullptr;
  // renamed literals
  std::vector<Literal *> literals;
};

// a connection between two terms
struct Connection {
  // the two terms to unify
  TermList unify[2];
};

template<>
struct std::hash<Connection> {
  size_t operator()(const Connection &connection) const {
    std::hash<uint64_t> hasher;
    return
      hasher(connection.unify[0].content()) ^
      hasher(connection.unify[1].content());
  }
};

template<>
struct std::equal_to<Connection> {
  bool operator()(const Connection &left, const Connection &right) const {
    return
      (left.unify[0] == right.unify[0] && left.unify[1] == right.unify[1]) ||
      (left.unify[0] == right.unify[1] && left.unify[1] == right.unify[0]);
  }
};

// something to keep in the term index
struct Predicate {
  // the indexed literal
  Literal *literal;
  Predicate(Literal *literal) : literal(literal) {}

  // machinery for LiteralSubstitutionTree
  Literal *key() const { return literal; }
  bool operator==(const Predicate &other) const
  { return literal->getId() == other.literal->getId(); }
  bool operator<(const Predicate &other) const
  { return literal->getId() < other.literal->getId(); }
  bool operator>(const Predicate &other) const
  { return literal->getId() > other.literal->getId(); }
};

std::ostream &operator<<(std::ostream &out, const Predicate &indexed) {
  return out << indexed.literal->toString();
}

struct Matrix {
  // clause copies
  std::vector<Copy> copies;
  // map from connections to SAT variables
  std::unordered_map<Connection, int> conn2sat;
  // map from SAT variables to connections
  std::vector<Connection> sat2conn;

  // number of first-order variables used so far
  unsigned offset = 0;
  // index for non-equality predicates
  Indexing::LiteralSubstitutionTree<Predicate> predicate_index;

  Matrix() {
    // offset by 1 as 0 is not a valid SAT variable
    sat2conn.push_back({TermList::empty(), TermList::empty()});
  }

  // increase the number of copies of `cl` by one
  void amplify(CaDiCaL::Solver &solver, Clause *cl) {
    // the new clause
    Copy copy;
    copy.original = cl;

    // variable renaming applied to produce fresh variables
    Renaming renaming(offset);

    // first pass: insert literals, find connections to others
    for(unsigned i = 0; i < cl->length(); i++) {
      // normalise `l` and insert it into `copy`
      Literal *l = (*cl)[i];
      renaming.normalizeVariables(l);
      l = renaming.apply(l);
      copy.literals.push_back(l);

      // all the previous possible connections
      auto unifiers = predicate_index.getUnifications(
        l,
        /*complementary=*/true,
        /*retrieveSubstitutions=*/false
      );
      while(unifiers.hasNext()) {
        // the literal to connect to
        Literal *k = unifiers.next().data->literal;

        // skip ground connections, they do nothing
        if(l->ground() && k->ground())
          continue;

        // add connection
        int fresh = sat2conn.size();
        Connection connection {TermList(k), TermList(l)};
        // if not seen before...
        if(conn2sat.insert({connection, fresh}).second) {
          sat2conn.push_back(connection);
          // we want to know about assignments
          solver.add_observed_var(fresh);
          // heuristic: more connections good
          solver.phase(fresh);
        }
      }
    }

    // bump offset for the next clause
    offset = renaming.nextVar();
    // second pass: insert literals into the index
    for(Literal *l : copy.literals)
      predicate_index.insert(l);
    // finally add the copy
    copies.emplace_back(std::move(copy));
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
  // ordering (for SimpleCongruenceClosure?!)
  OrderingSP ordering;

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

  Propagator(Problem &problem, const Matrix &matrix) :
    matrix(matrix),
    ordering(Kernel::Ordering::create(problem, *env.options))
  {}

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
    auto [k, l] = matrix.sat2conn[assigned].unify;
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
        auto [k, l] = matrix.sat2conn[-assigned].unify;
        if(!attempt.unify(TermList(k), 0, TermList(l), 0)) {
          // `reason` contradictory, exit
          // log() << "unification: " << reason << '\n';
          return;
        }
      }

      // will always exit since the totality of connections cannot be unified
      for(int assigned : connections) {
        auto [k, l] = matrix.sat2conn[assigned].unify;
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

    // find a path through the matrix
    auto path = find_path();
    // at least one connection along the path must be made
    for(int connection = 1; connection < matrix.sat2conn.size(); connection++) {
      TermList s = matrix.sat2conn[connection].unify[0];
      TermList t = matrix.sat2conn[connection].unify[1];
      auto k = static_cast<Literal *>(s.term());
      auto l = static_cast<Literal *>(t.term());
      if(path.count(k) && path.count(l))
        reason.push_back(connection);
    }

    // log() << "final: " << reason << '\n';
    return false;
  }

  // find a path through the matrix
  std::unordered_set<Literal *> find_path() {
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
      size_t length = copy.literals.size();
      // make a Vampire clause for grounding - useful for proof printing
      Clause *ground = new (length) Clause(
        length,
        NonspecificInference1(InferenceRule::INSTANTIATION, copy.original)
      );
      // don't ask
      ground->incRefCnt();

      // fill out `ground`
      for(unsigned i = 0; i < length; i++) {
        // apply the substitution
        Literal *substituted = substitution.apply(copy.literals[i], 0);
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

conflict:
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

    // for checking the path is E-satisfiable
    DP::SimpleCongruenceClosure cc(ordering.ptr());

    // to choose a random satisfied literal in clauses
    std::vector<unsigned> random_order;

    // read the path off pathfinder's model
    std::unordered_set<Literal *> path;
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
          cc.addLiteral((*ground)[j]);
          path.insert(copy.literals[j]);
          break;
        }
      }
    }

    if(cc.getStatus(false) == DP::DecisionProcedure::UNSATISFIABLE) {
      ASS(cc.getUnsatCoreCount())
      Stack<Literal *> core;
      cc.getUnsatCore(core, 0);
      SATClause *conflict = sat2fo.createConflictClause(core);
      ASS(conflict)
      pathfinder.addClause(conflict);
      sats.push_back(conflict);
      goto conflict;
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
  Propagator propagator(getProblem(), matrix);
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

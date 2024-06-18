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

#include "DP/SimpleCongruenceClosure.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/SAT2FO.hpp"

std::ostream &log() { return std::cout << "% "; }

template<typename T>
std::ostream &operator<<(std::ostream &out, const std::vector<T> &v) {
  out << '[';
  for(const T &t : v)
    out << t << ' ';
  out << ']';
  return out;
}

template<typename T>
std::ostream &operator<<(std::ostream &out, const std::unordered_set<T> &s) {
  out << '{';
  for(const T &t : s)
    out << t << ' ';
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

// an unordered pair of terms
struct TermPair {
  TermList one, other;
};

std::ostream &operator<<(std::ostream &out, const TermPair &pair) {
  return out << '<' << pair.one << ", " << pair.other << '>';
}

template<>
struct std::hash<TermPair> {
  size_t operator()(const TermPair &connection) const {
    std::hash<uint64_t> hasher;
    return
      hasher(connection.one.content()) ^
      hasher(connection.other.content());
  }
};

template<>
struct std::equal_to<TermPair> {
  bool operator()(const TermPair &left, const TermPair &right) const {
    return
      (left.one == right.one && left.other == right.other) ||
      (left.one == right.other && left.other == right.one);
  }
};

// something to keep in the literal index
struct Predicate {
  // the indexed literal
  Literal *literal;
  Predicate(Literal *literal) : literal(literal) {}

  // machinery for LiteralSubstitutionTree
  Literal *key() const { return literal; }
  bool operator==(const Predicate &other) const
  { return literal == other.literal; }
  bool operator<(const Predicate &other) const
  { return literal->getId() < other.literal->getId(); }
  bool operator>(const Predicate &other) const
  { return literal->getId() > other.literal->getId(); }
};

std::ostream &operator<<(std::ostream &out, const Predicate &indexed) {
  return out << indexed.literal->toString();
}

// something to keep in the subterm/eq index
struct Subterm {
  // the indexed term
  TypedTermList term;
  Subterm(TypedTermList term) : term(term) {}

  // machinery for LiteralSubstitutionTree
  TypedTermList key() const { return term; }
  bool operator==(const Subterm &other) const
  { return term == other.term; }
  bool operator<(const Subterm &other) const
  { return term < other.term; }
  bool operator>(const Subterm &other) const
  { return other.term < term; }
};

std::ostream &operator<<(std::ostream &out, const Subterm &indexed) {
  return out << indexed.term;
}


struct Matrix {
  // clause copies
  std::vector<Copy> copies;
  // map from connections to SAT variables
  std::unordered_map<TermPair, int> conn2sat;
  // map from SAT variables to connections
  std::vector<TermPair> sat2conn;
  // set of disequations to observe
  std::unordered_set<TermPair> disequations;

  // number of first-order variables used so far
  unsigned variables = 0;

  // index for non-equality predicates
  Indexing::LiteralSubstitutionTree<Predicate> predicate_index;
  // index for sides of equations
  Indexing::TermSubstitutionTree<Subterm> side_index;
  // index for subterms
  Indexing::TermSubstitutionTree<Subterm> subterm_index;
  // used to test whether two terms could ever unify
  RobSubstitution test_could_unify;

  Matrix() {
    // offset by 1 as 0 is not a valid SAT variable
    sat2conn.push_back({TermList::empty(), TermList::empty()});
  }

  void add_connection(TermList s, TermList t) {
    // skip ground connections, they do nothing
    if(s.isTerm() && s.term()->ground() && t.isTerm() && t.term()->ground())
      return;

    // add connection
    int fresh = sat2conn.size();
    TermPair connection {s, t};
    // if not seen before...
    if(conn2sat.insert({connection, fresh}).second) {
      // log() << fresh << '\t' << connection << '\n';
      sat2conn.push_back(connection);
    }
  }

  void add_disequation(TermList s, TermList t) {
    test_could_unify.reset();
    if(test_could_unify.unify(s, 0, t, 0))
      disequations.insert({s, t});
  }

  // increase the number of copies of `cl` by one
  void amplify(Clause *cl) {
    // check `cl` is not a tautology:
    // this happens sometimes and messes with the stuff that happens later
    for(unsigned i = 0; i < cl->length(); i++) {
      Literal *l = (*cl)[i];
      for(unsigned j = i + 1; j < cl->length(); j++) {
        Literal *k = (*cl)[j];
        if(l == Literal::complementaryLiteral(k))
          return;
      }

      if(!l->isEquality() || !l->polarity())
        continue;
      if((*l)[0] == (*l)[1])
        return;
    }

    // the new clause
    Copy copy;
    copy.original = cl;

    // variable renaming applied to produce fresh variables
    Renaming renaming(variables);

    // first pass: find connections to others
    for(unsigned i = 0; i < cl->length(); i++) {
      // normalise `l` and insert it into `copy`
      Literal *l = (*cl)[i];
      renaming.normalizeVariables(l);
      l = renaming.apply(l);
      copy.literals.push_back(l);

      // all the previous possible connections
      if(l->isEquality()) {
        if(l->polarity()) {
          TermList sort = SortHelper::getEqualityArgumentSort(l);
          for(unsigned side : {0, 1}) {
            TypedTermList t((*l)[side], sort);
            auto unifiers = subterm_index.getUnifications(
              t,
              /*retrieveSubstitutions=*/false
            );
            while(unifiers.hasNext()) {
              TypedTermList subterm = unifiers.next().data->term;
              add_connection(t, subterm);
            }
          }
        }
      }
      else {
        auto unifiers = predicate_index.getUnifications(
          l,
          /*complementary=*/true,
          /*retrieveSubstitutions=*/false
        );
        while(unifiers.hasNext()) {
          // the literal to connect to
          Literal *k = unifiers.next().data->literal;
          add_connection(TermList(l), TermList(k));
        }
      }

      NonVariableNonTypeIterator subterms(l);
      while(subterms.hasNext()) {
        TypedTermList subterm(subterms.next());
        auto unifiers = side_index.getUnifications(
          subterm,
          /*retrieveSubstitutions=*/false
        );
        while(unifiers.hasNext()) {
          TypedTermList side = unifiers.next().data->term;
          add_connection(side, subterm);
        }
      }
    }

   // second pass: insert literals into the index
    for(Literal *l : copy.literals) {
      // their top-level parts
      if(l->isEquality()) {
        if(l->polarity()) {
          TermList sort = SortHelper::getEqualityArgumentSort(l);
          side_index.insert(TypedTermList((*l)[0], sort));
          side_index.insert(TypedTermList((*l)[1], sort));
        }
      }
      else
        predicate_index.insert(l);

      // and all subterms
      NonVariableNonTypeIterator subterms(l);
      while(subterms.hasNext())
        subterm_index.insert(TypedTermList(subterms.next()));
    }

    // add disequation constraints
    for(unsigned i = 0; i < cl->length(); i++) {
      Literal *l = copy.literals[i];
      for(unsigned j = i + 1; j < cl->length(); j++) {
        Literal *k = copy.literals[j];
        if(l->polarity() == k->polarity() || l->functor() != k->functor())
          continue;
        add_disequation(TermList(l), TermList(k));
      }

      if(!l->isEquality() || !l->polarity())
        continue;
      add_disequation((*l)[0], (*l)[1]);
    }

    // finally add the copy
    copies.emplace_back(std::move(copy));

    // bump variables for the next clause
    variables = renaming.nextVar();
  }
};

// scratch space: pairs of terms to unify
static std::vector<std::pair<TermList, TermList>> UNIFY;
// scratch space: occurs check
static std::vector<TermList> OCCURS;

struct RigidSubstitution {
  struct Binding {
    TermList term;
    Binding() : term(0) {}
    Binding(TermList term) : term(term) {}
    operator bool() const { return term.content() != 0; }
  };

  // variable-term map
  std::vector<Binding> bindings;
  // trail of variables to unbind
  std::vector<unsigned> trail;

  RigidSubstitution(size_t variables) : bindings(variables) {}

  // determine what a variable is bound to
  TermList lookup(unsigned var) const {
    while(bindings[var]) {
      TermList bound = bindings[var].term;
      if(bound.isTerm())
        return bound;
      var = bound.var();
    }
    return TermList(var, false);
  }

  // for SubstHelper
  TermList apply(unsigned var) const {
    TermList bound = lookup(var);
    if(bound.isTerm())
      // TODO do this better
      bound = SubstHelper::apply(bound, *this);
    return bound;
  }

  // check whether `var` occurs in `term` modulo bindings
  // `term` is assumed to have already been `lookup`'d
  bool occurs(unsigned var, TermList term) const {
    OCCURS.clear();
    OCCURS.push_back(term);
    do {
      TermList t = OCCURS.back();
      OCCURS.pop_back();
      if(t.isVar()) {
        if(t.var() == var)
          return true;
        continue;
      }
      ASS(t.isTerm())
      Term *tt = t.term();
      for(unsigned i = 0; i < tt->arity(); i++) {
        TermList arg = (*tt)[i];
        if(arg.isVar())
          arg = lookup(arg.var());
        OCCURS.push_back(arg);
      }
    } while(!OCCURS.empty());
    return false;
  }

  // unify s and t, leaving bindings clean on failure
  bool unify(TermPair unify) {
    auto [s, t] = unify;
    UNIFY.clear();
    UNIFY.push_back({s, t});
    unsigned trail_start = trail.size();
    do {
      auto [s, t] = UNIFY.back();
      UNIFY.pop_back();

      // equal terms, do nothing
      if(s == t)
        continue;

      if(s.isVar())
        s = lookup(s.var());
      if(t.isVar())
        t = lookup(t.var());

      // equal terms, do nothing
      if(s == t)
        continue;

      // one is var, bind to the other
      if(s.isVar() || t.isVar()) {
        unsigned var = s.isVar() ? s.var() : t.var();
        TermList term = s.isVar() ? t : s;

        if(occurs(var, term)) {
          // occurs failure, clean up
          pop_to(trail_start);
          return false;
        }

        // OK, bind the variable
        // log() << var << " -> " << term << '\n';
        bindings[var] = Binding(term);
        trail.push_back(var);
        continue;
      }

      ASS(s.isTerm() && t.isTerm())
      Term *st = s.term();
      Term *tt = t.term();
      if(st->functor() != tt->functor()) {
        // functors don't match, clean up on failure
        pop_to(trail_start);
        return false;
      }

      // matching-functor case, proceed
      for(unsigned i = 0; i < st->arity(); i++)
        UNIFY.push_back({(*st)[i], (*tt)[i]});

    } while(!UNIFY.empty());
    return true;
  }

  // undo variable bindings until the trail is of length `size`
  void pop_to(size_t size) {
    while(trail.size() > size) {
      unsigned var = trail.back();
      trail.pop_back();
      ::new (&bindings[var]) Binding();
      // log() << var << " -> *\n";
    }
  }

  bool equal(TermPair pair) const {
    auto [s, t] = pair;
    UNIFY.clear();
    UNIFY.push_back({s, t});

    do {
      auto [s, t] = UNIFY.back();
      UNIFY.pop_back();
      if(s == t)
        continue;

      if(s.isVar())
        s = lookup(s.var());
      if(t.isVar())
        t = lookup(t.var());

      if(s == t)
        continue;

      if(s.isVar() || t.isVar())
        return false;

      ASS(s.isTerm())
      ASS(t.isTerm())
      Term *st = s.term();
      Term *tt = t.term();
      if(st->functor() != tt->functor())
        return false;
      for(unsigned i = 0; i < st->arity(); i++)
        UNIFY.push_back({(*st)[i], (*tt)[i]});
    } while(!UNIFY.empty());
    return true;
  }
};

std::ostream &operator<<(std::ostream &out, const RigidSubstitution &substitution) {
  out << '{';
  bool first = true;
  for(unsigned i = 0; i < substitution.bindings.size(); i++)
    if(substitution.bindings[i]) {
      out
        << (first ? "" : ", ") <<
        i << " -> " << substitution.bindings[i].term;
      first = false;
    }
  return out << '}';
}

struct Propagator: public CaDiCaL::ExternalPropagator {
  // the matrix
  const Matrix &matrix;
  // current substitution
  RigidSubstitution substitution;
  // substitution used for minimizing unification conflicts
  RigidSubstitution minimize;
  // assignments made so far
  std::vector<int> trail;
  // map from variables to 0 if not assigned, -1/+1 for assigned
  std::vector<char> set;
  // if there is a clause for CaDiCaL to learn
  bool learn_set = false;
  // the next learned clause
  std::vector<int> learn;
  // random source
  std::mt19937 rng;
  // ordering (for SimpleCongruenceClosure?!)
  OrderingSP ordering;

  // store things to backtrack in a decision level
  struct Level {
    // size of the trail
    size_t trail;
    // number of variables bound
    size_t variables;
  };
  // decision levels
  std::vector<Level> levels;

  Propagator(Problem &problem, const Matrix &matrix) :
    matrix(matrix),
    substitution(matrix.variables),
    minimize(matrix.variables),
    set(matrix.sat2conn.size(), 0),
    ordering(Kernel::Ordering::create(problem, *env.options))
  {}

  void notify_assignment(int assigned, bool fixed) final {
    // log() << "assign: " << assigned << '\n';

    // should only get fixed assignments at decision level 0 (without chrono)
    ASS(!fixed || levels.empty())
    ASS_EQ(set[abs(assigned)], 0)

    trail.push_back(assigned);
    set[abs(assigned)] = assigned > 0 ? 1 : -1;

    // do nothing when variable is assigned false,
    // or there is a conflict we didn't tell CaDiCaL about yet
    if(assigned < 0 || learn_set)
      return;

    // unify the literals corresponding to the connection
    if(!substitution.unify(matrix.sat2conn[assigned]))
      compute_unification_reason(assigned);
  }

  // fill out `reason` given that `failed` caused a unification failure
  void compute_unification_reason(int failed) {
    ASS(!learn_set)
    ASS(learn.empty())

    learn_set = true;
    // conflicting literal guaranteed to be a reason
    learn.push_back(-failed);

    // unify this connection in a fresh substitution
    minimize.pop_to(0);
    // will always succeed as it has an MGU
    ALWAYS(minimize.unify(matrix.sat2conn[failed]))

    do {
      size_t restore = minimize.trail.size();
      failed = 0;
      // will always exit early since the totality of connections cannot be unified
      // NB does not repeat unifications from `reason`
      for(int connection : trail) {
        if(connection < 0)
          continue;
        if(!minimize.unify(matrix.sat2conn[connection])) {
          // this connection definitely necessary
          failed = connection;
          learn.push_back(-failed);
          minimize.pop_to(restore);
          break;
        }
      }
      // `failed` must have been set in the loop
      ASS_NEQ(failed, 0)
    } while(minimize.unify(matrix.sat2conn[failed]));

    // log() << "unification: " << learn << '\n';
  }

  void compute_disequation_reason(TermPair disequation) {
    ASS(!learn_set)
    ASS(learn.empty())
    learn_set = true;

    minimize.pop_to(0);
    int failed;
    do {
      size_t restore = minimize.trail.size();
      failed = 0;
      // will always exit early since the totality of connections cause disequation failure
      // NB does not repeat unifications from `reason`
      for(int connection : trail) {
        if(connection < 0)
          continue;
        // will always succeed as the set of connections is consistent
        ALWAYS(minimize.unify(matrix.sat2conn[connection]))
        if(minimize.equal(disequation)) {
          // this connection definitely necessary
          failed = connection;
          learn.push_back(-failed);
          minimize.pop_to(restore);
          break;
        }
      }
      // `failed` must have been set in the loop
      ASS_NEQ(failed, 0)
      // will always succeed as the set of connections is consistent
      ALWAYS(minimize.unify(matrix.sat2conn[failed]))
    } while(!minimize.equal(disequation));
    // log() << "disequation: " << learn << '\n';
  }

  bool check_disequations() {
    for(TermPair disequation : matrix.disequations)
      if(substitution.equal(disequation)) {
        compute_disequation_reason(disequation);
        return false;
      }
    return true;
  }

  void notify_new_decision_level() final {
    levels.push_back({trail.size(), substitution.trail.size()});
    // log() << "decision: " << levels.size() << '\n';
  }

  void notify_backtrack(size_t decision_level) final {
    // log() << "backtrack to: " << decision_level << '\n';
    // this seems to happen sometimes: ignore it
    if(decision_level >= levels.size())
      return;

    learn_set = false;
    learn.clear();

    // undo everything after this level
    Level level = levels[decision_level];
    levels.resize(decision_level);
    while(trail.size() > level.trail) {
      set[abs(trail.back())] = 0;
      trail.pop_back();
    }
    substitution.pop_to(level.variables);
  }

  bool cb_has_external_clause() final {
    if(learn_set)
      return true;
    if(!check_disequations())
      return true;
    return false;
  }

  int cb_add_external_clause_lit() final {
    if(learn.empty()) {
      learn_set = false;
      return 0;
    }
    int lit = learn.back();
    learn.pop_back();
    return lit;
  }

  bool cb_check_found_model(const std::vector<int> &model) final {
    ASS(!learn_set)
    ASS(learn.empty())
    learn_set = true;

#if 0
    // ooooh stars pretty!
    auto &out = log();
    for(int assign : model)
      out << (assign < 0 ? ' ' : '*');
    out << '\n';
#endif

    // find a path through the matrix
    auto path = find_path();

    // sets of predicates, sides of equations, and subterms in the path
    DHSet<TermList> predicates, sides, subterms;
    for(Literal *l : path) {
      if(l->isEquality()) {
        if(l->polarity()) {
          sides.insert((*l)[0]);
          sides.insert((*l)[1]);
        }
      }
      else {
        predicates.insert(TermList(l));
      }
      NonVariableNonTypeIterator it(l);
      while(it.hasNext())
        subterms.insert(TermList(it.next()));
    }

    // at least one connection along the path must be made
    for(int connection = 1; connection < matrix.sat2conn.size(); connection++) {
      // we can ignore connections already set:
      // 1. If the connection is between predicates, this wouldn't be a path
      // 2. If the connection is between an equation and a subterm, it wasn't strong enough
      if(set[connection] > 0)
        continue;

      auto [s, t] = matrix.sat2conn[connection];
      if(predicates.contains(s) && predicates.contains(t))
        learn.push_back(connection);
      else if(
        (sides.contains(t) && subterms.contains(s)) ||
        (sides.contains(s) && subterms.contains(t))
      )
        learn.push_back(connection);
    }

    // log() << "final: " << reason << '\n';
    return false;
  }

  // find a path through the matrix under the current substitution
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
        Literal *substituted = SubstHelper::apply(copy.literals[i], substitution);
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
      ASS_EQ(copy.literals.size(), ground->length())

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

    // check whether the path is E-satisfiable
    // if not, try another path
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
};

MainLoopResult UPCoP::runImpl() {
  Matrix matrix;
  // add initial clauses
  UnitList::Iterator units(_prb.units());
  while(units.hasNext())
    matrix.amplify(units.next()->asClause());

  Propagator propagator(getProblem(), matrix);
  CaDiCaL::Solver solver;
  solver.connect_external_propagator(&propagator);
  // chrono allows fixed assignments at non-zero decision levels - eek!
  solver.set("chrono", 0);
  for(int i = 1; i < matrix.sat2conn.size(); i++) {
    // observe all variables
    solver.add_observed_var(i);
    // prefer setting them positively
    solver.phase(i);
  }

  log() << env.options->inputFile() << '\n';

  // should throw if we find a proof
  ALWAYS(solver.solve() != CaDiCaL::SATISFIABLE)
  log() << "SZS status Incomplete\n";
  return Statistics::REFUTATION_NOT_FOUND;
}

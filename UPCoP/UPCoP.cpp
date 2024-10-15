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

#include <unordered_set>

#include "cadical.hpp"

#include "Kernel/Clause.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "UPCoP.hpp"

using namespace Kernel;
using namespace Indexing;

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

template<typename K, typename V>
std::ostream &operator<<(std::ostream &out, const std::unordered_map<K, V> &map) {
  out << '{';
  for(const auto &entry : map)
    out << entry << ' ';
  out << '}';
  return out;
}

template<typename S, typename T>
struct std::hash<std::pair<S, T>>
{
  size_t operator()(const std::pair<S, T> &pair) const {
    return std::hash<S>{}(pair.first) ^ std::hash<T>{}(pair.second);
  }
};

struct PosRef {
  unsigned index;

  PosRef() : index(0) {}
  explicit PosRef(unsigned index) : index(index) {}
  bool is_root() { return index == 0; }
  bool operator==(PosRef other) const { return index == other.index; }
};

std::ostream &operator<<(std::ostream &out, PosRef ref) { return out << 'p' << ref.index; }

template<>
struct std::hash<PosRef> {
  size_t operator()(PosRef ref) const {
    return std::hash<unsigned>{}(ref.index);
  }
};

struct Pos {
  PosRef parent;
  unsigned child;
  Clause *here = nullptr;
  std::vector<Clause *> possibilities;
  unsigned children = 0;

  Pos(PosRef parent, unsigned child)
    : parent(parent), child(child) {}
};

class Positions {
  std::vector<Pos> positions;
  std::unordered_map<std::pair<PosRef, unsigned>, PosRef> lookup;

public:
  Positions() {
    positions.push_back(Pos(PosRef(), 0));
  }

  Pos &operator[](PosRef ref) { return positions[ref.index]; }

  Literal *at(PosRef ref) const {
    ASS(!ref.is_root())
    // counter-intuitively, we want to go to the parent and get their nth literal
    const Pos &position = positions[ref.index];
    const Pos &parent = positions[position.parent.index];
    if(!parent.here)
      return nullptr;
    return (*parent.here)[position.child];
  }

  PosRef get(PosRef parent, unsigned child) {
    auto pair = std::make_pair(parent, child);
    decltype(lookup)::iterator found = lookup.find(pair);
    if(found != lookup.end())
      return found->second;

    PosRef result(positions.size());
    lookup[pair] = result;
    positions.push_back(Pos(parent, child));
    // TODO positions[parent.index].children = std::max(child, 
    std::cout << parent << '.' << child << " -> " << result << '\n';
    return result;
  }
};

struct PosTL;

struct PosVar {
  PosRef pos;
  unsigned var;
  PosVar(PosRef pos, unsigned var) : pos(pos), var(var) {}
  PosVar(PosTL term);
  bool operator==(PosVar other) const { return pos == other.pos && var == other.var; }
};

template<>
struct std::hash<PosVar> {
  size_t operator()(PosVar var) const {
    return std::hash<PosRef>{}(var.pos) ^ std::hash<unsigned>{}(var.var);
  }
};

struct PosTL {
  PosRef pos;
  TermList term;
  PosTL() : pos(0), term(0) {}
  PosTL(PosRef pos, TermList term) : pos(pos), term(term) {}
  PosTL(PosVar x) : pos(x.pos), term(x.var, false) {}
  operator bool() const { return term.content() != 0; }
  bool operator==(PosTL other) const { return pos == other.pos && term == other.term; }
  bool isVar() const { return term.isVar(); }
  bool isTerm() const { return term.isTerm(); }
  unsigned functor() const { return term.term()->functor(); }
  unsigned arity() const { return term.term()->arity(); }
  PosTL operator[](unsigned i) { return PosTL(pos, (*term.term())[i]); }
};

std::ostream &operator<<(std::ostream &out, PosTL term) {
  return out << term.term << '/' << term.pos << '\n';
}

PosVar::PosVar(PosTL term) : pos(term.pos), var(term.term.var()) {}

// scratch space: pairs of terms to unify
static std::vector<std::pair<PosTL, PosTL>> UNIFY;
// scratch space: occurs check
static std::vector<PosTL> OCCURS;

struct RigidSubstitution {
  // variable-term map
  std::unordered_map<PosVar, PosTL> bindings;
  // trail of variables to unbind
  std::vector<PosVar> trail;

  void clear() {
    bindings.clear();
    trail.clear();
  }

  // determine what a variable is bound to
  PosTL lookup(PosVar var) {
    while(bindings[var]) {
      PosTL bound = bindings[var];
      if(bound.isTerm())
        return bound;
      var = bound;
    }
    return var;
  }

  // check whether `var` occurs in `term` modulo bindings
  // `term` is assumed to have already been `lookup`'d
  bool occurs(PosVar var, PosTL term) {
    OCCURS.clear();
    OCCURS.push_back(term);
    do {
      PosTL t = OCCURS.back();
      OCCURS.pop_back();
      if(t == PosTL(var))
        return true;
      if(t.isVar())
        continue;

      ASS(t.isTerm())
      for(unsigned i = 0; i < t.arity(); i++) {
        PosTL arg = t[i];
        if(arg.isVar())
          arg = lookup(arg);
        OCCURS.push_back(arg);
      }
    } while(!OCCURS.empty());
    return false;
  }

  // unify s and t, leaving bindings clean on failure
  bool unify(PosTL s, PosTL t) {
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
        s = lookup(s);
      if(t.isVar())
        t = lookup(t);

      // equal terms, do nothing
      if(s == t)
        continue;

      // one is var, bind to the other
      if(s.isVar() || t.isVar()) {
        PosVar var = s.isVar() ? s : t;
        PosTL term = s.isVar() ? t : s;

        if(occurs(var, term)) {
          // occurs failure, clean up
          pop_to(trail_start);
          return false;
        }

        // OK, bind the variable
        bindings[var] = term;
        trail.push_back(var);
        continue;
      }

      ASS(s.isTerm() && t.isTerm())
      if(s.functor() != t.functor()) {
        // functors don't match, clean up on failure
        pop_to(trail_start);
        return false;
      }

      // matching-functor case, proceed
      for(unsigned i = 0; i < s.arity(); i++)
        UNIFY.push_back({s[i], t[i]});
    } while(!UNIFY.empty());
    return true;
  }

  // undo variable bindings until the trail is of length `size`
  void pop_to(size_t size) {
    while(trail.size() > size) {
      PosVar var = trail.back();
      trail.pop_back();
      ::new (&bindings[var]) PosTL;
    }
  }

  bool equal(PosTL s, PosTL t) {
    UNIFY.clear();
    UNIFY.push_back({s, t});

    do {
      auto [s, t] = UNIFY.back();
      UNIFY.pop_back();
      if(s == t)
        continue;

      if(s.isVar())
        s = lookup(s);
      if(t.isVar())
        t = lookup(t);

      if(s == t)
        continue;

      if(s.isVar() || t.isVar())
        return false;

      ASS(s.isTerm())
      ASS(t.isTerm())
      if(s.functor() != t.functor())
        return false;
      for(unsigned i = 0; i < s.arity(); i++)
        UNIFY.push_back({s[i], t[i]});
    } while(!UNIFY.empty());
    return true;
  }
};

std::ostream &operator<<(std::ostream &out, const RigidSubstitution &subst) {
  return out << subst.bindings << '\n';
}

std::unordered_map<std::pair<Literal *, Literal *>, bool> CAN_UNIFY;
static bool can_unify(Literal *l, Literal *k) {
  if(l->polarity() == k->polarity() || l->functor() != k->functor())
    return false;

  auto found = CAN_UNIFY.find({l, k});
  if(found != CAN_UNIFY.end())
    return found->second;

  RobSubstitution subst;
  bool result = subst.unify(TermList(l), 0, TermList(k), 1);
  CAN_UNIFY[{l, k}] = result;
  return result;
}

enum class Flavour {
  CLAUSE_AT,
  CONNECTION
};

struct Place {
  Clause *clause;
  PosRef at;
  bool seen = false;

  Place(Clause *clause, PosRef onto)
    : clause(clause), at(onto) {}
};

struct Connection {
  PosRef above, below;

  Connection(PosRef above, PosRef below)
    : above(above), below(below) {}
};

struct Dispatch {
  Flavour flavour;
  union {
    Place place;
    Connection connection;
  };

  Dispatch(Place place) : flavour(Flavour::CLAUSE_AT), place(place) {}
  Dispatch(Connection connection) : flavour(Flavour::CONNECTION), connection(connection) {}
};

class Propagator final : public CaDiCaL::ExternalPropagator {
  // parent solver
  CaDiCaL::Solver &solver;

  // positions in the tableau
  Positions positions;
  // current depth limit
  unsigned depth_limit;
  // term index to find possible extensions
  LiteralSubstitutionTree<LiteralClause> predicate_index;
  // current substitution
  RigidSubstitution substitution;

  // map from variables to their meaning
  std::vector<Dispatch> dispatches;
  // SAT variable for a position and clause
  std::unordered_map<std::pair<PosRef, Clause *>, int> place_lookup;
  // SAT variable for a connection between positions
  std::unordered_map<std::pair<PosRef, PosRef>, int> connection_lookup;

  // queue of learned clauses
  std::vector<std::vector<int>> clause_queue;
  // queue of propagations
  std::vector<int> prop_queue;
  // reasons for propagated literals
  std::unordered_map<int, std::vector<int>> prop_reason;
  // literals assigned postively
  std::vector<int> trail;
  // assignments deferred as clauses not yet in place
  std::unordered_set<int> deferred;

  struct Decision {
    // length of the SAT trail at this decision level
    size_t sat;
    // length of the first-order variable trail at this decision level
    size_t binding;
  };

  // length of the trail at each decision level
  std::vector<Decision> decisions;

  int get_place_var(PosRef position, Clause *cl) {
    auto pair = std::make_pair(position, cl);
    auto found = place_lookup.find(pair);
    if(found != place_lookup.end())
      return found->second;

    int result = dispatches.size();
    dispatches.push_back(Place(cl, position));
    place_lookup.insert({pair, result});
    solver.add_observed_var(result);
    positions[position].possibilities.push_back(cl);
    std::cout << cl->number() << '@' << position << " -> " << result << '\n';
    return result;
  }

  int get_connection_var(PosRef above, PosRef below) {
    auto pair = std::make_pair(above, below);
    decltype(connection_lookup)::iterator found = connection_lookup.find(pair);
    if(found != connection_lookup.end())
      return found->second;

    int result = dispatches.size();
    dispatches.push_back(Connection(above, below));
    connection_lookup.insert({pair, result});
    solver.add_observed_var(result);
    std::cout << above << '~' << below << " -> " << result << '\n';
    return result;
  }

  void add_place_constraints(int var, Place place) {
    ASS(place.clause)

    // each literal has to be connected to something above or to a clause below
    for(unsigned i = 0; i < place.clause->length(); i++) {
      Literal *l = (*place.clause)[i];
      std::vector<int> possibilities = {-var};
      PosRef position = positions.get(place.at, i);
      PosRef ancestor = positions[position].parent;
      unsigned depth = 1;
      while(!ancestor.is_root()) {
        depth++;
        possibilities.push_back(get_connection_var(ancestor, position));
        ancestor = positions[ancestor].parent;
      }

      if(depth < depth_limit) {
        auto unifiers = predicate_index.getUnifications(
          l,
          /*complementary=*/true,
          /*retrieveSubstitutions=*/false
        );
        while(unifiers.hasNext()) {
          LiteralClause record = *unifiers.next().data;
          possibilities.push_back(get_place_var(position, record.clause));
        }
      }
      clause_queue.push_back(std::move(possibilities));
    }

    // each clause has to be connected by at least one literal to the parent
    // (except the start clause)
    if(!place.at.is_root()) {
      std::vector<int> at_least_one_connection = {-var};
      for(unsigned i = 0; i < place.clause->length(); i++) {
        PosRef below = positions.get(place.at, i);
        at_least_one_connection.push_back(get_connection_var(place.at, below));
      }
      clause_queue.push_back(std::move(at_least_one_connection));
    }
  }

  template<bool explain = true>
  bool make_connection(RigidSubstitution &substitution, int assigned) {
    ASS_G(assigned, 0)
    ASS(dispatches[assigned].flavour == Flavour::CONNECTION)
    Connection connection = dispatches[assigned].connection;
    unsigned n = positions[connection.above].child;
    unsigned m = positions[connection.below].child;
    PosRef p = positions[connection.above].parent;
    PosRef q = positions[connection.below].parent;
    Clause *c = positions[p].here;
    Clause *d = positions[q].here;
    if(!c || !d) {
      deferred.insert(assigned);
      return true;
    }
    if(n >= c->length() || m >= d->length())
      goto fail_fast;

    {
      Literal *l = (*c)[n];
      Literal *k = (*d)[m];
      if(!can_unify(l, k))
        goto fail_fast;
      if(!substitution.unify(PosTL(p, TermList(l)), PosTL(q, TermList(k)))) {
        if(explain)
          explain_unification_failure(assigned);
        return false;
      }
    }
    return true;

fail_fast:
    std::vector reason = { -assigned, -place_lookup[{p, c}], -place_lookup[{q, d}] };
    std::cout << "fast connection conflict: " << reason << '\n';
    clause_queue.emplace_back(std::move(reason));
    return false;
  }

  void explain_unification_failure(int start) {
    std::vector<int> reason = {-start};
    RigidSubstitution substitution;
    while(true) {
restart:
      substitution.clear();
      for(int trouble : reason)
        if(!make_connection<false>(substitution, -trouble))
          goto finish;

      for(int assigned : trail)
        if(dispatches[assigned].flavour == Flavour::CONNECTION)
          if(!make_connection<false>(substitution, assigned)) {
            reason.push_back(-assigned);
            goto restart;
          }
      ASSERTION_VIOLATION
    }

finish:
    // add the placed clauses to the reason
    size_t original = reason.size();
    for(size_t i = 0; i < original; i++) {
      Connection connection = dispatches[-reason[i]].connection;
      PosRef p = positions[connection.above].parent;
      PosRef q = positions[connection.below].parent;
      Clause *c = positions[p].here;
      Clause *d = positions[q].here;
      reason.push_back(-place_lookup[{p, c}]);
      reason.push_back(-place_lookup[{q, d}]);
    }
    std::cout << "connection conflict: " << reason << '\n';
    clause_queue.emplace_back(std::move(reason));
  }

public:
  Propagator(CaDiCaL::Solver &solver, unsigned depth_limit)
    : solver(solver), depth_limit(depth_limit) {
    solver.connect_external_propagator(this);
    dispatches.push_back(Place(nullptr, PosRef()));
  }

  void read_problem(const Problem &prb) {
    List<Unit *>::Iterator units(prb.units());
    while(units.hasNext()) {
      Clause *cl = units.next()->asClause();
      for(unsigned i = 0; i < cl->size(); i++)
        predicate_index.insert({(*cl)[i], cl});

      if(cl->derivedFromGoal()) {
        int start = get_place_var(PosRef(), cl);
        solver.add(start);
      }
    }
    solver.add(0);
  }

  void notify_assignment(const std::vector<int> &all_assigned) override {
    for(int assigned : all_assigned) {
      std::cout << assigned << '\n';
      if(assigned < 0)
        continue;

      Dispatch dispatch = dispatches[assigned];
      switch(dispatch.flavour) {
      case Flavour::CLAUSE_AT: {
        Place place = dispatch.place;
        Clause *placed = place.clause;

        // disallow two clauses in one position
        if(positions[place.at].here) {
          int already = place_lookup[{place.at, positions[place.at].here}];
          clause_queue.push_back({-already, -assigned});
          std::cout << "place conflict: " << clause_queue.back() << '\n';
          return;
        }
        for(auto cl : positions[place.at].possibilities) {
          if(cl == placed)
            continue;
          int propagate = place_lookup[{place.at, cl}];
          if(!prop_reason[propagate].empty())
            continue;
          prop_queue.push_back(-propagate);
          prop_reason[propagate] = {-assigned, -propagate};
        }

        // disallow clauses placed at non-existent positions
        for(PosRef p = place.at; !p.is_root(); p = positions[p].parent) {
          Clause *above = positions[positions[p].parent].here;
          if(above && above->length() < positions[p].child) {
            std::vector<int> reason = { -place_lookup[{positions[p].parent, above}], -assigned };
            std::cout << "non-existent place conflict: " << reason << '\n';
            clause_queue.emplace_back(std::move(reason));
            return;
          }
        }

        // add closing constraints when placing a clause for the first time
        if(!place.seen) {
          add_place_constraints(assigned, place);
          place.seen = true;
        }

        positions[place.at].here = placed;
        break;
      }
      case Flavour::CONNECTION: {
        // TODO propagate impossible connections
        // TODO propagate that clauses below a connection need not be placed
        if(!make_connection(substitution, assigned))
          return;
        break;
      }
      }
      trail.push_back(assigned);
    }
  }

  void notify_new_decision_level() override {
    std::cout << "decision level: " << decisions.size() + 1 << '\n';
    decisions.push_back({trail.size(), substitution.trail.size()});
  }

  void notify_backtrack(size_t decision_level) override {
    std::cout << "backtrack: " << decision_level << '\n';
    Decision decision = decisions[decision_level];
    decisions.resize(decision_level);
    while(trail.size() > decision.sat) {
      int undo = trail.back();
      trail.pop_back();
      std::cout << "undo: " << undo << '\n';
      deferred.erase(undo);
      switch(dispatches[undo].flavour) {
      case Flavour::CLAUSE_AT: {
        Place place = dispatches[undo].place;
        positions[place.at].here = nullptr;
        break;
      }
      case Flavour::CONNECTION:
        break;
      }
    }
    substitution.pop_to(decision.binding);
    prop_queue.clear();
  }

  int cb_propagate() override {
    if(prop_queue.empty())
      return 0;
    int result = prop_queue.back();
    std::cout << "propagate: " << result << '\n';
    prop_queue.pop_back();
    return result;
  };

  virtual int cb_add_reason_clause_lit(int propagated) override {
    int atom = std::abs(propagated);
    std::vector<int> &clause = prop_reason[atom];
    if(clause.empty()) {
      std::cout << 0 << '\n';
      prop_reason.erase(atom);
      return 0;
    }
    int next = clause.back();
    std::cout << "reason for " << propagated << ": " << next << '\n';
    clause.pop_back();
    return next;
  }

  bool cb_has_external_clause(bool &) override { return !clause_queue.empty(); }

  int cb_add_external_clause_lit() override {
    ASS(!clause_queue.empty())
    std::vector<int> &next = clause_queue.back();
    if(next.empty()) {
      clause_queue.pop_back();
      return 0;
    }
    int result = next.back();
    next.pop_back();
    return result;
  }

  bool cb_check_found_model(const std::vector<int> &) override {
    std::cout << "final\n";
    std::cout << "deferred: " << deferred << '\n';
    std::cout << trail << '\n';
    ASS(clause_queue.empty())
    ASS(prop_queue.empty())
    for(auto assigned : deferred) {
      std::cout << assigned << '\n';
      if(!make_connection(substitution, assigned))
        return false;
    }
    return true;
  }
};

MainLoopResult UPCoP::runImpl() {
  List<Unit *>::Iterator units(_prb.units());
  while(units.hasNext())
    std::cout << units.next()->toString() << '\n';

  unsigned depth_limit = 0;
  while(++depth_limit) {
    std::cout << "depth: " << depth_limit << '\n';
    CaDiCaL::Solver solver;
    Propagator propagator(solver, depth_limit);
    propagator.read_problem(_prb);
    if(solver.solve() == CaDiCaL::SATISFIABLE)
      return Statistics::REFUTATION_NOT_FOUND;
  }
  ASSERTION_VIOLATION
}

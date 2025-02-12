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
 * @file Dedukti.cpp
 * Routines for Dedukti output
 *
 * Most of the magic proof terms taken from
 * "A Shallow Embedding of Resolution and Superposition Proofs into the λΠ-Calculus Modulo"
 * Guillaume Burel
 */

#include "Dedukti.hpp"

#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Parse/TPTP.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/Superposition.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/FunctionDefinition.hpp"

#include <unordered_map>
#include <set>
#include <sstream>

using namespace Inferences;

const char *PRELUDE = R"(
(; Prop ;)
Prop : Type.
def Prf : (Prop -> Type).
true : Prop.
[] Prf true --> (r : Prop -> ((Prf r) -> (Prf r))).
false : Prop.
[] Prf false --> (r : Prop -> (Prf r)).
not : (Prop -> Prop).
[p] Prf (not p) --> ((Prf p) -> (r : Prop -> (Prf r))).
and : (Prop -> (Prop -> Prop)).
[p, q] Prf (and p q) --> (r : Prop -> (((Prf p) -> ((Prf q) -> (Prf r))) -> (Prf r))).
or : (Prop -> (Prop -> Prop)).
[p, q] Prf (or p q) --> (((Prf p) -> (Prf false)) -> (((Prf q) -> (Prf false)) -> (Prf false))).
imp : (Prop -> (Prop -> Prop)).
[p, q] Prf (imp p q) --> ((Prf p) -> (Prf q)).
iff : Prop -> Prop -> Prop.
[p, q] Prf (iff p q) --> (Prf (and (imp p q) (imp q p))).

(; Set ;)
Set : Type.
injective El : (Set -> Type).
iota : Set.
inhabit : A : Set -> El A.

(; Equality ;)
def eq : a : Set -> El a -> El a -> Prop.
[a, x, y] Prf (eq a x y) --> p : (El a -> Prop) -> Prf (p x) -> Prf (p y).
def refl : (a : Set) -> x : (El a) -> Prf (eq a x x).
[a, x] refl a x --> p : ((El a) -> Prop) => t : Prf (p x) => t.
def comm : (a : Set) -> x : (El a) -> y : (El a) -> Prf (eq a x y) -> Prf (eq a y x).
[a, x, y] comm a x y --> e : (Prf (eq a x y)) => p : ((El a) -> Prop) => e (z : (El a) => imp (p z) (p x)) (t : (Prf (p x)) => t).
def comml : (a : Set) -> x : (El a) -> y : (El a) -> (Prf (eq a x y) -> Prf false) -> (Prf (eq a y x) -> Prf false).
[a, x, y] comml a x y --> l : (Prf (eq a x y) -> Prf false) => e : Prf (eq a y x) => l (comm a y x e).
def comml_not : (a : Set) -> x : (El a) -> y : (El a) -> (Prf (not (eq a x y)) -> Prf false) -> (Prf (not (eq a y x)) -> Prf false).
[a, x, y] comml_not a x y --> l : ((Prf (eq a x y) -> Prf false) -> Prf false) => ne : (Prf (eq a y x) -> Prf false) => l (e : Prf (eq a x y) => ne (comm a x y e)).

(; Quant ;)
forall : (a : Set -> (((El a) -> Prop) -> Prop)).
[a, p] Prf (forall a p) --> (x : (El a) -> (Prf (p x))).
exists : (a : Set -> (((El a) -> Prop) -> Prop)).
[a, p] Prf (exists a p) --> (r : Prop -> ((x : (El a) -> ((Prf (p x)) -> (Prf r))) -> (Prf r))).

(; polymorphic quantifier ;)
forall_poly : (Set -> Prop) -> Prop.
[p] Prf (forall_poly p) --> a : Set -> Prf (p a).

(; Classic ;)
def cPrf : (Prop -> Type) := (p : Prop => (Prf (not (not p)))).
def cand : (Prop -> (Prop -> Prop)) := (p : Prop => (q : Prop => (and (not (not p)) (not (not q))))).
def cor : (Prop -> (Prop -> Prop)) := (p : Prop => (q : Prop => (or (not (not p)) (not (not q))))).
def cimp : (Prop -> (Prop -> Prop)) := (p : Prop => (q : Prop => (imp (not (not p)) (not (not q))))).
def cforall : (a : Set -> (((El a) -> Prop) -> Prop)) := (a : Set => (p : ((El a) -> Prop) => (forall a (x : (El a) => (not (not (p x))))))).
def cexists : (a : Set -> (((El a) -> Prop) -> Prop)) := (a : Set => (p : ((El a) -> Prop) => (exists a (x : (El a) => (not (not (p x))))))).

(; Clauses ;)
def prop_clause : Type.
def ec : prop_clause.
def cons : (Prop -> (prop_clause -> prop_clause)).
def clause : Type.
def cl : (prop_clause -> clause).
def bind : (A : Set -> (((El A) -> clause) -> clause)).
def bind_poly : (Set -> clause) -> clause.
def Prf_prop_clause : (prop_clause -> Type).

[] Prf_prop_clause ec --> (Prf false).
[p, c] Prf_prop_clause (cons p c) --> ((Prf p -> Prf false) -> (Prf_prop_clause c)).
def Prf_clause : (clause -> Type).
[c] Prf_clause (cl c) --> (Prf_prop_clause c).
[A, f] Prf_clause (bind A f) --> (x : (El A) -> (Prf_clause (f x))).
[f] Prf_clause (bind_poly f) --> (alpha : Set -> (Prf_clause (f alpha))).

def av_clause : Type.
def acl : clause -> av_clause.
def if : Prop -> av_clause -> av_clause.
def Prf_av_clause : av_clause -> Type.

[c] Prf_av_clause (acl c) --> Prf_clause c.
[sp, c] Prf_av_clause (if sp c) --> (Prf (not sp) -> Prf false) -> Prf_av_clause c.

(;----------------------------------------------------------------------------;)

)";

using namespace Kernel;

// RAII to automatically close tracked open parentheses
struct CloseParens {
  std::ostream &out;
  unsigned count = 0;
  CloseParens(std::ostream &out) : out(out) {}
  // OK to move, but not to copy
  CloseParens(CloseParens &&other) noexcept
    : out(other.out), count(other.count) { other.count = 0; }
  CloseParens(const CloseParens &) = delete;
  CloseParens &operator=(const CloseParens &) = delete;

  [[nodiscard]] const char *open(const char *start = "(") & {
    count++;
    return start;
  }

  [[nodiscard]] const char *open_if(bool condition, const char *start = "(") & {
    if(condition)
      return open(start);
    return "";
  }

  ~CloseParens() { while(count--) out << ')'; }
};

/*
 * These types describe various transformations that could be applied to a term or literal.
 * This is useful when we want to print an equation under some transformation,
 * but _without_ changing the order of its literals.
 *
 * For example: if we have X = c and we apply the substitution X -> d,
 * we may end up with the equation c = d, _not_ d = c.
 */

template<typename S, typename T>
struct Sequence;

// CRTP
template<typename Derived>
struct Transformation {
  template<typename Other>
  Sequence<Derived, Other> then(Other &&other) {
    return Sequence<Derived, Other> { std::move(*static_cast<Derived *>(this)), other };
  }
};

// do-nothing identity transform
struct Identity : public Transformation<Identity> {
  Literal *operator()(Literal *literal) { return literal; }
  TermList operator()(TermList term) { return term; }
};

// apply S, then T
template<typename S, typename T>
struct Sequence : public Transformation<Sequence<S, T>> {
  S s;
  T t;
  Sequence(S s, T t) : s(s), t(t) {}
  Literal *operator()(Literal *literal) { return t(s(literal)); }
  TermList operator()(TermList term) { return t(s(term)); }
};

// simple substitution, no banks here
struct DoSubstitution : public Transformation<DoSubstitution> {
  SimpleSubstitution &substitution;
  DoSubstitution(SimpleSubstitution &substitution) : substitution(substitution) {}

  Literal *operator()(Literal *literal) { return SubstHelper::apply(literal, substitution); }
  TermList operator()(TermList term) { return SubstHelper::apply(term, substitution); }
};

// apply a RobSubstitution using a particular bank
template<unsigned bank>
struct DoRobSubstitution : public Transformation<DoRobSubstitution<bank>> {
  RobSubstitution &substitution;
  DoRobSubstitution(RobSubstitution &substitution) : substitution(substitution) {}

  Literal *operator()(Literal *literal) { return substitution.apply(literal, bank); }
  TermList operator()(TermList term) { return substitution.apply(term, bank); }
};
using DoRobSubstitution0 = DoRobSubstitution<0>;
using DoRobSubstitution1 = DoRobSubstitution<1>;

// replace a term with another
struct DoReplacement : public Transformation<DoReplacement> {
  TermList from, to;
  DoReplacement(TermList from, TermList to) : from(from), to(to) {}
  Literal *operator()(Literal *literal) { return EqHelper::replace(literal, from, to); }

  TermList operator()(TermList term) {
    if(term.isVar())
      return term;
    // EqHelper::replace only replaces _occurrences_
    if(term == from)
      return to;
    return TermList(EqHelper::replace(term.term(), from, to));
  }
};

/* here ends the transforms */

/*
 * We sometimes need to know whether we should use a specific variable or a don't-care.
 * Consider resolving p(X) against ~p(Y) to get the empty clause.
 * Neither X nor Y will be bound in the resulting Dedukti term,
 * but we have to supply something of appropriate sort.
 * In this case we should rely on the sort being non-empty and use the don't-care term "inhabit"
 * instead of a specific variable.
 *
 * We abstract this with a `Care` type which tells us when we care.
 * `AlwaysCare` is when we always care about which variable we have.
 */
struct AlwaysCare {
  bool cares(unsigned _) { return true; }
};

// dedukti-print a variable
template<typename Care = AlwaysCare>
struct DkVar {
  // negative numbers are special, everything else is a variable
  int code = 0;
  TermList sort;
  Care care;

  DkVar(unsigned var, TermList sort, bool specialVar, Care care) : sort(sort), care(care) {
    if(specialVar)
      code = -1;
    else if(!care.cares(var))
      code = -2;
    else
      code = var;
  }

  DkVar(unsigned var, TermList sort, Care care = Care {}) : DkVar(var, sort, false, care) {}
  DkVar(TermList t, TermList sort, Care care = Care {}) : DkVar(t.var(), sort, t.isSpecialVar(), care) {}
};

template<typename Care>
struct DkTerm;

template<typename Care>
static std::ostream &operator<<(std::ostream &out, DkVar<Care> dk) {
  // special variables are used for the "z" term
  // frequently encountered when doing replacements
  if(dk.code == -1)
    return out << "z";
  // if we don't care...
  else if(dk.code == -2)
    // ...and it's a sort, say simply "iota"
    if(dk.sort == AtomicSort::superSort())
      return out << "iota";
    // ...and it's a term, say "inhabit" indexed by the sort
    else
      return out << "(inhabit " << DkTerm(dk.sort, AtomicSort::superSort(), dk.care) << ")";
  else
    return out << dk.code;
}

// dedukti-print a symbol name
struct DkName {
  const char *name;
  bool builtin = false;
  DkName(const char *name) : name(name) {}
  DkName(const std::string &name) : DkName(name.c_str()) {}
  DkName(Term *t) {
    if(TermList(t) == AtomicSort::defaultSort()) {
      name = "iota";
      builtin = true;
      return;
    }
    name = t->isSort()
      ? static_cast<AtomicSort *>(t)->typeConName().c_str()
      : t->functionName().c_str();
  }
};

static std::ostream &operator<<(std::ostream &out, DkName dk) {
  if(dk.builtin)
    return out << dk.name;
  return out << "{|" << dk.name << "|}";
}

// space-separated term arguments
template<typename Care>
struct DkArgs {
  Term *parent;
  Care care;
  DkArgs(Term *parent, Care care) : parent(parent), care(care) {}
};

template<typename Care>
static std::ostream &operator<<(std::ostream &out, DkArgs<Care> args) {
  if(!args.parent->arity())
    return out;

  // one set of recursive term arguments, kept on a stack
  struct Frame {
    CloseParens close;
    Term *parent;
    unsigned arg;
    Frame(std::ostream &out, Term *parent, unsigned arg) : close(out), parent(parent), arg(arg)
    { out << close.open(); }
  };

  std::vector<Frame> todo;
  Term *parent = args.parent;
  unsigned arg = 0;
  while(true) {
    TermList t = (*parent)[arg];
    out << " ";
    if(t.isVar())
      out << DkVar(t, SortHelper::getArgSort(parent, arg++), args.care);
    else if(t.isTerm()) {
      Term *term = t.term();
      arg++;
      if(term->arity()) {
        todo.push_back(Frame(out, parent, arg));
        parent = term;
        arg = 0;
      }
      out << DkName(term);
    }

    while(arg == parent->arity()) {
      if(todo.empty())
        return out;
      Frame &restore = todo.back();
      parent = restore.parent;
      arg = restore.arg;
      todo.pop_back();
    }
  }
}

// dedukti-print a term
template<typename Care = AlwaysCare>
struct DkTerm {
  TermList term, sort;
  Care care;
  DkTerm(TermList term, TermList sort, Care care = Care {}) : term(term), sort(sort), care(care) {}
};

template<typename Care>
static std::ostream &operator<<(std::ostream &out, DkTerm<Care> dk) {
  if(dk.term.isVar())
    return out << DkVar(dk.term, dk.sort, dk.care);

  Term *term = dk.term.term();
  CloseParens cp(out);
  out << cp.open_if(term->arity());
  return out << DkName(term) << DkArgs(term, dk.care);
}

// dedukti-print a literal
template<typename Care = AlwaysCare, typename Transform = Identity>
struct DkLit {
  Literal *literal;
  Care care;
  Transform transform;

  DkLit(Literal *literal, Care care = Care {}, Transform transform = Transform {})
    : literal(literal), care(care), transform(transform) {}
};

template<typename Care, typename Transform>
static std::ostream &operator<<(std::ostream &out, DkLit<Care, Transform> dk) {
  CloseParens cp(out);
  Literal *after = dk.transform(dk.literal);
  out << cp.open_if(!dk.literal->polarity(), "(not ");
  if(dk.literal->isEquality()) {
    TermList sort = SortHelper::getEqualityArgumentSort(after);
    return out
      << "(eq " << DkTerm(sort, AtomicSort::superSort(), dk.care) << ' '
      << DkTerm(dk.transform(dk.literal->termArg(0)), sort, dk.care) << " "
      << DkTerm(dk.transform(dk.literal->termArg(1)), sort, dk.care) << ")";
  }

  return out << cp.open_if(after->arity()) << DkName(after->predicateName()) << DkArgs(after, dk.care);
}

template<typename Transform, typename Care>
static void outputLiteralName(
  std::ostream &out,
  Literal *literal,
  const char *name,
  const char *comm,
  Care care,
  Transform transform
) {
  if(!literal->isEquality()) {
    out << name;
    return;
  }

  Literal *after = transform(literal);
  TermList leftAfter = transform(literal->termArg(0));
  TermList rightAfter = transform(literal->termArg(1));
  TermList sort = SortHelper::getEqualityArgumentSort(after);
  bool need_commute = after->termArg(0) != leftAfter || after->termArg(1) != rightAfter;
  if(need_commute)
    out
      << "(" << comm << " "
      << DkTerm(sort, AtomicSort::superSort()) << " "
      // TODO this is switched with respect to `outputLiteralPtr` - come up with some nice abstraction for this
      << DkTerm(leftAfter, sort, care) << " "
      << DkTerm(rightAfter, sort, care) << " ";
  out << name;
  if(need_commute)
    out << ")";
}

// dedukti-print a literal _reference_ named as a pointer
// this takes care of commuting equational literals if they flip under the `Transform`
template<typename Care, typename Transform>
struct DkLitPtr {
  Literal *literal;
  Care care;
  Transform transform;

  DkLitPtr(Literal *literal, Care care = Care {}, Transform transform = Transform {})
    : literal(literal), care(care), transform(transform) {}
};

template<typename Care, typename Transform>
static std::ostream &operator<<(std::ostream &out, DkLitPtr<Care, Transform> dk) {
  Literal *after = dk.transform(dk.literal);
  if(!dk.literal->isEquality())
    return out << after;

  CloseParens cp(out);
  TermList leftAfter = dk.transform(dk.literal->termArg(0));
  TermList rightAfter = dk.transform(dk.literal->termArg(1));
  TermList sort = SortHelper::getEqualityArgumentSort(after);
  if(after->termArg(0) != leftAfter || after->termArg(1) != rightAfter)
    out
      << cp.open("(comml") << (dk.literal->isNegative() ? "_not" : "")
      << " " << DkTerm(sort, AtomicSort::superSort())
      << " " << DkTerm(rightAfter, sort, dk.care)
      << " " << DkTerm(leftAfter, sort, dk.care) << " ";
  return out << after;
}

// dedukti-print an AVATAR split
struct DkSplit {
  SATLiteral split;
  DkSplit(SATLiteral split) : split(split) {}
  DkSplit(unsigned splitName) : DkSplit(Splitter::getLiteralFromName(splitName)) {}
};

static std::ostream &operator<<(std::ostream &out, DkSplit dk) {
  CloseParens cp(out);
  return out << cp.open_if(!dk.split.polarity(), "(not ") << "sp" << dk.split.var();
}

struct VarsWithSorts {
  std::set<unsigned> sortVars;
  std::map<unsigned, TermList> termVars;

  VarsWithSorts() = default;
  VarsWithSorts(Clause *cl) {
    DHMap<unsigned, TermList> sorts;
    SortHelper::collectVariableSorts(cl, sorts);
    for(auto [v, sort] : iterTraits(sorts.items()))
      if(sort == AtomicSort::superSort())
        sortVars.insert(v);
      else {
        termVars.insert({v, sort});
        for(TermList v : iterTraits(VariableIterator(sort)))
          sortVars.insert(v.var());
      }
  }

  struct end {};
  struct iterator {
    const VarsWithSorts &parent;
    std::set<unsigned>::iterator sortIter;
    std::map<unsigned, TermList>::iterator termIter;

    std::pair<unsigned, TermList> operator*() {
      if(sortIter != parent.sortVars.end())
        return {*sortIter, AtomicSort::superSort()};
      else
        return *termIter;
    }

    bool operator!=(end) {
      return sortIter != parent.sortVars.end() || termIter != parent.termVars.end();
    }

    void operator++() {
      if(sortIter != parent.sortVars.end())
        sortIter++;
      else
        termIter++;
    }
  };

  iterator begin() { return {*this, sortVars.begin(), termVars.begin()}; }
  end end() { return {}; }
  bool containsVar(unsigned var) { return sortVars.count(var) || termVars.count(var); }
};

// dedukti-print a clause
struct DkClause {
  Clause *clause;
  DkClause(Clause *clause) : clause(clause) {}
};

static std::ostream &operator<<(std::ostream &out, DkClause dk) {
  CloseParens cp(out);
  if(dk.clause->noSplits())
    out << "Prf_clause";
  else {
    out << "Prf_av_clause";
    SplitSet &splits = *dk.clause->splits();
    for(unsigned i = 0; i < splits.size(); i++)
      out << cp.open(" (if ") << DkSplit(splits[i]);
    out << cp.open(" (acl");
  }

  for(auto [var, sort] : VarsWithSorts(dk.clause)) {
    if(sort == AtomicSort::superSort())
      out << cp.open(" (bind_poly ") << cp.open() << var << " : Set =>";
    else
      out
        << cp.open(" (bind ") << DkTerm(sort, AtomicSort::superSort()) << ' '
        << cp.open() << var << " : El " << DkTerm(sort, AtomicSort::superSort()) << " =>";
  }
  out << cp.open(" (cl");
  for(Literal *literal : dk.clause->iterLits())
    out << cp.open(" (cons ") << DkLit(literal);
  return out << " ec";
}

// dedukti-print a formula
struct DkFormula {
  Formula *formula;
  DkFormula(Formula *formula) : formula(formula) {}
};

static std::ostream &operator<<(std::ostream &out, DkFormula dk) {
  Formula *f = dk.formula;
  CloseParens cp(out);
  switch(f->connective()) {
    case LITERAL:
      return out << DkLit(f->literal());
    case AND:
    case OR: {
      const char *op = f->connective() == AND ? "and" : "or";
      FormulaList *children = f->args();
      while(children->tail()) {
        out << cp.open() << op << " " << DkFormula(children->head()) << ' ';
        children = children->tail();
      }
      return out << DkFormula(children->head());
    }
    case IMP:
    case IFF: {
      const char *op = f->connective() == IMP ? "imp" : "iff";
      return out << '(' << op << ' ' << DkFormula(f->left()) << ' ' << DkFormula(f->right()) << ')';
    }
    case XOR:
      return out << "(not (iff " << DkFormula(f->left()) << ' ' << DkFormula(f->right()) << "))";
    case NOT:
      return out << "(not " << DkFormula(f->uarg()) << ')';
    case FORALL:
    case EXISTS: {
      const char *binder = f->connective() == FORALL ? "forall" : "exists";
      VList *vars = f->vars();
      SList *sorts = f->sorts();
      VList::Iterator vit(vars);
      SList::Iterator sit(sorts);
      while(vit.hasNext()) {
        unsigned var = vit.next();
        TermList sort;
        if(sit.hasNext())
          sort = sit.next();
        else if(SortHelper::tryGetVariableSort(var, f->qarg(), sort));
          // sort computed
        else
          // this actually does happen with e.g. ![X, Y: X]: Y = Y
          sort = AtomicSort::superSort();

        // special case ![X: $tType]: ...
        if(sort == AtomicSort::superSort()) {
          out << cp.open() << "forall_poly " << cp.open() << var << " : Set => ";
          continue;
        }
        out
          << cp.open() << binder << ' '
          << DkTerm(sort, AtomicSort::superSort()) << ' '
          << cp.open() << var
          << " : El " << DkTerm(sort, AtomicSort::superSort()) << " => ";
      }
      out << DkFormula(f->qarg());
      return out;
    }
    case BOOL_TERM:
      ASSERTION_VIOLATION
    case FALSE:
      return out << "false";
    case TRUE:
      return out << "true";
    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION
      break;
  }
}

// dedukti-print either a clause or a formula
struct DkUnit {
  Unit *unit;
  DkUnit(Unit *unit) : unit(unit) {}
};

static std::ostream &operator<<(std::ostream &out, DkUnit dk) {
  if(dk.unit->isClause())
    return out << DkClause(static_cast<Clause *>(dk.unit));
  else
    return out << "Prf " << DkFormula(static_cast<FormulaUnit *>(dk.unit)->formula());
}

static void axiomName(std::ostream &out, Unit *axiom) {
  out << "{|axiom_";
  std::string recoveredName;
  if(Parse::TPTP::findAxiomName(axiom, recoveredName))
    out << recoveredName;
  out << axiom->number() << "|}";
}

// def deduction : <clause> := <intro splits>
static void deductionPrefix(std::ostream &out, Unit *deduction, bool splits = true) {
  out << "def deduction" << deduction->number() << ": " << DkUnit(deduction) << " := ";
  if(splits && deduction->isClause()) {
    Clause *clause = static_cast<Clause *>(deduction);
    if(clause->noSplits())
      return;

    SplitSet &splits = *clause->splits();
    for(unsigned i = 0; i < splits.size(); i++) {
      SATLiteral split = Splitter::getLiteralFromName(splits[i]);
      out << " nnsp" << split.var() << " : (Prf";
      {
        CloseParens cp(out);
        out
          << cp.open_if(!split.polarity(), " (not")
          <<  " (not sp" << split.var();
      }
      out << ") -> Prf false) =>";
    }
  }
}

// deductionN <splits>
static void parentWithSplits(std::ostream &out, Clause *parent) {
  out << "deduction" << parent->number();
  if(parent->noSplits())
    return;
  SplitSet &splits = *parent->splits();
  for(unsigned i = 0; i < splits.size(); i++)
    out << " nnsp" << Splitter::getLiteralFromName(splits[i]).var();
}

static void sorry(std::ostream &out, Unit *admit) {
  out << "sorry" << admit->number() << ": ";
  UnitIterator parents = admit->getParents();
  while(parents.hasNext())
    out << DkUnit(parents.next()) << " -> ";
  out
    << DkUnit(admit) << ".\n"
    << "#PRINT \"sorry: " << ruleName(admit->inference().rule()) << "\".\n";

  deductionPrefix(out, admit, false);
  out << "sorry" << admit->number();
  parents = admit->getParents();
  while(parents.hasNext())
    out << " deduction" << parents.next()->number();
}

// apply `subst` to all literals of a clause, except `except`, discarding the result
// useful in order to reconstruct the _output_ bank variable names for an inference
static void applySubstToClause(RobSubstitution &subst, int bank, Clause *clause, Literal *except = nullptr) {
  for(Literal *l : clause->iterLits())
    if(l != except)
      subst.apply(l, bank);
}

// bind all variables and literals present in `clause`
static void bindClause(std::ostream &out, Clause *clause, VarsWithSorts &variables) {
  for(auto [v, sort] : variables)
    if(sort == AtomicSort::superSort())
      out << " " << v << " : Set => ";
    else
      out << " " << v << " : El " << DkTerm(sort, AtomicSort::superSort()) << " => ";
  for(Literal *l : clause->iterLits())
    out << "" << l << " : (Prf " << DkLit(l) << " -> Prf false) => ";
}

// wrap up common behaviour found when printing an inference
template<typename Extra>
struct ClausalInference {
  // the retrieved proof-extra
  const Extra &extra;
  // variables in `derived`
  VarsWithSorts derivedVars;
  UnitIterator parentIt;

  template<typename E = Extra>
  static E &getExtra(Clause *derived) { return env.proofExtra.get<Extra>(derived); }

  // specialisation for clausal inferences that don't need proof-extra
  template<>
  static std::nullptr_t &getExtra<std::nullptr_t>(Clause *derived) {
    static std::nullptr_t EXTRA;
    return EXTRA;
  }

  ClausalInference(std::ostream &out, Clause *derived) :
    extra(getExtra(derived)),
    derivedVars(VarsWithSorts(derived)),
    parentIt(derived->getParents())
  {
    deductionPrefix(out, derived);
    bindClause(out, derived, derivedVars);
  }

  bool cares(unsigned var) { return derivedVars.containsVar(var); }
};

// for inferences with only one parent
template<typename Extra>
struct UnaryClausalInference : public ClausalInference<Extra> {
  Clause *parent = nullptr;
  VarsWithSorts parentVars;

  UnaryClausalInference(std::ostream &out, Clause *derived) :
    ClausalInference<Extra>(out, derived)
  {
    ALWAYS(this->parentIt.hasNext())
    parent = this->parentIt.next()->asClause();
    parentVars = VarsWithSorts(parent);
    parentWithSplits(out, parent);
  }
};

// for inferences with one-or-more parents
template<typename Extra>
struct VariadicClausalInference : public UnaryClausalInference<Extra> {
  std::vector<Clause *> others;
  VariadicClausalInference(std::ostream &out, Clause *derived)
    : UnaryClausalInference<Extra>(out, derived)
  {
    for(Unit *u : iterTraits(this->parentIt))
      others.push_back(u->asClause());
  }
};

// for inferences with exactly two parents
template<typename Extra>
struct BinaryClausalInference : public UnaryClausalInference<Extra> {
  Clause *left = nullptr, *right = nullptr;
  VarsWithSorts &leftVars, rightVars;
  BinaryClausalInference(std::ostream &out, Clause *derived) :
    UnaryClausalInference<Extra>(out, derived),
    left(this->parent),
    leftVars(this->parentVars)
  {
    ALWAYS(this->parentIt.hasNext())
    right = this->parentIt.next()->asClause();
    rightVars = VarsWithSorts(right);
  }
};

static void resolution(std::ostream &out, Clause *derived) {
  BinaryClausalInference<Inferences::BinaryResolutionExtra> inf(out, derived);

  // compute unifier for selected literals
  RobSubstitution subst;
  Literal *selectedLeft = inf.extra.selectedLiteral.selectedLiteral;
  Literal *selectedRight = inf.extra.otherLiteral;
  ASS_NEQ(selectedLeft->polarity(), selectedRight->polarity())
  ALWAYS(subst.unify(TermList(selectedLeft), 0, TermList(selectedRight), 1));

  // apply subst to all of the parent literals in the same order as BinaryResolution does it
  applySubstToClause(subst, 0, inf.left, selectedLeft);
  applySubstToClause(subst, 1, inf.right, selectedRight);
  Literal *leftSelectedSubst = subst.apply(selectedLeft, 0);
  Literal *rightSelectedSubst = subst.apply(selectedRight, 1);

  for(auto [v, sort] : inf.leftVars)
    out << " " << DkTerm(subst.apply(TermList(v, false), 0), sort, inf);
  unsigned litLeft;
  for(litLeft = 0; (*inf.left)[litLeft] != selectedLeft; litLeft++)
    out << " " << DkLitPtr((*inf.left)[litLeft], inf, DoRobSubstitution0(subst));

  const char *tp = "tp", *tnp = "tnp";
  if(selectedLeft->isNegative())
    std::swap(tp, tnp);

  out << " (" << tp << ": (Prf " << DkLit(leftSelectedSubst, inf) << ") => ";
  parentWithSplits(out, inf.right);
  for(auto [v, sort] : inf.rightVars)
    out << " " << DkTerm(subst.apply(TermList(v, false), 1), sort, inf);
  unsigned litRight;
  for(litRight = 0; (*inf.right)[litRight] != selectedRight; litRight++)
    out << " " << DkLitPtr((*inf.right)[litRight], inf, DoRobSubstitution1(subst));
  out << " (" << tnp << ": Prf " << DkLit(rightSelectedSubst, inf) << " => (tnp tp))";
  for(litRight++; litRight < inf.right->length(); litRight++)
    out << " " << DkLitPtr((*inf.right)[litRight], inf, DoRobSubstitution1(subst));
  out << ")";
  for(litLeft++; litLeft < inf.left->length(); litLeft++)
    out << " " << DkLitPtr((*inf.left)[litLeft], inf, DoRobSubstitution0(subst));
}

static void subsumptionResolution(std::ostream &out, Clause *derived) {
  BinaryClausalInference<Inferences::LiteralInferenceExtra> inf(out, derived);

  // reconstruct match by calling into the SATSR code
  Literal *m = inf.extra.selectedLiteral;
  SATSubsumption::SATSubsumptionAndResolution satSR;
  ALWAYS(satSR.checkSubsumptionResolutionWithLiteral(inf.right, inf.left, inf.left->getLiteralPosition(m)))
  auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();

  // TODO this should be more or less the 'resolution' term, but with multiple tnp/tp lambdas factored out
  // Anja is a smart cookie

  // NB no substitution as `left` is subsumed
  for(auto [v, sort] : inf.leftVars)
    out << " " << DkVar(v, sort, inf);

  // TODO can we make this case distinction less unpleasant?
  if(m->isPositive()) {
    for(Literal *l : inf.left->iterLits()) {
      out << " ";
      if(l != m) {
        out << l;
        continue;
      }

      out << "(tp: (Prf " << DkLit(m, inf) << ") => ";
      parentWithSplits(out, inf.right);
      for(auto [v, sort] : inf.rightVars)
        out << " " << DkTerm(SubstHelper::apply(TermList(v, false), subst), sort, inf);
      for(Literal *k : inf.right->iterLits()) {
        out << " ";
        Literal *ksubst = SubstHelper::apply(k, subst);
        if(Literal::complementaryLiteral(ksubst) != m) {
          out << DkLitPtr(k, inf, DoSubstitution(subst));
          continue;
        }
        out << "(tnp: Prf " << DkLit(k, inf, DoSubstitution(subst)) << " => (";
        outputLiteralName(out, k, "tnp", "comml", inf, DoSubstitution(subst));
        out << " tp))";
      }
      out << ")";
    }
  }
  else {
    for(Literal *l : inf.left->iterLits()) {
      out << " ";
      if(l != m) {
        out << l;
        continue;
      }

      out << "(tnp: (Prf " << DkLit(m, inf) << ") => ";
      parentWithSplits(out, inf.right);
      for(auto [v, sort] : inf.rightVars)
        out << " " << DkTerm(SubstHelper::apply(TermList(v, false), subst), sort, inf);
      for(Literal *k : inf.right->iterLits()) {
        out << " ";
        Literal *ksubst = SubstHelper::apply(k, subst);
        if(Literal::complementaryLiteral(ksubst) != m) {
          out << DkLitPtr(k, inf, DoSubstitution(subst));
          continue;
        }
        out << "(tp: Prf " << DkLit(k, inf, DoSubstitution(subst)) << " => (tnp ";
        outputLiteralName(out, k, "tp", "comm", inf, DoSubstitution(subst));
        out << "))";
      }
      out << ")";
    }
  }
}

static void superposition(std::ostream &out, Clause *derived) {
  BinaryClausalInference<Inferences::SuperpositionExtra> inf(out, derived);

  // compute unifier for selected literals
  RobSubstitution subst;
  Literal *leftSelected = inf.extra.selected.selectedLiteral.selectedLiteral;
  Literal *rightSelected = inf.extra.selected.otherLiteral;
  TermList from = inf.extra.rewrite.lhs;
  TermList to = EqHelper::getOtherEqualitySide(rightSelected, from);
  TermList sort = SortHelper::getEqualityArgumentSort(rightSelected);
  bool fromisLHS = rightSelected->termArg(0) == from;
  TermList target = inf.extra.rewrite.rewritten;
  ASS(rightSelected->isEquality())
  ASS(rightSelected->isPositive())
  ASS(rightSelected->termArg(0) == from || rightSelected->termArg(1) == from)
  ALWAYS(subst.unify(target, 0, from, 1))

  // apply subst to all of the parent literals in the same order as Superposition does it
  subst.apply(to, 1);
  subst.apply(leftSelected, 0);
  subst.apply(target, 0);
  subst.apply(from, 1);
  applySubstToClause(subst, 0, inf.left, leftSelected);
  applySubstToClause(subst, 1, inf.right, rightSelected);

  TermList fromSubst = subst.apply(from, 1);
  TermList toSubst = subst.apply(to, 1);
  TermList sortSubst = subst.apply(sort, 1);

  for(auto [v, sort] : inf.leftVars)
    out << " " << DkTerm(subst.apply(TermList(v, false), 0), sort, inf);
  for(Literal *litLeft : inf.left->iterLits()) {
    out << " ";
    if(derived->contains(subst.apply(litLeft, 0))) {
      out << DkLitPtr(litLeft, inf, DoRobSubstitution0(subst));
      continue;
    }

    out << " (q : (Prf (" << DkLit(litLeft, inf, DoRobSubstitution0(subst)) << ")) => ";
    parentWithSplits(out, inf.right);

    for(auto [v, sort] : inf.rightVars)
      out << " " << DkTerm(subst.apply(TermList(v, false), 1), sort, inf);
    unsigned litRight;
    for(litRight = 0; (*inf.right)[litRight] != rightSelected; litRight++)
      out << " " << DkLitPtr((*inf.right)[litRight], inf, DoRobSubstitution1(subst));

    out
      << " (r : (Prf " << DkLit(rightSelected, inf, DoRobSubstitution1(subst)) << ") => "
      << DkLitPtr(litLeft, inf, DoRobSubstitution0(subst).then(DoReplacement(fromSubst, toSubst)))
      << " (";

    if(!fromisLHS)
      out
        << "comm "
        << DkTerm(sortSubst, AtomicSort::superSort(), inf) << " "
        << DkTerm(toSubst, sortSubst, inf) << " "
        << DkTerm(fromSubst, sortSubst, inf) << " ";
    out << "r (z : (El " << DkTerm(sortSubst, AtomicSort::superSort()) << ") => ";

    TermList z(0, true);
    out << DkLit(litLeft, inf, DoRobSubstitution0(subst).then(DoReplacement(fromSubst, z))) << ") q))";

    for(litRight++; litRight < inf.right->length(); litRight++)
      out << " " << DkLitPtr((*inf.right)[litRight], inf, DoRobSubstitution1(subst));
    out << ")";
  }
}

// check whether `demodulator` l = r rewrites left-to-right in the context of C[t] -> C[s]
static bool isL2RDemodulatorFor(Literal *demodulator, Clause *rewritten, TermList target, Clause *result) {
  ASS(demodulator->isEquality())
  ASS(demodulator->isPositive())

  // TODO this is waaay overkill, but it's very hard to work out which way a demodulator was used
  // consult MH about how best to do this
  SimpleSubstitution subst;
  if(!MatchingUtils::matchTerms(demodulator->termArg(0), target, subst))
    return false;
  TermList rhsSubst = SubstHelper::apply(demodulator->termArg(1), subst);

  for(Literal *l : rewritten->iterLits())
    if(!result->contains(l) && !result->contains(EqHelper::replace(l, target, rhsSubst)))
      return false;

  return true;
}

static void demodulation(std::ostream &out, Clause *derived) {
  BinaryClausalInference<Inferences::RewriteInferenceExtra> inf(out, derived);

  // compute match for demodulation
  ASS_EQ(inf.right->length(), 1)
  SimpleSubstitution subst;
  Literal *rightLit = (*inf.right)[0];
  TermList target = inf.extra.rewritten;
  TermList from = isL2RDemodulatorFor(rightLit, inf.left, target, derived)
    ? rightLit->termArg(0)
    : rightLit->termArg(1);
  TermList to = EqHelper::getOtherEqualitySide(rightLit, from);
  TermList sort = SortHelper::getEqualityArgumentSort(rightLit);
  bool fromisLHS = rightLit->termArg(0) == from;
  ASS(rightLit->isEquality())
  ASS(rightLit->isPositive())
  ASS(rightLit->termArg(0) == from || rightLit->termArg(1) == from)
  ALWAYS(MatchingUtils::matchTerms(from, target, subst))

  // also apply subst to the selected literals because we need it later
  TermList toSubst = SubstHelper::apply(to, subst);
  TermList sortSubst = SubstHelper::apply(sort, subst);

  for(auto [v, sort] : inf.leftVars)
    out << " " << DkVar(v, sort, inf);
  for(Literal *litLeft : inf.left->iterLits()) {
    out << " ";
    if(derived->contains(litLeft)) {
      out << litLeft;
      continue;
    }

    out << " (q : (Prf (" << DkLit(litLeft, inf) << ")) => ";
    parentWithSplits(out, inf.right);

    for(auto [v, sort] : inf.rightVars)
      out << " " << DkTerm(subst.apply(v), SubstHelper::apply(sort, subst), inf);
    out
      << " (r : (Prf " << DkLit(rightLit, inf, DoSubstitution(subst)) << ") => "
      << DkLitPtr(litLeft, inf, DoReplacement(target, toSubst)) << " (";

    if(!fromisLHS)
      out
        << "comm "
        << DkTerm(sortSubst, AtomicSort::superSort()) << " "
        << DkTerm(toSubst, sortSubst, inf) << " "
        << DkTerm(target, sortSubst, inf) << " ";
    out << "r (z : (El " << DkTerm(sortSubst, AtomicSort::superSort()) << ") => ";

    TermList z(0, true);
    out << DkLit(litLeft, inf, DoReplacement(target, z)) << ") q)))";
  }
}

static void definitionUnfolding(std::ostream &out, Clause *derived) {
  VariadicClausalInference<Inferences::FunctionDefinitionExtra> inf(out, derived);

  for(auto [v, sort] : inf.derivedVars)
    out << " " << DkVar(v, sort, inf);

  std::unordered_map<unsigned, unsigned> rewrites;
  for(unsigned i = 0; i < inf.others.size(); i++)
    rewrites.insert({inf.extra.lhs[i]->functor(), i});

  std::vector<std::string> after;
  for(Literal *l : inf.parent->iterLits()) {
restart:
    out << " (t_" << l << " : Prf " << DkLit(l, inf) << " =>";
    NonVariableNonTypeIterator subterms(l);
    while(subterms.hasNext()) {
      Term *candidate = subterms.next();
      if(auto found = rewrites.find(candidate->functor()); found != rewrites.end()) {
        auto [_, i] = *found;
        Clause *def = inf.others[i];
        Literal *eq = (*def)[0];
        TermList lhs(inf.extra.lhs[i]);
        TermList rhs = EqHelper::getOtherEqualitySide(eq, lhs);
        TermList sort = SortHelper::getEqualityArgumentSort(eq);
        SimpleSubstitution subst;
        //std::cout << lhs << " onto " << *candidate << "??" << std::endl;
        ALWAYS(MatchingUtils::matchTerms(TermList(lhs), TermList(candidate), subst))
        TermList lhsSubst(SubstHelper::apply(lhs, subst));
        TermList rhsSubst = SubstHelper::apply(rhs, subst);
        TermList sortSubst = SubstHelper::apply(sort, subst);
        parentWithSplits(out, def);

        auto defVars = VarsWithSorts(def);
        for(auto [v, sort] : defVars)
          out << " " << DkTerm(subst.apply(v), sortSubst, inf);
        out << " (e_" << eq << " : Prf " << DkLit(eq, inf, DoSubstitution(subst)) << " => ";

        std::stringstream deferred;

        DoReplacement transform(lhsSubst, rhsSubst);
        Literal *lAfter = transform(l);

        // decide if needs commutation
        bool needs_comm = false;
        if(l->isEquality()) {
          TermList eqSort = SortHelper::getEqualityArgumentSort(l);
          TermList leftAfter = transform(l->termArg(0));
          TermList rightAfter = transform(l->termArg(1));
          needs_comm = lAfter->termArg(0) != leftAfter || lAfter->termArg(1) != rightAfter;

          if (needs_comm)
            deferred
              << "(comm" << (lAfter->polarity() ? "" : "l") << " "
              << DkTerm(eqSort, AtomicSort::superSort(), inf) << " "
              << DkTerm(leftAfter, sortSubst, inf) << " "
              << DkTerm(rightAfter, sortSubst, inf);
        }

        deferred << " (";
        if(eq->termArg(0) == lhs)
          deferred << "e_" << eq;
        else
          deferred
            << "(comm "
            << DkTerm(sortSubst, AtomicSort::superSort(), inf) << " "
            << DkTerm(SubstHelper::apply(eq->termArg(0), subst), sortSubst, inf) << " "
            << DkTerm(SubstHelper::apply(eq->termArg(1), subst), sortSubst, inf)
            << " e_" << eq << ")";
        deferred
          << " (z : El " << DkTerm(sortSubst, AtomicSort::superSort()) << " => "
          << DkLit(l, inf, DoReplacement(lhsSubst, TermList(0, true)))
          << ") t_" << l << ")))";
        if(needs_comm)
          deferred << ")";
        l = lAfter;

        after.push_back(deferred.str());
        goto restart;
      }
    }
    out << " " << l << " t_" << l << ")";
    while(!after.empty()) {
      out << after.back();
      after.pop_back();
    }
  }
}

static void trivialInequalityRemoval(std::ostream &out, Clause *derived) {
  UnaryClausalInference<std::nullptr_t> inf(out, derived);

  for(auto [v, sort] : inf.parentVars)
    out << " " << DkVar(v, sort, inf);
  for(Literal *l : inf.parent->iterLits())
    if(l->isEquality() && !l->polarity() && l->termArg(0) == l->termArg(1)) {
      TermList sort = SortHelper::getEqualityArgumentSort(l);
      out
        << " (p : Prf (" << DkLit(l, inf) << ") => p (refl "
        << DkTerm(sort, AtomicSort::superSort(), inf) << ' '
        << DkTerm(l->termArg(0), sort, inf)
        << "))";
    }
    else
      out << ' ' << l;
}

static void equalityResolution(std::ostream &out, Clause *derived) {
  UnaryClausalInference<Inferences::EqualityResolutionExtra> inf(out, derived);

  // compute unifier
  RobSubstitution subst;
  Literal *selected = inf.extra.selectedLiteral;
  ASS(selected->isEquality())
  ASS(selected->isNegative())
  TermList sort = SortHelper::getEqualityArgumentSort(selected);
  TermList s = selected->termArg(0), t = selected->termArg(1);
  ALWAYS(subst.unify(s, 0, t, 0));

  // apply subst to all of the parent literals in the same order as EqualityResolution does it
  applySubstToClause(subst, 0, inf.parent, selected);
  TermList sortSubst = subst.apply(sort, 0);

  for(auto [v, sort] : inf.parentVars)
    out << " " << DkTerm(subst.apply(TermList(v, false), 0), sortSubst, inf);
  unsigned lit;
  for(lit = 0; (*inf.parent)[lit] != selected; lit++)
    out << " " << DkLitPtr((*inf.parent)[lit], inf, DoRobSubstitution0(subst));

  out
    << " (p : Prf ("
    << DkLit(subst.apply(selected, 0), inf)
    << ") => p (refl "
    << DkTerm(sortSubst, AtomicSort::superSort(), inf) << ' '
    << DkTerm(subst.apply(s, 0), sortSubst, inf)
    << "))";

  for(lit++; lit < inf.parent->length(); lit++)
    out << " " << DkLitPtr((*inf.parent)[lit], inf, DoRobSubstitution0(subst));
}

static void equalityResolutionWithDeletion(std::ostream &out, Clause *derived) {
  UnaryClausalInference<Inferences::EqResWithDeletionExtra> inf(out, derived);

  // compute unifier
  SimpleSubstitution subst;
  for(Literal *l : inf.extra.resolved) {
    ASS(l->isNegative())
    ASS(l->isEquality())

    TermList s = l->termArg(0), t = l->termArg(1);
    ASS(s.isVar() || t.isVar())
    bool lhs = s.isVar() && !t.containsSubterm(s);
    if(!lhs)
      std::swap(s, t);
    ASS(s.isVar() && !t.containsSubterm(s))
    ALWAYS(subst.bind(s.var(), t))
  }

  for(auto [v, sort] : inf.parentVars)
    out << " " << DkTerm(subst.apply(v), SubstHelper::apply(sort, subst), inf);
  for(Literal *l : inf.parent->iterLits()) {
    out << " ";
    if(!inf.extra.resolved.count(l)) {
      out << DkLitPtr(l, inf, DoSubstitution(subst));
      continue;
    }
    TermList sort = SortHelper::getEqualityArgumentSort(l);
    out
      << " (p : Prf ("
      << DkLit(SubstHelper::apply(l, subst), inf)
      << ") => p (refl "
      << DkTerm(sort, AtomicSort::superSort(), inf) << ' '
      << DkTerm(SubstHelper::apply(l->termArg(0), subst), SubstHelper::apply(sort, subst), inf)
      << "))";
  }
}

static void duplicateLiteral(std::ostream &out, Clause *derived) {
  UnaryClausalInference<std::nullptr_t> inf(out, derived);

  for(auto [v, sort] : inf.derivedVars)
    out << " " << DkVar(v, sort);
  for(Literal *l : inf.parent->iterLits())
    out << " " << l;
}

static void factoring(std::ostream &out, Clause *derived) {
  UnaryClausalInference<Inferences::FactoringExtra> inf(out, derived);

  // compute unifier for selected literal
  RobSubstitution subst;
  Literal *selected = inf.extra.selectedLiteral.selectedLiteral;
  Literal *other = inf.extra.otherLiteral;
  ASS_EQ(selected->polarity(), other->polarity())
  ASS_EQ(selected->functor(), other->functor())
  ALWAYS(subst.unify(TermList(selected), 0, TermList(other), 0));

  // apply subst to all of the parent literals in the same order as Factoring does it
  applySubstToClause(subst, 0, inf.parent, other);

  for(auto [v, sort] : inf.parentVars)
    out << " " << DkTerm(subst.apply(TermList(v, false), 0), subst.apply(sort, 0), inf);
  for(Literal *l : inf.parent->iterLits())
    out << " " << DkLitPtr(l, inf, DoRobSubstitution0(subst));
}

static void AVATARDefinition(std::ostream &out, Unit *def) {
  Clause *component = env.proofExtra.get<SplitDefinitionExtra>(def).component;
  unsigned componentName = component->splits()->sval();
  SATLiteral split = Splitter::getLiteralFromName(componentName);
  out << "def sp" << split.var() << " : Prop :=";

  CloseParens cp(out);
  auto vars = VarsWithSorts(component);
  for(auto [var, sort] : vars)
    out
      << "forall " << DkTerm(sort, AtomicSort::superSort()) << ' '
      << cp.open() << var << " : El " << DkTerm(sort, AtomicSort::superSort())
      << " =>";
  for(Literal *literal : component->iterLits())
    out << cp.open(" (imp ") << "(not " << DkLit(literal) << ")";
  out << " false";
}

static void AVATARComponent(std::ostream &out, Clause *component) {
  ASS(component->splits())
  ASS_EQ(component->splits()->size(), 1)
  deductionPrefix(out, component);

  unsigned componentName = component->splits()->sval();
  SATLiteral split = Splitter::getLiteralFromName(componentName);
  // variables in numerical order
  auto componentVars = VarsWithSorts(component);

  bindClause(out, component, componentVars);
  CloseParens cp(out);
  out << "nnsp" << split.var() << cp.open() << "psp : Prf " << DkSplit(componentName) << " => psp";
  for(auto [v, _] : componentVars)
    out << " " << v;
  for(Literal *l : component->iterLits())
    out << " " << l;
}

static void AVATARSplitClause(std::ostream &out, Unit *derived) {
  UnitIterator parents = derived->getParents();
  ALWAYS(parents.hasNext())
  Clause *parent = parents.next()->asClause();
  SATClause *sat = env.proofExtra.get<SplitClauseExtra>(derived).clause;

  std::unordered_map<unsigned, Clause *> components;
  while(parents.hasNext()) {
    Unit *parent = parents.next();
    auto dex = env.proofExtra.get<SplitDefinitionExtra>(parent);
    ASS(dex.component->isComponent())
    unsigned component = dex.component->splits()->sval();
    components.insert({component, dex.component});
  }

  DHSet<SATLiteral> splitSet;
  if(!parent->noSplits()) {
    SplitSet &splits = *parent->splits();
    for(unsigned i = 0; i < splits.size(); i++)
      splitSet.insert(Splitter::getLiteralFromName(splits[i]));
  }
  std::vector<SATLiteral> existingSplits, newSplits;
  for(unsigned i = 0; i < sat->length(); i++) {
    if(splitSet.contains((*sat)[i]))
      existingSplits.push_back((*sat)[i]);
    else
      newSplits.push_back((*sat)[i]);
  }

  out << "def deduction" << derived->number() << " : Prf_av_clause";
  {
    CloseParens cp(out);
    for(SATLiteral sl : existingSplits)
      out << cp.open(" (if ") << DkSplit(sl);
    out << cp.open(" (acl") << cp.open(" (cl");
    for(SATLiteral sl : newSplits)
      out << cp.open(" (cons ") << DkSplit(sl);
    out << " ec";
  }
  out << " :=";

  Stack<LiteralStack> disjointLiterals;
  if(!Splitter::getComponents(parent, disjointLiterals)) {
    disjointLiterals.reset();
    LiteralStack component;
    for(Literal *l : parent->iterLits())
      component.push(l);
    disjointLiterals.push(std::move(component));
  }

  for(SATLiteral l : existingSplits)
    out << " nnsp" << l.var() << " : ((Prf " << DkSplit(l) << " -> Prf false) -> Prf false) =>";
  for(SATLiteral l : newSplits)
    out << " nnsp" << l.var() << " : (Prf " << DkSplit(l) << " -> Prf false) =>";

  CloseParens cp(out);
  decltype(disjointLiterals)::Iterator classes(disjointLiterals);
  // map variables in the parent to corresponding variables in the child splits
  SimpleSubstitution parent2SplitVars;
  while(classes.hasNext()) {
    LiteralStack klass = classes.next();
    Clause *found = nullptr;
    SimpleSubstitution subst;
    bool flip = false;
    for(auto [name, component] : components) {
      if(klass.size() == component->length()) {
        subst.reset();
        if(klass.size() == 1 && klass[0]->ground() && Literal::positiveLiteral(klass[0]) == Literal::positiveLiteral((*component)[0])) {
          found = component;
          flip = klass[0] != (*component)[0];
          break;
        }
        if(MLVariant::isVariant(klass.begin(), component, /*complementary=*/false, &subst)) {
          found = component;
          break;
        }
      }
    }
    ASS(found)

    SATLiteral split = Splitter::getLiteralFromName(found->splits()->sval());
    out << " nnsp" << split.var();
    for(auto [foundVar, foundSort] : VarsWithSorts(found)) {
      out
        << cp.open(" (") << subst.apply(foundVar).var()
        << " : El " << DkTerm(SubstHelper::apply(foundSort, subst), AtomicSort::superSort())
        << " =>";
      ALWAYS(parent2SplitVars.bind(subst.apply(foundVar).var(), TermList(foundVar, false)))
    }
    for(Literal *l : found->iterLits()) {
      if(flip)
        l = Literal::complementaryLiteral(l);
      out
        << cp.open(" (") << SubstHelper::apply(l, subst) << " : (Prf "
        << DkLit(l, AlwaysCare {}, DoSubstitution(subst))
        << " -> Prf false) =>";
    }
  }

  out << " deduction" << parent->number();
  // basically outputParentWithSplits() but NB comment below
  if(!parent->noSplits()) {
    SplitSet &splits = *parent->splits();
    for(unsigned i = 0; i < splits.size(); i++) {
      SATLiteral l = Splitter::getLiteralFromName(splits[i]);
      // if there is *already* a split in the parent (and it's negative),
      // need to double-negate it in order to match what the parent expects
      if(!l.polarity())
        out
          << "(nnnsp" << l.var() << " : (Prf (not sp" << l.var() << ") -> Prf false) =>"
          << "nnnsp" << l.var() << " nnsp" << l.var() << ")";
      else
        out << " nnsp" << l.var();
    }
  }

  for(auto [parentVar, _] : VarsWithSorts(parent))
    out << " " << parentVar;
  for(Literal *l : parent->iterLits()) {
    out << ' ';
    Literal *lsubst = SubstHelper::apply(l, parent2SplitVars);
    bool needs_commute = l->isEquality() && (
         SubstHelper::apply((*l)[0], parent2SplitVars) != (*lsubst)[0]
      || SubstHelper::apply((*l)[1], parent2SplitVars) != (*lsubst)[1]);
    if(needs_commute) {
      TermList sort = SortHelper::getEqualityArgumentSort(l);
      out << "(comml";
      if(!l->polarity())
        out << "_not";
      out << ' '
        << DkTerm(sort, AtomicSort::superSort()) << ' '
        << DkTerm((*l)[1], sort) << ' '
        << DkTerm((*l)[0], sort) << ' ';
    }
    out << l;
    if(needs_commute)
      out << ")";
  }
}

static void AVATARContradictionClause(std::ostream &out, Unit *contradiction) {
  UnitIterator it = contradiction->getParents();
  ALWAYS(it.hasNext())
  Clause *parent = it.next()->asClause();
  out
    << "def deduction" << contradiction->number() << " : "
    << DkClause(parent) << " := deduction" << parent->number();
}

namespace Shell {
namespace Dedukti {

void outputPrelude(std::ostream &out) {
  out << PRELUDE;
}

void outputTypeDecl(std::ostream &out, const std::string &name, OperatorType *type) {
  out << DkName(name) << ":";

  TermList range = type->result();
  // special-case type constructors
  if(range == AtomicSort::superSort()) {
    for(unsigned i = 0; i < type->arity(); i++)
      out << " Set ->";
    out << " Set.\n";
    return;
  }

  for(unsigned i = 0; i < type->numTypeArguments(); i++)
    out << ' ' << i << " : Set ->";
  for(unsigned i = type->numTypeArguments(); i < type->arity(); i++)
    out << " El " << DkTerm(type->arg(i), AtomicSort::superSort()) << " ->";

  // predicate
  if(range.isEmpty())
    out << " Prop";
  // function
  else
    out << " El " << DkTerm(range, AtomicSort::superSort());

  out << ".\n";
}

void outputAxiom(std::ostream &out, Unit *axiom) {
  axiomName(out, axiom);
  out << ": " << DkUnit(axiom) << ".\n";
}

void outputDeduction(std::ostream &out, Unit *u) {
  switch(u->inference().rule())
  {
  case InferenceRule::INPUT:
    if(u->inputType() == UnitInputType::CONJECTURE)
      return;
  case InferenceRule::NEGATED_CONJECTURE:
    outputAxiom(out, u);
    deductionPrefix(out, u);
    axiomName(out, u);
    break;
  case InferenceRule::DEFINITION_UNFOLDING:
    definitionUnfolding(out, u->asClause());
    break;
  case InferenceRule::RESOLUTION:
    resolution(out, u->asClause());
    break;
  case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    duplicateLiteral(out, u->asClause());
    break;
  case InferenceRule::FACTORING:
    factoring(out, u->asClause());
    break;
  case InferenceRule::SUBSUMPTION_RESOLUTION:
    subsumptionResolution(out, u->asClause());
    break;
  case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    trivialInequalityRemoval(out, u->asClause());
    break;
  case InferenceRule::EQUALITY_RESOLUTION:
    equalityResolution(out, u->asClause());
    break;
  case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    equalityResolutionWithDeletion(out, u->asClause());
    break;
  case InferenceRule::SUPERPOSITION:
    superposition(out, u->asClause());
    break;
  case InferenceRule::FORWARD_DEMODULATION:
  case InferenceRule::BACKWARD_DEMODULATION:
    demodulation(out, u->asClause());
    break;
  case InferenceRule::AVATAR_DEFINITION:
    AVATARDefinition(out, u);
    break;
  case InferenceRule::AVATAR_COMPONENT:
    AVATARComponent(out, u->asClause());
    break;
  case InferenceRule::AVATAR_SPLIT_CLAUSE:
    AVATARSplitClause(out, u);
    break;
  case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    AVATARContradictionClause(out, u);
    // TODO just the identity function
    break;
  case InferenceRule::AVATAR_REFUTATION:
    // TODO
    return;
  default:
    sorry(out, u);
  }
  out << ".\n";
}
}
}

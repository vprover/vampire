#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__CPP__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__CPP__

#include <algorithm>
#include <functional>
#include <iostream>
#include <type_traits>
#include <unordered_map>

#include "Debug/Assertion.hpp"
#include "Debug/PrintDebug.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/macro_magic.h"
#include "Shell/Analysis/TheorySubclauseAnalyser.hpp"
#define ASS_(x) if (!(x)) {cout << endl << "######################### ASSERTION violation " << #x << endl; throw "assertion violation";}
#if VDEBUG
#define ASS_REP_(x, v) if (!(x)) {cout << endl << "######################### ASSERTION violation " << #x << endl; cout << v << endl; throw;}
#else
#define ASS_REP_(x, v) if (!(x)) {cout << endl << "######################### ASSERTION violation " << #x << endl; cout << v << endl;}
#endif
// #define ASS_(x) ASS(x)

struct ClauseRest;

template<class A>
struct optional {
  bool _present;
  A _elem;
  bool present() const {return _present;}
  const A& get() const {
    ASS(present());
    return _elem;
  }
  A& get() {
    ASS(present());
    return _elem;
  }
  explicit optional(A a) : _present(true), _elem(a) {}
  optional() : _present(false) {}
};

bool isTheoryLiteral(const Literal &lit);
ostream &operator<<(ostream &out, const AbsLiteral &lit);
ostream &operator<<(ostream &out, const AbsClause &lit);

#define _TAIL(x, ...) __VA_ARGS__

using namespace Shell::Analysis;
using namespace std;
using namespace Kernel;

using Interpretation = Theory::Interpretation;

struct rect_maps;

struct rect_map {
private:
  unsigned n_vars;
  vumap<unsigned, unsigned> map;

public:
  rect_map() : n_vars(0), map(vumap<unsigned, unsigned>()) {}
  AbsVarTerm get(const AbsVarTerm& v) ;
};

template <class A, class Config> struct gen_comparator {
  CmpResult operator()(const A &l, const A &r, rect_maps &map) const;

  template <class B>
  CmpResult cmp(const B &lhs, const B &rhs, rect_maps &map) const {
    return gen_comparator<B, Config>{}(lhs, rhs, map);
  }
};

template <class A, class Config> struct state_wrapped_comparator_std {
  rect_maps &map;
  state_wrapped_comparator_std(rect_maps &map) : map(map) {}
  bool operator()(A const &l, A const &r) {
    return gen_comparator<A, Config>{}(l, r, map) == CMP_LESS;
  }
};

template <class Config> struct state_wrapped_comparator_poly {
  rect_maps &map;
  state_wrapped_comparator_poly(rect_maps &map) : map(map) {}
  template <class B> CmpResult cmp(const B &l, const B &r) {
    return gen_comparator<B, Config>{}(l, r, map);
  }
};

struct rect_maps {
  rect_map l;
  rect_map r;
  rect_maps() : l(rect_map()), r(rect_map()) {}
};

template <class A> CmpResult compare_ground(A l, A r) {
  if (l < r)
    return CMP_LESS;
  if (l > r)
    return CMP_GREATER;
  return CMP_EQUIV;
}

template<class Container, class Config>
CmpResult gen_compare_container(const Container &lhs, const Container &rhs,
                     rect_maps &map) {
  using A = typename Container::value_type;
  auto li = lhs.begin();
  auto ri = rhs.begin();
  while (li != lhs.end() && ri != rhs.end()) {
    auto l = *li;
    auto r = *ri;
    auto c = gen_comparator<A, Config>{}(l, r, map);
    switch (c) {
    case CMP_NONE:
    case CMP_LESS:
    case CMP_GREATER:
      return c;
    case CMP_EQUIV:;
    }
    li++;
    ri++;
  }
  auto lend = li == lhs.end();
  auto rend = ri == rhs.end();
  if (!lend && rend)
    return CMP_LESS;
  if (lend && !rend)
    return CMP_GREATER;

  return CMP_EQUIV;
}

#define IMPL_GEN_COMPARE_CONTAINER(container) \
  template <class A, class Config> struct gen_comparator<container<A>, Config> { \
    CmpResult operator()(const container<A> &lhs, const container<A> &rhs, \
                         rect_maps &map) const { \
      return gen_compare_container<container<A>, Config>(lhs,rhs, map); \
    } \
  }; 

IMPL_GEN_COMPARE_CONTAINER(vvec)

template <class A, class Config> struct gen_comparator<optional<A>, Config> { 
  using container = optional<A>;
  CmpResult operator()(const container &lhs, const container &rhs, 
                       rect_maps &map) const { 

    if (lhs.present() && rhs.present()) 
      return gen_comparator<A, Config>{}(lhs.get(), rhs.get(), map); 
    if (!lhs.present() && rhs.present()) return CMP_LESS;
    if (lhs.present() && !rhs.present()) return CMP_GREATER;
    return CMP_EQUIV;
  } 
}; 

template <class A, class Config> struct gen_comparator<refw<A>, Config> {
  CmpResult operator()(const refw<A> &lhs, const refw<A> &rhs,
                       rect_maps &map) const {
    const A &l = lhs.get();
    const A &r = rhs.get();
    return gen_comparator<A, Config>{}(l, r, map);
  }
};

template <class A, class Config> struct gen_comparator<rc<A>, Config> {
  CmpResult operator()(const rc<A> &lhs, const rc<A> &rhs,
                       rect_maps &map) const {
    const A &l = *lhs.get();
    const A &r = *rhs.get();
    return gen_comparator<A, Config>{}(l, r, map);
  }
};

/** ============= lexicographical comparison ================== **/

namespace __lex_cmp {

template <class Fn, class A, class... Fs> struct lex_ {
  static CmpResult cmp(Fn f, A l, A h, Fs... fs);
};

template <class Fn, class A> struct lex_<Fn, A> {
  static CmpResult cmp(Fn f, A l, A r) { return CMP_EQUIV; }
};

template <class Fn, class A, class F, class... Fs>
struct lex_<Fn, A, F, Fs...> {
  static CmpResult cmp(Fn cmp, A l, A r, F field, Fs... rest) {
    auto c = cmp.template cmp<decltype(field(l))>(field(l), field(r));
    switch (c) {
    case CMP_LESS:
    case CMP_GREATER:
    case CMP_NONE:
      return c;
    case CMP_EQUIV:
      return lex_<Fn, A, Fs...>::cmp(cmp, l, r, rest...);
    }
  }
};

} // namespace __lex_cmp

template <class Fn, class A, class... Fs>
CmpResult lex_cmp(Fn f, A l, A r, Fs... fs) {
  return __lex_cmp::lex_<Fn, A, Fs...>::cmp(f, l, r, fs...);
}

/** ============= subclass comparison ================== **/

namespace __subclass_cmp {
template <class Fn, class A, class... Bs> struct _subclass_cmp {
  static CmpResult cmp(Fn f, const A &lhs, const A &rhs);
};

template <class Fn, class A> struct _subclass_cmp<Fn, A> {
  static CmpResult cmp(Fn f, const A &lhs, const A &rhs) { ASSERTION_VIOLATION }
};

template <class Fn, class A, class B, class... Bs>
struct _subclass_cmp<Fn, A, B, Bs...> {
  static CmpResult cmp(Fn f, const A &l, const A &r) {
    const B *lhs = dynamic_cast<const B *>(&l);
    const B *rhs = dynamic_cast<const B *>(&r);
    if (lhs && rhs) {
      return f.template cmp<B>(*lhs, *rhs);
    } else if (lhs && !rhs) {
      return CMP_LESS;
    } else if (!lhs && rhs) {
      return CMP_GREATER;
    } else {
      return _subclass_cmp<Fn, A, Bs...>::cmp(f, l, r);
    }
  }
};
} // namespace __subclass_cmp

template <class Fn, class A, class... As>
CmpResult subclass_cmp(Fn f, const A &lhs, const A &rhs) {
  return __subclass_cmp::_subclass_cmp<Fn, A, As...>::cmp(f, lhs, rhs);
}

/** ============= subclass comparison ================== **/

#define TIE_OP(OP, CLASS, ...)                                                 \
  inline friend bool operator OP(const CLASS &l, const CLASS &r) {             \
    auto toTup = [](const CLASS &x) { return std::make_tuple(__VA_ARGS__); };  \
    return toTup(l) OP toTup(r);                                               \
  }

#define OPERATORS(CLASS, ...)                                                  \
  TIE_OP(<, CLASS, __VA_ARGS__)                                                \
  TIE_OP(>, CLASS, __VA_ARGS__)                                                \
  TIE_OP(<=, CLASS, __VA_ARGS__)                                               \
  TIE_OP(>=, CLASS, __VA_ARGS__)                                               \
  TIE_OP(==, CLASS, __VA_ARGS__)

/** ============= utility term datatypes ================== **/

class AbsSymbol {
protected:
  unsigned functor;

  explicit AbsSymbol(unsigned functor) : functor(functor) {}

public:
  friend ostream &operator<<(ostream &out, const AbsSymbol &s);

  virtual Signature::Symbol &symbol() const = 0;

  Theory::Interpretation interpret() const {
    return symbol().getInterpretation();
  }
  bool interpreted() const {
    return interpret() != Theory::INVALID_INTERPRETATION;
  }


  template <class A, class Config> friend struct gen_comparator;
  OPERATORS(AbsSymbol, x.functor)
};

ostream &operator<<(ostream &out, const AbsSymbol &s) {
  out << s.symbol().name();
  return out;
}

Theory::Interpretation interpretation(Signature::Symbol &sym) {
  return sym.getInterpretation();
}

class Predicate : public AbsSymbol {
public:
  explicit Predicate(unsigned functor) : AbsSymbol(functor) {}

  Signature::Symbol &symbol() const override {
    return *env.signature->getPredicate(functor);
  }

  bool isEquality() const { return interpret() == Interpretation::EQUAL; }

  template <class A, class Config> friend struct gen_comparator;
  OPERATORS(Predicate, x.functor)
};

class Function : public AbsSymbol {
public:
  explicit Function(unsigned functor) : AbsSymbol(functor) {}

  Signature::Symbol &symbol() const override {
    return *env.signature->getFunction(functor);
  }

  bool isPlus() const { return Theory::isPlus(interpret()); }

  bool isTimes() const { return Theory::isTimes(interpret()); }

  bool isAssoc() const {
    auto i = interpret();
    return Theory::isPlus(i) || Theory::isTimes(i);
  }

  bool isCommut() const {
    auto i = interpret();
    return Theory::isPlus(i) || Theory::isTimes(i);
  }

  IntegerConstantType toInt() const {
    IntegerConstantType out;
    ALWAYS(theory->tryInterpretConstant(Term::createConstant(functor), out));
    return out;
  }



  bool leftDistributiveOver(const Function &other) const {
    return Theory::isTimes(this->interpret()) &&
           Theory::isPlus(other.interpret());
  }

  bool isInterpretedConstant() const {
    return Theory::instance()->isInterpretedConstant(functor);
  }

  bool isUnaryMinus() const { return Theory::isUnaryMinus(this->interpret()); }

  IntegerConstantType toIntegerConstant() const {
    IntegerConstantType out;
    Term* trm = Term::createConstant(functor);
    bool res = theory->tryInterpretConstant(trm, out);
    ASS_(res)
    // cout << "%==============================" << out << endl
    return out;
  }

  template <class A, class Config> friend struct gen_comparator;

  OPERATORS(Function, x.functor)
};

class AbsVarTerm : public AbsTerm {
public:
  CLASS_NAME(AbsVarTerm);

  USE_ALLOCATOR(AbsVarTerm);

private:
  unsigned _var;

public:
  friend struct CmpUninterpretedVarsMatch;
  bool interpreted() const override { return false; }
  explicit AbsVarTerm(unsigned var) : _var(var) {}
  ~AbsVarTerm() {}

  inline void write(ostream &out, rect_map &map) const {
    out << "X" << map.get(*this)._var;
  }

  void write(ostream &out) const override { out << "X" << _var; }

  void normalize() override {}
  // void rectify(rect_map &r) override { _var = r.get(_var); }
  void mergeAssoc() override {}
  void sortCommut() override {}
  void distributeLeft() override {}
  void distributeRight() override {}
  void pushMinus() override {}
  void var_set(vset<AbsVarTerm> &v) const override { v.insert(*this); }

  void vars(vvec<unsigned> &v, on_unsigned_t onUninterpreted) const override {
    v.push_back(_var);
  }
  template <class A, class Config> friend struct gen_comparator;
  OPERATORS(AbsVarTerm, x._var)
  friend struct CmpVarsMatch;
  friend struct CmpVarsEqual;
  friend struct rect_map;
  friend void gen_dump(ostream &out, const vset<AbsVarTerm> &rest, rect_map &map);
};

AbsTerm::~AbsTerm() {}

class ACTerm : public AbsTerm {
public:
  CLASS_NAME(ACTerm);
  USE_ALLOCATOR(ACTerm);

private:
  Function _fun;
  typedef vvec<refw<AbsTerm>> args_t;
  args_t _args;

public:
  ACTerm(Function fun, std::initializer_list<refw<AbsTerm>> ts)
      : _fun(fun), _args(args_t(ts)) {}

  ACTerm(Function fun, args_t ts) : _fun(fun), _args(ts) {}
  ~ACTerm() {}

  ACTerm(Term &term) : _fun(term.functor()), _args(args_t()) {
    for (auto i = 0; i < term.arity(); i++) {
      auto &t = AbsTerm::from(*term.nthArgument(i));
      _args.push_back(t);
    }
    ASS_(!term.isSpecial())
    ASS_(!term.isLiteral())
    ASS_REP(!_fun.isUnaryMinus() || _args.size() == 1, term.functionName())
  }

  bool interpreted() const override { return !uninterpreted(); }

  void integrityCheck() {
    for (auto a : _args) {
      if (auto x = dynamic_cast<ACTerm *>(&a.get())) {
        x->integrityCheck();
      }
    }
    ASS_(!_fun.isPlus() || _args.size() > 0)
  }

  bool isNumberConstant() const {
    return Theory::isNumberConstant(_fun.interpret());
  }

  bool uninterpreted() const {
    return _fun.interpret() == Theory::INVALID_INTERPRETATION;
  }

  void normalize() override {
    pushMinus();
    distributeLeft();
    distributeRight();
    mergeAssoc();
    sortCommut();
  }

  // void rectify(rect_map &r) override {
  //   for (auto &t : _args) {
  //     t.get().rectify(r);
  //   }
  // }

  void pushMinus() override {
    CALL("ACTerm::pushMinus")
    if (_fun.isUnaryMinus()) {
      ASS_(_args.size() == 1);
      if (auto x = dynamic_cast<ACTerm *>(&_args[0].get())) {
        auto minus = _fun;
        if (x->_fun.isPlus()) {
          _fun = x->_fun;
          /*  -(x + y + ..) => (-x) + (-y) + ...  */
          _args.clear();
          _args.reserve(x->_args.size());
          for (AbsTerm &a : x->_args) {
            _args.push_back(*new ACTerm(minus, {a}));
          }
          x->_args.clear();
          delete x;

        } else if (x->_fun.isTimes()) {
          /*  -(x * y * ..) => (-x) * y * ...  */
          x->_args[0] =
              *new ACTerm(minus, {x->_args[0]}); // TODO: add * (-1) instead
        }
      }
    }
    for (auto a : _args) {
      a.get().pushMinus();
    }
  }

  bool isInterpretedConstant() const {
    return _fun.isInterpretedConstant() && _args.size() == 0;
  }

  IntegerConstantType toIntegerConstant() const {
    return _fun.toIntegerConstant();
  }

  void sortCommut() override;

  void mergeAssoc() override {
    CALL("ACTerm::mergeAssoc")
    for (auto arg : _args) {
      arg.get().mergeAssoc();
    }

    if (_fun.isAssoc()) { // TODO performance
      vvec<refw<AbsTerm>> new_args;
      new_args.reserve(_args.size());
      for (int i = 0; i < _args.size(); i++) {
        auto arg = dynamic_cast<ACTerm *>(&_args[i].get());
        if (arg && arg->_fun == _fun) {
          /* merge */
          new_args.reserve(new_args.capacity() + arg->_args.size() - 1);
          for (auto arg_ : arg->_args) {
            new_args.push_back(arg_);
          }
          arg->_args.clear();
          //                    delete arg;
        } else {
          /* do not merge */
          new_args.push_back(_args[i]);
        }
      }
      _args.clear();
      _args = new_args;
    }
  }
  vset<AbsVarTerm> var_set() const {
    vset<AbsVarTerm> v;
    var_set(v);
    return v;
  }
  void var_set(vset<AbsVarTerm> &vs) const override {
    for (auto &t : _args) {
      t.get().var_set(vs);
    }
  }

  void vars(vvec<unsigned> &v, on_unsigned_t onUninterpreted) const override {
    if (uninterpreted()) {
      onUninterpreted(*this, v);
    } else {
      for (auto &t : _args) {
        t.get().vars(v, onUninterpreted);
      }
    }
  }

  void distributeLeft() override {
    CALL("ACTerm::distributeLeft")
    distribute(0, 1, [](AbsTerm &x) { x.distributeLeft(); });
  }

  void distributeRight() override {
    CALL("ACTerm::distributeRight")
    distribute(1, 0, [](AbsTerm &x) { x.distributeRight(); });
  }

  template <class Fn> void distribute(size_t fst, size_t snd, Fn rec) {
    if (_args.size() == 2) {
      AbsTerm &l = _args[fst];
      AbsTerm &r_ = _args[snd];
      auto r = dynamic_cast<ACTerm *>(&r_);

      if (r && _fun.leftDistributiveOver(r->_fun)) {
        /*   a * (b + c)  => (a * b) + (a * c)
         *   l   -- r --     -- x --   -- r --
         *   -- this ---     ------ this -----
         */
        ASS_(r->_args.size() == 2);
        auto mul = _fun;
        auto add = r->_fun;
        auto &a = l;
        auto &b = r->_args[fst];
        auto &c = r->_args[snd];

        auto &x = *new ACTerm(mul, {a, b});
        x._args[fst] = a;
        x._args[snd] = b;

        r->_fun = mul;
        r->_args[fst] = a;
        r->_args[snd] = c;

        this->_fun = add;
        this->_args[fst] = x;
        this->_args[snd] = *r;

        rec(x);
        rec(*r);
      } else {

        rec(l);
        rec(r_);
      }
    } else {
      for (AbsTerm &a : _args) {
        rec(a);
      }
    }
  }
  inline bool isInterpreted() const {
    return _fun.interpret() != Theory::INVALID_INTERPRETATION;
  }

public:
  virtual void write(ostream &out) const override;
  template <class A, class Config> friend struct gen_comparator;
  OPERATORS(ACTerm, !x.isInterpreted(), !x.isNumberConstant(), x._fun, x._args)
  template <class D>
  friend void gen_dump(ostream &out, const ACTerm &trm, rect_map &map);
};

template <class F1, class F2> bool matchB(const AbsTerm &term, F1 f1, F2 f2) {
  if (auto t = dynamic_cast<const ACTerm *>(&term)) {
    return f1(*t);
  } else {
    ASS_(dynamic_cast<const AbsVarTerm *>(&term));
    return f2(*static_cast<const AbsVarTerm *>(&term));
  }
}
template <class F1, class F2> void match(const AbsTerm &term, F1 f1, F2 f2) {
  if (auto t = dynamic_cast<const ACTerm *>(&term)) {
    return f1(*t);
  } else {
    ASS_(dynamic_cast<const AbsVarTerm *>(&term));
    return f2(*static_cast<const AbsVarTerm *>(&term));
  }
}
Signature::Symbol &fnSym(const Term &t) {
  return *env.signature->getFunction(t.functor());
}

bool interpretedFun(const Term &t) { return fnSym(t).interpreted(); }
AbsTerm &AbsTerm::from(TermList &t) {
  if (t.isVar()) {
    t.var();
    return *new AbsVarTerm(t.var());
  } else {
    return *new ACTerm(*t.term());
  }
}

#define TRY_CMP(OP, CLASS)                                                     \
  {                                                                            \
    if (auto l = dynamic_cast<const CLASS *>(&lhs)) {                          \
      if (auto r = dynamic_cast<const CLASS *>(&rhs)) {                        \
        const CLASS &l_ = *l;                                                  \
        const CLASS &r_ = *r;                                                  \
        if (l_ OP r_)                                                          \
          return true;                                                         \
      } else {                                                                 \
        return true;                                                           \
      }                                                                        \
    }                                                                          \
  }

/* utility datatypes */
class AbsLiteral {
public:
  CLASS_NAME(AbsLiteral)
  USE_ALLOCATOR(AbsLiteral)

  bool positive;
  Predicate predicate;
  vvec<refw<AbsTerm>> terms; // TODO destructor

  explicit AbsLiteral(Literal *l)
      : positive(l->isPositive()), predicate(l->functor()),
        terms(vvec<refw<AbsTerm>>()) {
    terms.reserve(l->arity());
    for (auto i = 0; i < l->arity(); i++) {
      auto &t = AbsTerm::from(*l->nthArgument(i));
      terms.push_back(t);
    }
  }

  void var_set(vset<AbsVarTerm>& out) const;
  void normalize();
  // void rectify(rect_map& map);

  /**
   * returns whether this is a theory literal. A literal @b lit is a theory
   * literal iff (any of)
   * - the predicate symbol is interpreted
   * - it is an equality literal with at least on theory term
   */
  bool isTheoryLiteral() {
    if (predicate.interpreted()) {
      if (predicate.interpret() == Interpretation::EQUAL) {
        AbsTerm& l = terms[0];
        AbsTerm& r = terms[1];
        return l.interpreted() || r.interpreted();
      } else {
        /* some interpeted predicate */
        return true;
      }
    } else {
      return false;
    }
  }

  AbsLiteral(bool positive, Predicate pred, vvec<refw<AbsTerm>> terms)
      : positive(positive), predicate(pred), terms(terms) {}

  template <class A, class Config> friend struct gen_comparator;

  OPERATORS(AbsLiteral, x.predicate, x.positive, x.terms);
};

struct ClauseRest {
  using varset = vset<AbsVarTerm>;
  varset vars;
  bool moreVars;
  ClauseRest() : vars(varset()), moreVars(false) {}
};

class AbsClause {
  rc<AbsLiteral> _lit;
  optional<ClauseRest> _thryVars;
  optional<ClauseRest> _unintVars;

public:
  CLASS_NAME(AbsClause)
  USE_ALLOCATOR(AbsClause)

  AbsClause( rc<AbsLiteral> lit,
            optional<ClauseRest> thryVars,
            optional<ClauseRest> unintVars 
            ) : _lit(lit), _thryVars(thryVars), _unintVars(unintVars) {}

  static vvec<refw<AbsClause>> abstractions(const Clause& c) { 
    // static Predicate THEORY_CLAUSE_FUNCTOR = Predicate(env.signature->addPredicate("theory", 0));
    // static Predicate UNINT_CLAUSE_FUNCTOR  = Predicate(env.signature->addPredicate("unint", 0));
    vvec<rc<AbsLiteral>> lits;
    lits.reserve(c.length());
    for (int i = 0; i < c.size(); i++) {
      lits.push_back(rc<AbsLiteral>(new AbsLiteral(c[i])));
    }


    decltype(abstractions(c)) out;
    for (int cur = 0; cur < lits.size(); cur++) {
      auto view_vars = vset<AbsVarTerm>();
      auto current = lits[cur];
      current->var_set(view_vars);

      ASS_REP_((!current->predicate.interpreted()
        || current->predicate.interpret() != Interpretation::INT_LESS
        || matchB(current->terms[0],
          [](const ACTerm& t) { return t.isInterpretedConstant() && t.toIntegerConstant() == IntegerConstantType(0); },
          [](const AbsVarTerm&) {return true;}
          )), ( *current ))

      if (current->isTheoryLiteral()) {
        auto add_to_vars = [&] (const rc<AbsLiteral>& lit, optional<ClauseRest>& out) {
          if (!out.present()) {
            out = optional<ClauseRest>(ClauseRest());
          }
          auto intermed = vset<AbsVarTerm>();
          lit->var_set(intermed);
          for (auto v : view_vars) {
            if (intermed.find(v) != intermed.end())
              out.get().vars.insert(v);
            else 
              out.get().moreVars = true;
          }
        };
        auto theoryVars = optional<ClauseRest>();
        auto uninterpretedVars = optional<ClauseRest>();
        for (int i = 0; i < lits.size(); i++) {
          if (i != cur) {
            auto l = lits[i];
            add_to_vars(l, l->isTheoryLiteral() 
                ? theoryVars 
                : uninterpretedVars);
          }
        }
        out.push_back(*new AbsClause(current, theoryVars, uninterpretedVars));
      }
    }
    return out; 
  }
  template <class A, class Config> friend struct gen_comparator;
  template <class D>
  friend void gen_dump(ostream &out, const AbsClause &cl, rect_map &map);
  friend ostream &operator<<(ostream &out, const AbsClause &cl);
};

// ostream &operator<<(ostream &out, AbsClause const &t) {
//
//   for (auto x : t.literals()) {
//     out << x << " ";
//   }
//   return out;
// }



CmpResult LitEquiv1::compare(const AbsClause &lhs, const AbsClause &rhs) {
  return CMP_EQUIV;
}

void LitEquiv1::dump(ostream &out, const AbsClause &lit) { out << "*"; }

struct cmp_eq {
  template <class A> CmpResult cmp(const A &l, const A &r) {
    if (l == r) {
      return CMP_NONE;
    } else {
      return CMP_EQUIV;
    }
  }
};

struct cmp_less {
  template <class A> CmpResult cmp(const A &l, const A &r) {
    if (l < r)
      return CMP_LESS;
    else if (r < l)
      return CMP_GREATER;
    else if (l == r)
      return CMP_EQUIV;
    else
      return CMP_NONE;
  }
};
bool operator<(const AbsTerm &lhs, const AbsTerm &rhs) {
  auto r =
      subclass_cmp<cmp_less, AbsTerm, AbsVarTerm, ACTerm>(cmp_less{}, lhs, rhs);
  return r == CMP_LESS;
}

bool operator==(const AbsTerm &lhs, const AbsTerm &rhs) {
  auto r =
      subclass_cmp<cmp_eq, AbsTerm, AbsVarTerm, ACTerm>(cmp_eq{}, lhs, rhs);
  return r == CMP_EQUIV;
}

ostream &operator<<(ostream &out, AbsTerm &t) {
  t.write(out);
  return out;
}

/* === comparisons based on equivalence classes  === */

template <class Config> struct gen_comparator<AbsLiteral, Config> {
  CmpResult operator()(const AbsLiteral &lhs, const AbsLiteral &rhs,
                       rect_maps &map) const {

#define CLOSURE(t) , [](const AbsLiteral &x) { return t; }

    return lex_cmp(state_wrapped_comparator_poly<Config>(map), lhs,
                   rhs MAP(CLOSURE, x.positive, x.predicate, x.terms));

#undef CLSR
  }
};

template <class Config> struct gen_comparator<AbsTerm, Config> {
  CmpResult operator()(const AbsTerm &lhs, const AbsTerm &rhs,
                       rect_maps &map) const {

    auto r = subclass_cmp<state_wrapped_comparator_poly<Config>, AbsTerm,
                          AbsVarTerm, ACTerm>(
        state_wrapped_comparator_poly<Config>(map), lhs, rhs);
    return r;
  }
};

#define APPLY_CMP_RECTIFIED_TY(l, r, ty) gen_comparator<ty, Config>{}(l, r, map)
#define APPLY_CMP_RECTIFIED(l, r) APPLY_CMP_RECTIFIED_TY(l, r, decltype(l))

#define IMPL_GEN_COMPARATOR_GROUND(CLASS)                                      \
  template <class Config> struct gen_comparator<CLASS, Config> {               \
    CmpResult operator()(const CLASS &lhs, const CLASS &rhs,                   \
                         rect_maps &map) const {                               \
      return compare_ground<CLASS>(lhs, rhs);                                  \
    }                                                                          \
  };

IMPL_GEN_COMPARATOR_GROUND(bool)
IMPL_GEN_COMPARATOR_GROUND(unsigned)
IMPL_GEN_COMPARATOR_GROUND(Predicate)
IMPL_GEN_COMPARATOR_GROUND(Function)

#define IMPL_GEN_COMPARATOR(CLASS, ...)                                        \
  template <class Config> struct gen_comparator<CLASS, Config> {               \
    CmpResult operator()(const CLASS &lhs, const CLASS &rhs,                   \
                         rect_maps &map) const __VA_ARGS__                     \
  };


template <class Config> struct gen_comparator<vset<AbsVarTerm>, Config> { 
  using container = vset<AbsVarTerm>;
  CmpResult operator()(const container &lhs_, const container &rhs_, 
                       rect_maps &map) const { 

    vset<unsigned> lhs;
    for (auto x : lhs_) {
      lhs.insert(map.l.get(x)._var);
    }
    vset<unsigned> rhs;
    for (auto x : rhs_) {
      rhs.insert(map.r.get(x)._var);
    }
    return gen_compare_container<vset<unsigned>, Config>(lhs, rhs, map); 
  } 
}; 



IMPL_GEN_COMPARATOR(ACTerm, {
  if (Config::CmpUninterpreted::special()) {
    auto l_unint = !lhs.isInterpreted();
    auto r_unint = !rhs.isInterpreted();

    /* number constants are all equiv */
    if (l_unint && r_unint)
      return Config::CmpUninterpreted::template cmp_uninterpreted<Config>(lhs, rhs, map);
    if (!l_unint && r_unint)
      return CMP_LESS;
    if (l_unint && !r_unint)
      return CMP_GREATER;
  }

  auto l_num = lhs.isNumberConstant();
  auto r_num = rhs.isNumberConstant();

  if (l_num && r_num) 
    return Config::CmpNumberConsts::compare_number_consts(lhs.toIntegerConstant(), rhs.toIntegerConstant());
  if (l_num && !r_num)
    return CMP_LESS;
  if (!l_num && r_num)
    return CMP_GREATER;

  auto c = APPLY_CMP_RECTIFIED(lhs._fun, rhs._fun);
  switch (c) {
  case CMP_LESS:
  case CMP_GREATER:
    return c;
  case CMP_NONE:
    ASSERTION_VIOLATION
  case CMP_EQUIV:;
  }

  /* both interpreted terms */
  return APPLY_CMP_RECTIFIED(lhs._args, rhs._args);
})

IMPL_GEN_COMPARATOR(ClauseRest, {
    return lex_cmp(state_wrapped_comparator_poly<Config>(map), 
        lhs, rhs,
        [](const ClauseRest& l) { return l.vars; },
        [](const ClauseRest& l) { return l.moreVars; });
    })



#define RETURN_ON_STRICT_INEQ(x)  \
  auto c = x; \
  switch (c) { \
  case CMP_LESS: \
  case CMP_GREATER: \
    return c; \
  case CMP_NONE: \
    ASSERTION_VIOLATION \
  case CMP_EQUIV:; \
  } \

IMPL_GEN_COMPARATOR(AbsClause, {
  return lex_cmp(state_wrapped_comparator_poly<Config>(map), 
      lhs, rhs,
      [](const AbsClause& l) { return l._lit; },
      [](const AbsClause& l) { return l._thryVars; },
      [](const AbsClause& l) { return l._unintVars; });
})

/* === dumping out equivalence class represnentativs  === */

template <class Sep, class Range, class Dump>
void dumpJoined(Sep separator, ostream &out, Range r, Dump d) {
  auto i = r.begin();
  auto end = r.end();
  if (i != end) {
    d(out, *i);
    i++;
    for (; i != end; i++) {
      out << separator;
      d(out, *i);
    }
  }
}


template <class Range, class Dump>
void dumpTuple(ostream &out, Range r, Dump d) {
  out << "(";
  dumpJoined(", ", out, r, d);
  // auto i = r.begin();
  // auto end = r.end();
  // if (i != end) {
  //   d(out, *i);
  //   i++;
  //   for (; i != end; i++) {
  //     out << ", ";
  //     d(out, *i);
  //   }
  // }
  out << ")";
}

// void dump_uninterpreted(ostream& out, vset<AbsVarTerm> vars, rect_map&) {
//
// }


void gen_dump(ostream &out, const ClauseRest &vars, rect_map &map);

template <class D>
void gen_dump(ostream &out, const AbsClause &cl, rect_map &map) {

#define DMP(name, x) \
  if (x.present()) {\
    out << " | ";\
    out << name;\
    gen_dump(out, x.get(), map);\
  }\

  gen_dump<D>(out, *cl._lit, map);
  DMP("T", cl._thryVars)
  DMP("C", cl._unintVars)
}
template <class D>
void gen_dump(ostream &out, const AbsLiteral &lit, rect_map &map) {
  out << (lit.positive ? " " : "!");
  out << lit.predicate;
  dumpTuple(out, lit.terms,
            [&](ostream &out, const AbsTerm &t) { gen_dump<D>(out, t, map); });
}

template <class D>
void gen_dump(ostream &out, const AbsTerm &trm, rect_map &map) {
  match(
      trm, [&](const ACTerm &t) { gen_dump<D>(out, t, map); },
      [&](const AbsVarTerm &t) { t.write(out, map); }); // TODO factor out
}

template <class D>
void gen_dump(ostream &out, const ACTerm &trm, rect_map &map) {

  if (D::CmpUninterpreted::special() && !trm.isInterpreted()) {
    return D::CmpUninterpreted::dumpUninterpreted(out, trm, map);

  } else if (trm.isNumberConstant()) {
    IntegerConstantType i = trm.toIntegerConstant();
    return D::CmpNumberConsts::dumpNumberConstant(out, i, map);

  } else {
    /* normal term */
    out << trm._fun;
    if (trm._args.size() > 0) {
      dumpTuple(out, trm._args, [&](ostream &out, const AbsTerm &t) {
        gen_dump<D>(out, t, map);
      });
    }
  }
}

struct CmpNumberConstsNop {
  static CmpResult compare_number_consts(IntegerConstantType lhs, IntegerConstantType rhs) {
    return CMP_EQUIV;
  }
  static void dumpNumberConstant(ostream &out, IntegerConstantType lit, rect_map &) {
    out << "c";
  }
};


struct CmpNumberConstsIsZero {
  static bool isZero(IntegerConstantType x) {
    static IntegerConstantType ZERO = IntegerConstantType(0); 
    return x == ZERO;
  }
  static CmpResult compare_number_consts(IntegerConstantType lhs, IntegerConstantType rhs) {
    // return CMP_EQUIV;
    return compare_ground(!isZero(lhs), !isZero(rhs));
  }
  static void dumpNumberConstant(ostream &out, IntegerConstantType lit, rect_map &) {
    if (isZero(lit)) {
      out << "0";
    } else {
      out << "c";
    }
  }
};

struct CmpVarsNop {
  static CmpResult cmp_vars(const AbsVarTerm &lhs, const AbsVarTerm &rhs,
                            rect_maps &map) {
    return CMP_EQUIV;
  }
};

struct CmpVarsEqual {
  static CmpResult cmp_vars(const AbsVarTerm &lhs, const AbsVarTerm &rhs,
                            rect_maps &map) {
    return compare_ground<unsigned>(lhs._var, rhs._var);
  }
};

struct CmpVarsMatch {
  static CmpResult cmp_vars(const AbsVarTerm &lhs, const AbsVarTerm &rhs,
                            rect_maps &map) {
    return compare_ground<unsigned>(map.l.get(lhs)._var, map.r.get(rhs)._var);
  }
};

struct CmpUninterpretedEquiv {
  static bool special() { return false; }
  template<class Config>
  static CmpResult cmp_uninterpreted(const ACTerm &lhs, const ACTerm &rhs,
                                     rect_maps &map) {
    ASSERTION_VIOLATION
  }
  static void dumpUninterpreted(ostream &out, const ACTerm &lit,
                                rect_map &map) {
    ASSERTION_VIOLATION
  }
};

struct CmpUninterpretedVarsMatch {
  static bool special() { return true; }
  template<class Config>
  static CmpResult cmp_uninterpreted(const ACTerm &lhs, const ACTerm &rhs,
                                     rect_maps &map) {
#define MAP_SET(lr) \
      vset<unsigned> lr;\
      for( auto v : static_cast<const AbsTerm &>(lr ## hs).var_set()) { \
        lr.insert(map.lr.get(v)._var); \
      } 

    MAP_SET(l)
    MAP_SET(r)
    return gen_compare_container<decltype(l), Config>(l,r,map);

    // auto l = static_cast<const AbsTerm &>(lhs).var_set();
    // auto r = static_cast<const AbsTerm &>(rhs).var_set();
    // if (l.size() < r.size())
    //   return CMP_LESS;
    // if (l.size() > r.size())
    //   return CMP_GREATER;
    // auto li = l.begin();
    // auto ri = r.begin();
    //
    // while (li != l.end()) {
    //   auto vl = map.l.get(*li);
    //   auto vr = map.r.get(*ri);
    //   if (vl < vr)
    //     return CMP_LESS;
    //   if (vl > vr)
    //     return CMP_GREATER;
    //   ri++;
    //   li++;
    // }
    //
    // return CMP_EQUIV;
  }
  static void dumpUninterpreted(ostream &out, const ACTerm &lit,
                                rect_map &map) {
    out << "?(";
    gen_dump(out, lit.var_set(), map);
    out << ")";
    // dumpTuple(out, lit.var_set(),
    //           [&](ostream &out, AbsVarTerm v) { v.write(out, map); });
  }
};

struct CmpUninterpretedNop {
  static bool special() { return true; }
  template<class Config>
  static CmpResult cmp_uninterpreted(const ACTerm &lhs, const ACTerm &rhs,
                                     rect_maps &map) {
    return CMP_EQUIV;
  }
  static void dumpUninterpreted(ostream &out, const ACTerm &lit,
                                rect_map &map) {
    out << "?(...)";
  }
};

IMPL_GEN_COMPARATOR(AbsVarTerm,
                    { return Config::CmpVars::cmp_vars(lhs, rhs, map); })

// struct LitEquiv2::Config {
//   using CmpUninterpreted = CmpUninterpretedNop;
//   using CmpVars = CmpVarsNop;
//   using CmpNumberConsts = CmpNumberConstsNop;
// };
// struct LitEquiv3::Config {
//   using CmpUninterpreted = CmpUninterpretedNop;
//   using CmpVars = CmpVarsMatch;
//   using CmpNumberConsts = CmpNumberConstsNop;
// };

struct LitEquiv4::Config {
  using CmpUninterpreted = CmpUninterpretedVarsMatch;
  using CmpVars = CmpVarsMatch;
  using CmpNumberConsts = CmpNumberConstsIsZero;
};

struct LitEquiv5::Config {
  using CmpUninterpreted = CmpUninterpretedEquiv;
  using CmpVars = CmpVarsMatch;
  using CmpNumberConsts = CmpNumberConstsIsZero;
};

//TODO here
#define __IMPL_LIT_EQUIV__COMPARE(i)                                           \
  CmpResult LitEquiv##i::compare(const AbsClause &lhs,                        \
                                 const AbsClause &rhs) {                      \
                                                                               \
    rect_maps map = rect_maps();                                               \
    using Config = LitEquiv##i::Config;                                        \
    return APPLY_CMP_RECTIFIED_TY(lhs, rhs, AbsClause);                       \
  }                                                                            \
  void LitEquiv##i::dump_raw(ostream &out, const AbsClause &cl) {                \
    out << cl;                              \
  } \
  void LitEquiv##i::dump(ostream &out, const AbsClause &cl) {                \
    auto map = rect_map();                                                     \
    gen_dump<LitEquiv##i::Config>(out, cl, map);                              \
  }

MAP(__IMPL_LIT_EQUIV__COMPARE, EQ_CLASSES)

ostream &operator<<(ostream &out, const AbsLiteral &lit) {
  out << (lit.positive ? " " : "!");
  out << lit.predicate;
  dumpTuple(out, lit.terms, [](ostream &out, const AbsTerm &t) { out << t; });
  return out;
}

/**
 * returns whether @b t points to a theory term. A theory term is a term where
 * the outer most function symbol is an interpreted one.
 *
 * Note that the typename TermList is deceptive here. t is actually a pointer
 * (~= iterator pointing to) to an element in a TermList.
 */
bool isTheoryTerm_L(const TermList &t) {
  if (t.isTerm()) {
    return interpretedFun(*t.term());
  } else {
    ASS_(t.isVar());
    return false;
  }
}



/**
 * returns whether @b lit is a theory literal. A literal @b lit is a theory
 * literal iff (any of)
 * - the predicate symbol is interpreted
 * - it is an equality literal with at least on theory term
 */
bool isTheoryLiteral(Literal &lit) {
  Signature::Symbol &sym = *env.signature->getPredicate(lit.functor());
  const TermList *args = lit.args();
  return sym.interpreted() && (!lit.isEquality() || isTheoryTerm_L(*args) ||
                               isTheoryTerm_L(*args->next()));
}

// vvec<refw<AbsClause>> absTheorySubclauses(Clause const &c) {
//   vvec<Literal *> lits;
//   for (int i = 0; i < c.length(); i++) {
//     if (isTheoryLiteral(*c[i]))
//       lits.push_back(c[i]);
//   }
//   return *new AbsClause(lits);
// }


// /**
//  * Returns the maximum theory subclause. The maximum theory subclause consists
//  * of all theory literals (see @b isTheoryLiteral) that are contained in @b c.
//  */
// AbsClause &maxTheorySubclause(Clause const &c) {
//   vvec<Literal *> lits;
//   for (int i = 0; i < c.length(); i++) {
//     if (isTheoryLiteral(*c[i]))
//       lits.push_back(c[i]);
//   }
//   return *new AbsClause(lits);
// }

#define INIT_EQ_CLASS_MEMBERS(i) , _eq##i(equiv_t_##i{})

TheorySubclauseAnalyser::TheorySubclauseAnalyser()
    : _total(0) MAP(INIT_EQ_CLASS_MEMBERS, EQ_CLASSES_) {}

#undef INIT_EQ_CLASS_MEMBERS

TheorySubclauseAnalyser::~TheorySubclauseAnalyser() {}

void TheorySubclauseAnalyser::addClause(Clause &c) {
  CALL("TheorySubclauseAnalyser::addClause")
  if (!c.isTheoryAxiom() && !c.isTheoryDescendant()) {
    // auto &scl = maxTheorySubclause(c);
    auto scl = AbsClause::abstractions(c);
    for (AbsClause& l_ : scl) {
      auto l = rc<AbsClause>(&l_);
      auto map = rect_map();
      _total++;
#define INSERT(i) _eq##i.insert(l);
      MAP(INSERT, EQ_CLASSES_)
#undef INSERT
    }
  }
}

#define EQ_CLASS_NAME_1 "AllEqual"
#define EQ_CLASS_NAME_2 "IgnoreVars_IgnoreUninterpreted"
#define EQ_CLASS_NAME_3 "MatchVars_IgnoreUninterpreted"
#define EQ_CLASS_NAME_4 "VarsMatch_UnintVarsMatch"
#define EQ_CLASS_NAME_5 "VarsMatch_UnintMatch"

void TheorySubclauseAnalyser::dumpStats(ostream &out) const {

#define DUMP(i) _eq##i.serialize(EQ_CLASS_NAME_##i, _total, out);

  out << endl;
  out << endl;

  MAP(DUMP, EQ_CLASSES)
#undef DUMP
}

TheorySubclauseAnalyser *TheorySubclauseAnalyser::instance =
    new TheorySubclauseAnalyser();

AbsTerm &AbsTerm::var(int i) { return *new AbsVarTerm(i); }
AbsTerm &AbsTerm::fun(unsigned functor, vvec<refw<AbsTerm>> args) {
  return *new ACTerm(Function(functor), args);
}
AbsLiteral &create_abs_lit(bool positive, unsigned functor,
                           vvec<refw<AbsTerm>> args) {
  return *new AbsLiteral(positive, Predicate(functor), args);
}

void AbsLiteral::var_set(vset<AbsVarTerm>& out) const {
  for (const AbsTerm& t : this->terms) {
    t.var_set(out);
  }
}

void AbsLiteral::normalize() {
  CALL("AbsLiteral::normalize()");
  for (AbsTerm &t : terms) {
    t.normalize();
  }
  if (predicate.isEquality()) {
    ASS_(terms.size() == 2);
    auto rect = rect_maps();
    struct Config {
      using CmpUninterpreted = CmpUninterpretedVarsMatch;
      using CmpVars = CmpVarsMatch;
      using CmpNumberConsts = CmpNumberConstsNop;
    };
    if (gen_comparator<AbsTerm, Config>{}(terms[0], terms[1], rect) ==
        CMP_GREATER) {
      std::swap(terms[0], terms[1]);
    }
  }
}

// void AbsTerm::rectify() {
//   auto r = rect_map();
//   this->rectify(r);
// }
//
// void AbsLiteral::rectify(rect_map& map) {
//   for (auto &t : terms) {
//     t.get().rectify(map);
//   }
// }

template <> struct Debug::print_debug<CmpResult> {
  void operator()(ostream &out, const CmpResult &a) const {
    switch (a) {
    case CMP_EQUIV:
      out << "EQUIV";
      break;
    case CMP_LESS:
      out << "LESS";
      break;
    case CMP_GREATER:
      out << "GREATER";
      break;
    case CMP_NONE:
      out << "NONE";
      break;
    }
  }
};

#define IMPL_PRINT_DEBUG_DEFAULT(CLASS)                                        \
  template <> struct Debug::print_debug<CLASS> {                               \
    void operator()(ostream &out, const CLASS &a) const { out << a; }          \
  };

IMPL_PRINT_DEBUG_DEFAULT(AbsTerm)
IMPL_PRINT_DEBUG_DEFAULT(Function)
IMPL_PRINT_DEBUG_DEFAULT(Predicate)

void ACTerm::sortCommut() {
  CALL("ACTerm::sortCommut")
  for (auto a : _args) {
    a.get().sortCommut();
  }
  if (_fun.isCommut()) {
    rect_maps map = rect_maps();
    // sort(_args.begin(), _args.end());
    struct Config {
      using CmpUninterpreted = CmpUninterpretedVarsMatch;
      using CmpVars = CmpVarsMatch;
      using CmpNumberConsts = CmpNumberConstsNop;
    };
    sort(_args.begin(), _args.end(),
         state_wrapped_comparator_std<AbsTerm, Config>(map));
  }
}
void ACTerm::write(ostream &out) const {
  out << _fun;
  if (_args.size() > 0) {
    dumpTuple(out, _args, [](ostream &out, AbsTerm &t) { out << t; });
  }
}
void normalize_absliteral(AbsLiteral &lit) { lit.normalize(); }
bool equal_absliteral(const AbsLiteral &l, const AbsLiteral &r) {
  return l == r;
}

AbsVarTerm rect_map::get(const AbsVarTerm& v){
  auto it = map.find(v._var);
  unsigned out;
  if (it == map.end()) {
    out = n_vars++;
    map.insert(decltype(map)::value_type(v._var, out));
  } else {
    ASS_(it->first == v._var);
    out = it->second;
  }
  return AbsVarTerm(out);
}

vset<AbsVarTerm> AbsTerm::var_set() const {
  vset<AbsVarTerm> out;
  var_set(out);
  return out;
}

void gen_dump(ostream &out, const vset<AbsVarTerm> &vars, rect_map &map) {
  vset<AbsVarTerm> s;
  for (auto v : vars) {
    s.insert(map.get(v));
  }
  dumpJoined(", ", out, s,
            [&](ostream &out, AbsVarTerm v) { out << "X" << v._var; });
}


void gen_dump(ostream &out, const ClauseRest &rest, rect_map &map) {
  out << "[";
  gen_dump(out, rest.vars, map);
  if (rest.moreVars) {

    if (rest.vars.size() != 0)
      out << ", ";

    out << "...";
  }
  out << "]";
}

ostream &operator<<(ostream &out, const ClauseRest &rest) {
  out << "[";
  dumpJoined(", ", out, rest.vars,
            [&](ostream &out, AbsVarTerm v) { out << v; });
  if (rest.moreVars) {

    if (rest.vars.size() != 0)
      out << ", ";

    out << "...";
  }
  out << "]";
  return out;
}

ostream &operator<<(ostream &out, const AbsClause &cl) {
  out << *cl._lit;
  if (cl._thryVars.present()) {
    out  << " | T" << cl._thryVars.get();
  } 
  if (cl._unintVars.present()) {
    out  << " | C" << cl._unintVars.get();
  } 
  return out;
}

#endif

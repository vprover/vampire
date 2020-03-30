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

// #define PRINT_TOP_N 20

using namespace Shell::Analysis;
using namespace std;
using namespace Kernel;

using Interpretation = Theory::Interpretation;

/* ================================================= */
/* =================== utilities =================== */
/* ================================================= */

// #define IMPL_DEFAULT_COMPARISONS(i)                                            \
//   template <class A> struct cmp##i<vvec<A>> {                                  \
//     CmpResult operator()(const vvec<A> &lhs, const vvec<A> &rhs) const {       \
//       auto li = lhs.begin();                                                   \
//       auto ri = rhs.begin();                                                   \
//       while (li != lhs.end() && ri != rhs.end()) {                             \
//         auto l = *li;                                                          \
//         auto r = *ri;                                                          \
//         auto c = cmp##i<A>{}(l, r);                                            \
//         switch (c) {                                                           \
//         case CMP_NONE:                                                         \
//         case CMP_LESS:                                                         \
//         case CMP_GREATER:                                                      \
//           return c;                                                            \
//         case CMP_EQUIV:;                                                       \
//         }                                                                      \
//         li++;                                                                  \
//         ri++;                                                                  \
//       }                                                                        \
//       auto lend = li == lhs.end();                                             \
//       auto rend = ri == rhs.end();                                             \
//       if (!lend && rend)                                                       \
//         return CMP_LESS;                                                       \
//       if (lend && !rend)                                                       \
//         return CMP_GREATER;                                                    \
//                                                                                \
//       return CMP_EQUIV;                                                        \
//     }                                                                          \
//   };                                                                           \
//                                                                                \
//   template <class A> struct cmp##i<refw<A>> {                                  \
//     CmpResult operator()(const refw<A> &lhs, const refw<A> &rhs) const {       \
//       const A &l = lhs.get();                                                  \
//       const A &r = rhs.get();                                                  \
//       return cmp##i<A>{}(l, r);                                                \
//     }                                                                          \
//   };                                                                           \
//                                                                                \
//   template <class A> struct cmp##i<rc<A>> {                                    \
//     CmpResult operator()(const rc<A> &lhs, const rc<A> &rhs) const {           \
//       const A &l = *lhs.get();                                                 \
//       const A &r = *rhs.get();                                                 \
//       return cmp##i<A>{}(l, r);                                                \
//     }                                                                          \
//   };
// MAP(IMPL_DEFAULT_COMPARISONS, EQ_CLASSES)

struct rect_maps;

struct rect_map {
private:
  unsigned n_vars;
  vumap<unsigned, unsigned> map;

public:
  rect_map() : n_vars(0), map(vumap<unsigned, unsigned>()) {}
  unsigned get(unsigned v) {
    auto it = map.find(v);
    unsigned out;
    if (it == map.end()) {
      out = n_vars++;
      map.insert(decltype(map)::value_type(v, out));
    } else {
      ASS(it->first == v);
      out = it->second;
    }
    return out;
  }
};

template <class A, class... Cmps> struct gen_comparator {
  CmpResult operator()(const A &l, const A &r, rect_maps &map) const;

  template <class B>
  CmpResult cmp(const B &lhs, const B &rhs, rect_maps &map) const {
    return gen_comparator<B, Cmps...>{}(lhs, rhs, map);
  }
};

template <class A, class... Cs> struct state_wrapped_comparator_std {
  rect_maps &map;
  state_wrapped_comparator_std(rect_maps& map) : map(map) {}
  bool operator()(A const& l, A const& r) {
    return gen_comparator<A, Cs...>{}(l, r, map) == CMP_LESS;
  }
};

template <class... Cs> struct state_wrapped_comparator_poly {
  rect_maps &map;
  state_wrapped_comparator_poly(rect_maps &map) : map(map) {}
  template <class B> CmpResult cmp(const B &l, const B &r) {
    return gen_comparator<B, Cs...>{}(l, r, map);
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

template <class A, class... Cs> struct gen_comparator<vvec<A>, Cs...> {
  CmpResult operator()(const vvec<A> &lhs, const vvec<A> &rhs,
                       rect_maps &map) const {
    auto li = lhs.begin();
    auto ri = rhs.begin();
    while (li != lhs.end() && ri != rhs.end()) {
      auto l = *li;
      auto r = *ri;
      auto c = gen_comparator<A, Cs...>{}(l, r, map);
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
};

template <class A, class... Cs> struct gen_comparator<refw<A>, Cs...> {
  CmpResult operator()(const refw<A> &lhs, const refw<A> &rhs,
                       rect_maps &map) const {
    const A &l = lhs.get();
    const A &r = rhs.get();
    return gen_comparator<A, Cs...>{}(l, r, map);
  }
};

template <class A, class... Cs> struct gen_comparator<rc<A>, Cs...> {
  CmpResult operator()(const rc<A> &lhs, const rc<A> &rhs,
                       rect_maps &map) const {
    const A &l = *lhs.get();
    const A &r = *rhs.get();
    return gen_comparator<A, Cs...>{}(l, r, map);
  }
};

#undef CMP_FUN

#define CMP_FRIEND(i) template <class A> friend struct cmp##i;

#define CMP_FRIENDS                                                            \
  MAP(CMP_FRIEND, EQ_CLASSES)                                                  \
  template <class A, class... Cmps> friend struct gen_comparator;

/** ============= lexicographical comparison ================== **/

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

template <class Fn, class A, class... Fs>
CmpResult lex_cmp(Fn f, A l, A r, Fs... fs) {
  return lex_<Fn, A, Fs...>::cmp(f, l, r, fs...);
}

/** ============= subclass comparison ================== **/

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

template <class Fn, class A, class... As>
CmpResult subclass_cmp(Fn f, const A &lhs, const A &rhs) {
  return _subclass_cmp<Fn, A, As...>::cmp(f, lhs, rhs);
}

#define HASH_CODE(item) code ^= std::hash<decltype(item)>{}(item);

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
  TIE_OP(==, CLASS, __VA_ARGS__)                                               \
  _IMPL_HASH(CLASS, __VA_ARGS__)

#define HASH_BODY(CLASS, ...)                                                  \
  auto code = 786532;                                                          \
  MAP(HASH_CODE, __VA_ARGS__)                                                  \
  return code;

#define _IMPL_HASH(CLASS, ...)                                                 \
  size_t hash_code() const {                                                   \
    const CLASS &x = *this;                                                    \
    HASH_BODY(CLASS, __VA_ARGS__)                                              \
  }                                                                            \
                                                                               \
  friend struct std::hash<CLASS>;

#define IMPL_HASH(CLASS, ...)                                                  \
  namespace std {                                                              \
  template <> struct hash<CLASS> {                                             \
    std::size_t operator()(CLASS const &x) const noexcept {                    \
      HASH_BODY(CLASS, __VA_ARGS__)                                            \
    }                                                                          \
  };                                                                           \
  }

template <class A> struct std::hash<vvec<refw<A>>> {
  size_t operator()(const vvec<refw<A>> &xs) const noexcept {
    size_t code = 827471209;
    for (auto x : xs) {
      code ^= std::hash<A>{}(x.get());
    }
    return code;
  }
};

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

  CMP_FRIENDS
  OPERATORS(AbsSymbol, x.functor)
};

IMPL_HASH(AbsSymbol, x.functor)

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

  CMP_FRIENDS
  OPERATORS(Predicate, x.functor)
};
IMPL_HASH(Predicate, x.functor)

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
    // Debug::dbg(*this, " is plus:", Theory::isPlus(i), " is times: ", Theory::isTimes(i));
    return Theory::isPlus(i) || Theory::isTimes(i);
  }

  bool leftDistributiveOver(const Function &other) const {
    return Theory::isTimes(this->interpret()) &&
           Theory::isPlus(other.interpret());
  }

  bool isInterpretedConstant() const {
    return Theory::instance()->isInterpretedConstant(functor);
  }

  bool isUnaryMinus() const { return Theory::isUnaryMinus(this->interpret()); }
  CMP_FRIENDS
  OPERATORS(Function, x.functor)
};
IMPL_HASH(Function, x.functor)
class AbsVarTerm : public AbsTerm {
public:
  CLASS_NAME(AbsVarTerm);

  USE_ALLOCATOR(AbsVarTerm);

private:
  unsigned _var;

public:
  AbsVarTerm(unsigned var) : _var(var) {}

  void write(ostream &out) const override { out << "X" << _var; }

  void normalize() override {}
  void rectify(rect_map &r) override { _var = r.get(_var); }
  void mergeAssoc() override {}
  void sortCommut() override {}
  void distributeLeft() override {}
  void distributeRight() override {}
  void pushMinus() override {}
  void var_set(vset<unsigned> &v) const override { v.insert(_var); }

  void vars(vvec<unsigned> &v, on_unsigned_t onUninterpreted) const override {
    v.push_back(_var);
  }
  CMP_FRIENDS
  OPERATORS(AbsVarTerm, x._var)
  friend class CmpVarsMatch;
  friend class CmpVarsEqual;
};
IMPL_HASH(AbsVarTerm, x._var)

/** Term of associative commutative function */
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

  ACTerm(Term &term) : _fun(term.functor()), _args(args_t()) {
    for (auto i = 0; i < term.arity(); i++) {
      auto &t = AbsTerm::from(*term.nthArgument(i));
      _args.push_back(t);
    }
    ASS(!term.isSpecial())
    ASS(!term.isLiteral())
    ASS_REP(!_fun.isUnaryMinus() || _args.size() == 1, term.functionName())
  }

  void integrityCheck() {
    for (auto a : _args) {
      if (auto x = dynamic_cast<ACTerm *>(&a.get())) {
        x->integrityCheck();
      }
    }
    ASS(!_fun.isPlus() || _args.size() > 0)
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
  void rectify(rect_map &r) override {
    for (auto &t : _args) {
      t.get().rectify(r);
    }
  }

  void pushMinus() override {
    CALL("ACTerm::pushMinus")
    if (_fun.isUnaryMinus()) {
      ASS(_args.size() == 1);
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
  vset<unsigned> var_set() const { 
    vset<unsigned> v;
    var_set(v);
    return v;
  }
  void var_set(vset<unsigned> &vs) const override {
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
        ASS(r->_args.size() == 2);
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
  CMP_FRIENDS
  OPERATORS(ACTerm, !x.isInterpreted(), !x.isNumberConstant(),  x._fun, x._args)
  template<class D>
  friend void gen_dump(ostream& out, const ACTerm& trm);
};
IMPL_HASH(ACTerm, x._fun, x._args)

template<class F1, class F2>
void match(const AbsTerm& term, F1 f1, F2 f2) {
  if (auto t = dynamic_cast<const ACTerm*>(&term)) {
    return f1(*t);
  } else {
    ASS(dynamic_cast<const AbsVarTerm*>(&term));
    return f2(*static_cast<const AbsVarTerm*>( &term ));
  }
}
IMPL_HASH(AbsTerm,
          size_t(dynamic_cast<const AbsVarTerm *>(&x)
                     ? (static_cast<const AbsVarTerm &>(x).hash_code())
                     : dynamic_cast<const ACTerm *>(&x)
                           ? (static_cast<const ACTerm &>(x).hash_code())
                           : 0))

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
struct AbsLiteral {
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

  void normalize();
  void rectify();

  AbsLiteral(bool positive, Predicate pred, vvec<refw<AbsTerm>> terms)
      : positive(positive), predicate(pred), terms(terms) {}

  CMP_FRIENDS

  CMP_FRIENDS
  OPERATORS(AbsLiteral, x.predicate, x.positive, x.terms);
};
IMPL_HASH(AbsLiteral, x.predicate, x.positive, x.terms);

ostream &operator<<(ostream &out, const AbsLiteral &lit);

template <>
CmpResult cmp1<AbsLiteral>::operator()(const AbsLiteral &lhs,
                                       const AbsLiteral &rhs) const {
  return CMP_EQUIV;
}

void LitEquiv1::dump(ostream& out, const AbsLiteral& lit) {
  out << "*";
}



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

#define PAIRS(x) , lhs.x, rhs.x

#define IMPL_CMP(i, CLASS, BODY)                                               \
  template <>                                                                  \
  CmpResult cmp##i<CLASS>::operator()(const CLASS &lhs, const CLASS &rhs)      \
      const BODY

#define IMPL_CMP_VALS__TO_CLSR(t) , [](ty x) { return t; }
#define IMPL_CMP_VALS(i, CLASS, ...)                                           \
  IMPL_CMP(i, CLASS, {                                                         \
    using ty = const CLASS &;                                                  \
    return lex_cmp(cmp##i{}, lhs,                                              \
                   rhs MAP(IMPL_CMP_VALS__TO_CLSR, __VA_ARGS__));              \
  })

#define IMPL_CMP_DEFAULT(i, CLASS)                                             \
  IMPL_CMP(i, CLASS, {                                                         \
    if (lhs < rhs)                                                             \
      return CMP_LESS;                                                         \
    else if (rhs < lhs)                                                        \
      return CMP_GREATER;                                                      \
    else if (lhs == rhs)                                                       \
      return CMP_EQUIV;                                                        \
    else                                                                       \
      return CMP_NONE;                                                         \
  })

#define IMPL_CMP_GROUND(i)                                                     \
  IMPL_CMP_DEFAULT(i, Predicate)                                               \
  IMPL_CMP_DEFAULT(i, Function)                                                \
  IMPL_CMP_DEFAULT(i, int)                                                     \
  IMPL_CMP_DEFAULT(i, bool)                                                    \
  IMPL_CMP_DEFAULT(i, unsigned)

MAP(IMPL_CMP_GROUND, EQ_CLASSES)

template <class... Cs> struct gen_comparator<AbsLiteral, Cs...> {
  CmpResult operator()(const AbsLiteral &lhs, const AbsLiteral &rhs,
                       rect_maps &map) const {

#define CLOSURE(t) , [](const AbsLiteral &x) { return t; }

    return lex_cmp(state_wrapped_comparator_poly<Cs...>(map), lhs,
                   rhs MAP(CLOSURE, x.positive, x.predicate, x.terms));

#undef CLSR
  }
};

template <class... Cs> struct gen_comparator<AbsTerm, Cs...> {
  CmpResult operator()(const AbsTerm &lhs, const AbsTerm &rhs,
                       rect_maps &map) const {

    auto r =
        subclass_cmp<state_wrapped_comparator_poly<Cs...>, AbsTerm, AbsVarTerm,
                     ACTerm>(state_wrapped_comparator_poly<Cs...>(map), lhs, rhs);
    return r;
  }
};

struct CmpNumberConstsNop {
  static CmpResult compare_number_consts(const ACTerm &lhs, const ACTerm &rhs) {
    return CMP_EQUIV;
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
    return compare_ground<unsigned>(map.l.get(lhs._var), map.r.get(rhs._var));
  }
};

struct CmpUninterpretedNop {
  static CmpResult cmp_uninterpreted(const ACTerm &lhs, const ACTerm &rhs,
                                     rect_maps &map) {
    return CMP_EQUIV;
  }
};

struct CmpUninterpretedVarsMatch {
  static CmpResult cmp_uninterpreted(const ACTerm &lhs, const ACTerm &rhs,
                                     rect_maps &map) {
    auto l = static_cast<const AbsTerm &>(lhs).var_set();
    auto r = static_cast<const AbsTerm &>(rhs).var_set();
    if (l.size() < r.size())
      return CMP_LESS;
    if (l.size() > r.size())
      return CMP_GREATER;
    auto li = l.begin();
    auto ri = r.begin();

    while (li != l.end()) {
      auto vl = map.l.get(*li);
      auto vr = map.r.get(*ri);
      if (vl < vr)
        return CMP_LESS;
      if (vl > vr)
        return CMP_GREATER;
      ri++;
      li++;
    }

    return CMP_EQUIV;
  }
};

#define SUB_COMPARATORS CmpUninterpreted, CmpVars, CmpNumberConsts
#define FINEST_COMPARATOR                                                      \
  gen_comparator<AbsTerm, CmpUninterpretedVarsMatch, CmpVarsMatch,             \
                 CmpNumberConstsNop> {}

#define APPLY_CMP_RECTIFIED_TY(l, r, ty)                                       \
  gen_comparator<ty, SUB_COMPARATORS>{}(l, r, map)
#define APPLY_CMP_RECTIFIED(l, r) APPLY_CMP_RECTIFIED_TY(l, r, decltype(l))

#define IMPL_GEN_COMPARATOR_GROUND(CLASS)                                      \
  template <class... Cs> struct gen_comparator<CLASS, Cs...> {                 \
    CmpResult operator()(const CLASS &lhs, const CLASS &rhs,                   \
                         rect_maps &map) const {                               \
      return compare_ground<CLASS>(lhs, rhs);                                  \
    }                                                                          \
  };

IMPL_GEN_COMPARATOR_GROUND(bool)
IMPL_GEN_COMPARATOR_GROUND(Predicate)
IMPL_GEN_COMPARATOR_GROUND(Function)

#define IMPL_GEN_COMPARATOR(CLASS, ...)                                        \
  template <class CmpUninterpreted, class CmpVars, class CmpNumberConsts>      \
  struct gen_comparator<CLASS, SUB_COMPARATORS> {                              \
    CmpResult operator()(const CLASS &lhs, const CLASS &rhs,                   \
                         rect_maps &map) const __VA_ARGS__                     \
  };

IMPL_GEN_COMPARATOR(ACTerm, {

  auto l_unint = !lhs.isInterpreted();
  auto r_unint = !rhs.isInterpreted();

  /* number constants are all equiv */
  if (l_unint && r_unint)
    return CmpUninterpreted::cmp_uninterpreted(lhs, rhs, map);
  if (!l_unint && r_unint)
    return CMP_LESS;
  if (l_unint && !r_unint)
    return CMP_GREATER;

  auto l_num = lhs.isNumberConstant();
  auto r_num = rhs.isNumberConstant();

  /* number constants are all equiv */
  if (l_num && r_num)
    return CmpNumberConsts::compare_number_consts(lhs, rhs);
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

IMPL_GEN_COMPARATOR(AbsVarTerm, { return CmpVars::cmp_vars(lhs, rhs, map); })

template <>
CmpResult cmp2<AbsLiteral>::operator()(const AbsLiteral &lhs,
                                       const AbsLiteral &rhs) const {

  rect_maps map = rect_maps();

  using CmpUninterpreted = CmpUninterpretedNop;
  using CmpVars = CmpVarsNop;
  using CmpNumberConsts = CmpNumberConstsNop;
  return APPLY_CMP_RECTIFIED_TY(lhs, rhs, AbsLiteral);
}

template <>
CmpResult cmp3<AbsLiteral>::operator()(const AbsLiteral &lhs,
                                       const AbsLiteral &rhs) const {

  rect_maps map = rect_maps();

  using CmpUninterpreted = CmpUninterpretedNop;
  using CmpVars = CmpVarsMatch;
  using CmpNumberConsts = CmpNumberConstsNop;
  return APPLY_CMP_RECTIFIED_TY(lhs, rhs, AbsLiteral);
}

template <>
CmpResult cmp4<AbsLiteral>::operator()(const AbsLiteral &lhs,
                                       const AbsLiteral &rhs) const {
  rect_maps map = rect_maps();

  using CmpUninterpreted = CmpUninterpretedVarsMatch;
  using CmpVars = CmpVarsMatch;
  using CmpNumberConsts = CmpNumberConstsNop;
  return APPLY_CMP_RECTIFIED_TY(lhs, rhs, AbsLiteral);
}

template<class D>
void gen_dump(ostream& out, const AbsLiteral& lit){
  out << (lit.positive ? " " : "!");
  out << lit.predicate;
  dumpTuple(out, lit.terms, [](ostream& out, const AbsTerm& t) {gen_dump<D>(out, t);});
}

template<class D>
void gen_dump(ostream& out, const AbsTerm& trm){
      match(trm, 
          [&](const ACTerm& t) { gen_dump<D>(out, t); },
          [&](const AbsVarTerm& t) { t.write(out); } );
}

template<class D>
void gen_dump(ostream& out, const ACTerm& trm) {

  if (!trm.isInterpreted())
    return D::dumpUninterpreted(out, trm);

  if (trm.isNumberConstant())
    return D::dumpNumberConstant(out, trm);

  out << trm._fun;
  if (trm._args.size() > 0) {
    dumpTuple(out, trm._args, [](ostream& out, const AbsTerm& t) {gen_dump<D>(out, t);});
  }

}

void LitEquiv4::dump(ostream& out, const AbsLiteral& lit) {
  gen_dump<LitEquiv4>(out, lit);
}

void LitEquiv4::dumpNumberConstant(ostream& out, const ACTerm& lit) {
  out << "c";
}

template<class Range, class Dump>
void dumpTuple(ostream& out, Range r, Dump d) {
  out << "(";
  auto i = r.begin();
  auto end = r.end();
  if (i != end) {
    d(out, *i);
    i++;
    for (; i != end; i++) {
      out << ", ";
      d(out, *i);
    }
  }
  out << ")";
}

void LitEquiv4::dumpUninterpreted(ostream& out, const ACTerm& lit) {
  out << "?";
  dumpTuple(out, lit.var_set(), [](ostream& out, unsigned v) { out << "X" << v; } );
}

ostream &operator<<(ostream &out, const AbsLiteral &lit) {
  out << (lit.positive ? " " : "!");
  out << lit.predicate;
  dumpTuple(out, lit.terms, [](ostream& out, const AbsTerm& t) { out << t; });
  return out;
}

class AbsTheoryClause {
  vvec<rc<AbsLiteral>> _lits;

public:
  CLASS_NAME(AbsTheoryClause)
  USE_ALLOCATOR(AbsTheoryClause)

  AbsTheoryClause(vvec<Literal *> &ls) : _lits(vvec<rc<AbsLiteral>>()) {
    CALL("AbsTheoryClause::AbsTheoryClause()")
    _lits.reserve(ls.size());
    for (auto l : ls) {
      _lits.push_back(rc<AbsLiteral>(new AbsLiteral(l)));
    }
  }

  AbsTheoryClause(AbsTheoryClause &&c) : _lits(std::move(c._lits)) {}

  AbsTheoryClause &operator=(AbsTheoryClause &&other) {
    _lits = std::move(other._lits);
    return *this;
  }

  const vvec<rc<AbsLiteral>> &literals() const { return _lits; }
};

ostream &operator<<(ostream &out, AbsTheoryClause const &t) {
  for (auto x : t.literals()) {
    out << x << " ";
  }
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
    // Signature::Symbol& sym =
    // *env.signature->getFunction(t.term()->functor()); return
    // sym.interpreted();
  } else {
    ASS(t.isVar());
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

/**
 * Returns the maximum theory subclause. The maximum theory subclause consists
 * of all theory literals (see @b isTheoryLiteral) that are contained in @b c.
 */
AbsTheoryClause &maxTheorySubclause(Clause const &c) {
  vvec<Literal *> lits;
  for (int i = 0; i < c.length(); i++) {
    if (isTheoryLiteral(*c[i]))
      lits.push_back(c[i]);
  }
  return *new AbsTheoryClause(lits);
}

/* TheorySubclauseAnalyser implementation */

#define INIT_EQ_CLASS_MEMBERS(i) , _eq##i(equiv_t_##i{})

TheorySubclauseAnalyser::TheorySubclauseAnalyser()
    : _literals(literals_type()) MAP(INIT_EQ_CLASS_MEMBERS, EQ_CLASSES) {}

#undef INIT_EQ_CLASS_MEMBERS

TheorySubclauseAnalyser::~TheorySubclauseAnalyser() {}

void TheorySubclauseAnalyser::addClause(Clause &c) {
  CALL("TheorySubclauseAnalyser::addClause")
  if (!c.isTheoryAxiom() && !c.isTheoryDescendant()) {

    auto &scl = maxTheorySubclause(c);
    for (auto l : scl.literals()) {
      l->normalize();
      l->rectify();
      _literals.insert(l);
#define INSERT(i) _eq##i.insert(l);
      MAP(INSERT, EQ_CLASSES)
#undef INSERT
    }
  }
}

// template <class C>
// void serializeContainer(ostream &out, const char *name, const C &cont) {
//   using entry = typename decltype(cont._content)::value_type;
//   using elem_t = typename decltype(cont._content)::value_type::first_type;
//   auto c = vvec<const entry *>();
//   for (auto &e : cont._content) {
//     c.push_back(&e);
//   }
//
//   struct {
//     bool operator()(const entry *l, const entry *r) {
//       return l->second.size() > r->second.size();
//     }
//   } comp;
//   sort(c.begin(), c.end(), comp);
//
// #ifdef PRINT_TOP_N
//   c.resize(min<size_t>(PRINT_TOP_N, c.size()));
// #endif
//
//   for (auto &pair : cont) {
//     auto size = pair->second.size();
//     auto &&elems = pair->second;
//     ASS_REP(size > 0, size);
//
//     out << i << "."
//         << "\t" << size << "\t" << **min_element(begin(elems), end(elems));
//     out << endl;
//     i++;
//   }
// }


// template <class C>
// void dumpContainer_(ostream &out, const char *name, const C &cont) {
//   using entry = typename decltype(cont._content)::value_type;
//   using elem_t = typename decltype(cont._content)::value_type::first_type;
//   auto c = vvec<const entry *>();
//   for (auto &e : cont._content) {
//     c.push_back(&e);
//   }
//
//   struct {
//     bool operator()(const entry *l, const entry *r) {
//       return l->second.size() > r->second.size();
//     }
//   } comp;
//   sort(c.begin(), c.end(), comp);
//
// #ifdef PRINT_TOP_N
//   c.resize(min<size_t>(PRINT_TOP_N, c.size()));
// #endif
//
//   int i = 1;
//   for (auto &pair : c) {
//     auto size = pair->second.size();
//     auto &&elems = pair->second;
//     ASS_REP(size > 0, size);
//
//     out << i << "."
//         << "\t" << size << "\t" << **min_element(begin(elems), end(elems));
//     out << endl;
//     i++;
//   }
// }

#define EQ_CLASS_NAME_1 "AllEqual"
#define EQ_CLASS_NAME_2 "IgnoreVars_IgnoreUninterpreted"
#define EQ_CLASS_NAME_3 "MatchVars_IgnoreUninterpreted"
#define EQ_CLASS_NAME_4 "VarsMatch_UnintVarsMatch"

void TheorySubclauseAnalyser::dumpStats(ostream &out) const {
  // dumpContainer(out, "Equality", _literals);

// #define DUMP(i)                                                                \
//   out << "================= "                                                  \
//       << "Equivalence class: " << EQ_CLASS_NAME_##i                            \
//       << " =================" << endl;                                         \
//   _eq##i.dump(out);

#define DUMP(i)                                                                \
  _eq##i.serialize(EQ_CLASS_NAME_##i, out);

  out << endl;
  out << endl;

  // MAP(DUMP, EQ_CLASSES)
  MAP(DUMP, 1, 4)
#undef DUMP
}

TheorySubclauseAnalyser *TheorySubclauseAnalyser::instance =
    new TheorySubclauseAnalyser();

#define IMPL_EQUIVALENCE_CLASS_FOR_LIT_EQUIV(i)                                \
   \
  bool EquivalenceClass<LitEquiv##i>::less::operator()(                        \
      const rc<AbsLiteral> &lhs, const rc<AbsLiteral> &rhs) const {            \
    switch (cmp##i<AbsLiteral>{}(*lhs.get(), *rhs.get())) {                    \
    case CMP_LESS:                                                             \
      return true;                                                             \
    default:                                                                   \
      return false;                                                            \
    }                                                                          \
  }

MAP(IMPL_EQUIVALENCE_CLASS_FOR_LIT_EQUIV, EQ_CLASSES)

AbsTerm &AbsTerm::var(int i) { return *new AbsVarTerm(i); }
AbsTerm &AbsTerm::fun(unsigned functor, vvec<refw<AbsTerm>> args) {
  return *new ACTerm(Function(functor), args);
}
AbsLiteral &create_abs_lit(bool positive, unsigned functor,
                           vvec<refw<AbsTerm>> args) {
  return *new AbsLiteral(positive, Predicate(functor), args);
}

void AbsLiteral::normalize() {
 CALL("AbsLiteral::normalize()");
  for (AbsTerm &t : terms) {
    t.normalize();
  }
  if (predicate.isEquality()) {
    ASS(terms.size() == 2);
    auto comparator = FINEST_COMPARATOR;
    auto rect = rect_maps();
    if (comparator(terms[0], terms[1], rect) == CMP_GREATER) {
      std::swap(terms[0], terms[1]);
    }
  }
}

void AbsTerm::rectify() {
  auto r = rect_map();
  this->rectify(r);
}

void AbsLiteral::rectify() {
  auto r = rect_map();
  for (auto &t : terms) {
    t.get().rectify(r);
  }
}

template <> struct Debug::print_debug<CmpResult> {
  void operator()(ostream &out, const CmpResult &a) const {
    switch (a) {
    case CMP_EQUIV:
      cout << "EQUIV";
      break;
    case CMP_LESS:
      cout << "LESS";
      break;
    case CMP_GREATER:
      cout << "GREATER";
      break;
    case CMP_NONE:
      cout << "NONE";
      break;
    }
  }
};

#define IMPL_PRINT_DEBUG_DEFAULT(CLASS) \
  template <> struct Debug::print_debug<CLASS> { \
    void operator()(ostream &out, const CLASS &a) const { \
      out << a; \
    } \
  }; \

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
    sort(_args.begin(), _args.end(), state_wrapped_comparator_std<AbsTerm, CmpUninterpretedVarsMatch, CmpVarsMatch, CmpNumberConstsNop>(map));
  }
}
void ACTerm::write(ostream& out) const {
  out << _fun;
  if (_args.size() > 0) {
    dumpTuple(out, _args, [](ostream& out, AbsTerm& t) { out << t; });
  }
}
void normalize_absliteral(AbsLiteral& lit) { lit.normalize(); }
bool equal_absliteral(const AbsLiteral& l,const AbsLiteral& r) { return l == r; }

#endif

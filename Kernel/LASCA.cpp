/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "LASCA.hpp"
#include "Debug/Assertion.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Stack.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/QKbo.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Metaiterators.hpp"
#include "Test/SyntaxSugar.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
namespace Kernel {
using Inferences::PolynomialEvaluation;
template<class T>
using RStack = Recycled<Stack<T>>;

template<class T, class... Ts>
RStack<T> rStack(T v, Ts... vs) {
  RStack<T> out;
  out->pushMany(std::move(v), std::move(vs)...);
  return out;
}

// number type to which integers are being translated to
using R = RealTraits;

std::ostream& operator<<(std::ostream& out, Literal* lit) 
{ return out << *lit; }

bool isInequality(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: 
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: return false;
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}


bool isEquality(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: 
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return false;
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: return true;
  }
  ASSERTION_VIOLATION
}

bool isIsInt(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: return true;
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: 
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return false;
  }
  ASSERTION_VIOLATION
}

std::ostream& operator<<(std::ostream& out, LascaPredicate const& self)
{ 
  switch(self) {
    case LascaPredicate::IS_INT_POS: return out << "isInt";
    case LascaPredicate::IS_INT_NEG: return out << "~isInt";
    case LascaPredicate::EQ: return out << "==";
    case LascaPredicate::NEQ: return out << "!=";
    case LascaPredicate::GREATER: return out << ">";
    case LascaPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
}


bool LascaState::hasSubstitutionProperty(SignedAtoms const& l)
{

  auto maybeEquiv = [this](TermList l, TermList r) -> bool 
  {
    ASS_NEQ(l, r)

    if (l.ground() && r.ground()) {
      return this->equivalent(l.term(), r.term());

    } else if (this->unify(l, r).isSome()) {
      return true;

    } else {
      return false;
    }
  };

  Stack<TermList> pos;
  Stack<TermList> neg;
  for (auto const& t_ : l.elems.iter()) {
    auto const& sign = std::get<0>(t_).sign;
    auto const& term = std::get<0>(t_).term;

    if (term.isVar() && sign != Sign::Zero) {
      if (concatIters(pos.iterFifo(), neg.iterFifo()).any([&](auto s) { return maybeEquiv(s, term); })) {
        return false;
      }
      pos.push(term);
      neg.push(term);
    } else if (sign != Sign::Zero) {

      auto& same  = sign == Sign::Pos ? pos : neg;
      auto& other = sign == Sign::Pos ? neg : pos;

      if (iterTraits(other.iterFifo())
        .any([&](auto& s) { return maybeEquiv(s, term); })) 
      {
          return false;
      }
      same.push(term);
    }
  }
  return true;
}


Literal* InequalityNormalizer::normalizeUninterpreted(Literal* lit) const 
{
  CALL("InequalityNormalizer::normalizeUninterpreted(Literal* lit) const")
  Stack<TermList> args(lit->arity());
  args.loadFromIterator(typeArgIter(lit));
  for (auto orig : termArgIter(lit)) {
    if (orig.isVar()) {
      args.push(orig);
    } else {
      auto norm = PolyNf::normalize(TypedTermList(orig.term()));
      auto eval = evaluator()
        .evaluate(norm)
        .value.map([](auto t) { return t.denormalize(); }) 
        || norm.denormalize();  // <- nothing was done during evaluation
      args.push(eval);
    }
  }
  auto out = Literal::create(lit, args.begin());
  DEBUG(*lit, " ==> ", *out)
  return out;
}

Recycled<Stack<Literal*>> InequalityNormalizer::normalizeLiteral(Literal* lit) const 
{
  Recycled<Stack<Literal*>> out;
  auto num = forAnyNumTraits([&](auto numTraits) { 
      auto norm = normalizeLasca<decltype(numTraits)>(lit);
      if (norm.isSome()) {
        out->loadFromIterator(
          arrayIter(norm->value)
            .map([](auto lit) { return lit.denormalize(); }));
        return true;
      } else {
        return false;
      }
    }); 
  if (!num) {
    out->push(normalizeUninterpreted(lit));
  }
  DEBUG(*lit, " ==> ", out)
  return out;
}

bool InequalityNormalizer::isNormalized(Clause* cl)  const
{ 
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    auto norm = normalizeLiteral(lit);
    if(norm->size() != 1 || lit != (*norm)[0]) {
      return false;
    }
  }
  return true;
}

#if VDEBUG
shared_ptr<LascaState> testLascaState(Options::UnificationWithAbstraction uwa, bool strongNormalization, Ordering* ordering, bool uwaFixedPointIteration) {

  auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/*rand*/ false, /*qkbo*/ true)) : nullptr;
  auto& ord = ordering == nullptr ? *qkbo : *ordering;
  auto state = LascaState::create(InequalityNormalizer(strongNormalization), &ord, uwa, uwaFixedPointIteration);
  if (qkbo)
        qkbo->setState(state);
  return state;
}
#endif

std::ostream& operator<<(std::ostream& out, SelectedSummand const& self)
{ 
  self.numeral().apply([&](auto n) -> void { out << n; });
  out << " " << self.monom();
  self.numTraits()
    .apply([&](auto numTraits) {
      for (auto s : self.contextTerms<decltype(numTraits)>()) {
        out << " + " << s;
      }
    });
  out << " " << self.symbol() << " 0";
  for (auto l : self.contextLiterals()) {
    out << " \\/ " << *l;
  }
  return out; 
}

Option<MaybeOverflow<AnyLascaLiteral>> InequalityNormalizer::renormalize(Literal* lit) const
{
  using Out = AnyLascaLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto overflown) { return overflown.map([](auto x) { return Out(x); }); });
  };
  return             wrapCoproduct(renormalizeLasca< IntTraits>(lit))
    || [&](){ return wrapCoproduct(renormalizeLasca< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(renormalizeLasca<RealTraits>(lit)); } 
    || Option<MaybeOverflow<Out>>();
}

Option<AnyLascaLiteral> LascaState::renormalize(Literal* lit)
{
  return this->normalizer.renormalize(lit)
    .andThen([](auto res) {
        // TODO overflow statistic
        return res.overflowOccurred 
          ? Option<AnyLascaLiteral>()
          : Option<AnyLascaLiteral>(res.value);
        });
}


Option<AnyInequalityLiteral> LascaState::renormalizeIneq(Literal* lit)
{
  return renormalize(lit)
    .andThen([](auto res) {
      return res.apply([](auto lit) { 
          return inequalityLiteral(lit).map([](auto x) { return AnyInequalityLiteral(x); }); 
      });
    });
}

PolyNf LascaState::normalize(TypedTermList term) 
{ 
  TIME_TRACE("lasca normalize term")
  auto norm = PolyNf::normalize(term);
  auto out = this->normalizer.evaluator().evaluate(norm); 
  if (out.overflowOccurred)  {
    WARN("failed to normalize: ", out.value)
    throw MachineArithmeticException("overflow while normalizing irc term");
  }
  return out.value || norm;
}

Option<AbstractingUnifier> LascaState::unify(TermList lhs, TermList rhs) const 
{ return AbstractingUnifier::unify(lhs, 0, rhs, 0, uwaMode(), uwaFixedPointIteration); }

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect)
{ return toCorrect.intDivide(gcd); }


IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r)
{ return IntegerConstantType::gcd(l, r); }

Ordering::Result compare(LascaPredicate l, LascaPredicate r) 
{
       if (l < r)  return Ordering::Result::LESS;
  else if (l > r)  return Ordering::Result::GREATER;
  else if (l == r) return Ordering::Result::EQUAL;
  else ASSERTION_VIOLATION
}

SelectedLiteral::SelectedLiteral(Clause* clause, unsigned litIdx, LascaState& shared)
  : cl(clause)
  , litIdx(litIdx)
  , interpreted(shared.renormalize(literal()))
{}

std::shared_ptr<LascaState> LascaState::globalState = nullptr;

using Guards = Recycled<Stack<Literal*>>;

template<class... Gs>
auto guards(Gs... gs) { return rStack(std::move(gs)...); }

template<class T> 
struct GuardedOption {
  T value;
  Guards guards;
 
  friend std::ostream& operator<<(std::ostream& out, GuardedOption const& self)
  { return out << self.value 
               << " guard(" << outputInterleaved(" | ", 
                     arrayIter(*self.guards).map([](auto g) -> Literal& { return *g; })) 
               << ")"; }
};

template<class U>
GuardedOption<U> guardedOption(U value, Guards guards) 
{ return {std::move(value), std::move(guards)}; }


template<class T> 
struct GuardedOptions {
  RStack<GuardedOption<T>> opts;

  friend std::ostream& operator<<(std::ostream& out, GuardedOptions const& self)
  { return out << outputInterleaved(" & ", self.opts->iter()); }
};

template<class T, class... Ts> 
GuardedOptions<T> guardedOptions(GuardedOption<T> t, GuardedOption<Ts>... ts) 
{ return GuardedOptions<T> { .opts = rStack(std::move(t), std::move(ts)...)}; }

template<class T>
struct _Unwrap;


template<class T> 
struct _Unwrap<GuardedOptions<T>> {
  using type = T;
};


// template<class T> 
// struct _Unwrap<T*> {
//   using type = T;
// };

template<class T> 
using Unwrap = typename _Unwrap<T>::type;

// gmap: (a -> b) -> GuardedOptions a -> GuardedOptions b
template<class F>
auto gmap(F f) 
{
   return [f = std::move(f)](auto arg) { 
     GuardedOptions<std::result_of_t<F(Unwrap<decltype(arg)>)>> out;
     for (auto& x : *arg.opts) {
       out.opts->push(guardedOption(f(std::move(x.value)), std::move(x.guards)));
     }
     return out; 
   };
}

template<class T> 
T clone(T const& orig)
{ return T(orig); }


// template<class T> 
// T clone(T& orig)
// { 
//   T const& _orig = orig;
//   return clone(_orig); 
// }

template<class T> 
T* clone(T* const& orig)
{ return orig; }

template<class T> 
RStack<T> clone(RStack<T> const& orig)
{
  RStack<T> out;
  out->loadFromIterator(arrayIter(*orig).map([](T const& x) -> T { return clone(x); }));
  return out;
}

// gflatten: GuardedOptions (GuardedOptions a) -> GuardedOptions a
template<class T>
auto gflatten(GuardedOptions<GuardedOptions<T>> in) 
{
  GuardedOptions<T> out;
  for (auto& opts : *in.opts) {
    auto& outerGuards = opts.guards;
    for (auto& opt : *opts.value.opts) {
      auto gs = clone(outerGuards);
      gs->loadFromIterator(opt.guards->iter());
      out.opts->push(guardedOption(clone(opt.value), std::move(gs)));
    }
  }
  return out;
}
// gflatmap: (a -> GuardedOptions b) -> GuardedOptions a -> GuardedOptions b
template<class F>
auto gflatmap(F f) 
{ return [f = std::move(f)](auto arg) { return gflatten(gmap(f)(std::move(arg))); }; }

// greturn: a -> GuardedOptions a
template<class T>
auto greturn(T t)  -> GuardedOptions<T>
{ 
  GuardedOptions<T> out;
  out.opts->push(guardedOption(std::move(t), Guards()));
  return out; 
}


template<class T>
class Slice {
  T* _cont;
  unsigned _size;
public:
  Slice(T* cont, unsigned size) : _cont(cont), _size(size) {}
  auto asTuple() const -> decltype(auto)
  { return std::tie(_cont, _size); }

  auto size() const { return _size; }

  T      & operator[](unsigned idx)       { ASS(idx < _size); return _cont[idx]; }
  T const& operator[](unsigned idx) const { ASS(idx < _size); return _cont[idx]; }

  auto indices() const { return range(0, size()); }

  auto iter() const { return indices().map([&](auto i) -> decltype(auto) { return (*this)[i]; }); }
  auto iter()       { return indices().map([&](auto i) -> decltype(auto) { return (*this)[i]; }); }

  friend std::ostream& operator<<(std::ostream& out, Slice const& self)
  { return out << "[ " << outputInterleaved(", ", self.iter()) << " ]"; }
};
template<class T>
Slice<T> slice(T* cont, unsigned size) { return Slice<T>(cont, size); }

// : (GuardedOptions a -> b) -> (GuardedOptions a -> GuardedOptions b)

// flipGuarded: GuardedOptions(Arg*) -> (GuardedOptions Arg)*
template<class T>
auto flipGuarded(Slice<GuardedOptions<T>> orig) -> GuardedOptions<RStack<T>> {
  // using Result = std::result_of_t<CreateTerm(unsigned, Arg*)>;
  GuardedOptions<RStack<T>> out;

  Recycled<Stack<unsigned>> guardSelections;
  guardSelections->loadFromIterator(range(0, orig.size()).map([](auto) { return 0; }));

  auto incr = [&]() {
    unsigned i = 0;
    while (i < guardSelections->size()) {
      (*guardSelections)[i]++;
      if ((*guardSelections)[i] >= orig[i].opts->size()) {
        (*guardSelections)[i] = 0;
        i++;
      } else {
        return true;
      }
    }
    return false;
  };

  do {
    auto chosen_arg_version = [&](auto arg_idx) -> GuardedOption<T>& {
      auto& arg = *orig[arg_idx].opts;
      auto chosen_version_idx = (*guardSelections)[arg_idx];
      return arg[chosen_version_idx];
    };
    RStack<T> ts;
    ts->loadFromIterator(
            range(0, orig.size())
              .map([&](unsigned i) { return chosen_arg_version(i).value; }));
    Guards guards;
    guards->loadFromIterator(range(0, orig.size())
              .flatMap([&](unsigned i) { return chosen_arg_version(i).guards->iter(); }));
    out.opts->push(guardedOption(std::move(ts), std::move(guards)));
  } while (incr());

  return out;
}

template<class CreateTerm, class Arg>
GuardedOptions<std::result_of_t<CreateTerm(unsigned, Arg*)>> liftGuarded(unsigned arity, GuardedOptions<Arg>* ts, CreateTerm createTerm) {
  return gmap([&](auto args) { return createTerm(arity, args->begin()); })(flipGuarded(slice(ts, arity)));

}

Option<std::function<GuardedOptions<TermList>(TermList*)>> translateInterpretedFunction_(unsigned f) {

  auto fng = [](auto _arity, auto f) { return some(std::function<GuardedOptions<TermList>(TermList*)>(
        [f = std::move(f)](TermList* args) -> GuardedOptions<TermList> { return f(args); })); 
  };


  auto fn = [](auto arity, auto f) { return some(std::function<GuardedOptions<TermList>(TermList*)>(
        [f = std::move(f)](TermList* args) -> GuardedOptions<TermList> { 
          return greturn(f(args));
          // return liftGuarded(arity, args, [f = std::move(f)](auto _arity, auto x){ return f(x); });
          // GuardedOptions<TermList> options;
          // options->push(make_pair(f(args), Guards()));
          // return options; 
        })); 
  };

  auto sym = env.signature->getFunction(f);
  if(sym->integerConstant()) {
    return fn(0, [sym](auto x) { return R::constantTl(typename R::ConstantType(sym->integerValue(), IntegerConstantType(1))); });
  }

  if(!theory->isInterpretedFunction(f))
    return {};


  auto _remainder = [](TermList* args, TermList quotient)
  { return R::add(args[0], R::minus(R::mul(args[1], quotient))); };

  auto remainder = [_remainder](auto quotient)
  { return [_remainder, quotient](TermList* ts) { return _remainder(ts, quotient(ts)); }; };


  auto remainderG = [_remainder](auto quotient /* TermList -> GuardedOptions<TermList>
  */)
  { 
    // return fmap(remainderG)
    return [_remainder, quotient](TermList* ts) -> GuardedOptions<TermList> { 
      return gmap([_remainder, ts](auto q){ return _remainder(ts, q); })(quotient(ts));;
   }; };

  auto quotientF = [](TermList* ts) { return R::toInt(R::div(ts[0], ts[1])); };
  auto quotientE = [=](TermList* ts) -> GuardedOptions<TermList> {
    auto out = guardedOptions(
         guardedOption(
           quotientF(ts), 
           guards(R::greater(false, ts[1], R::zero()))),
         guardedOption(
           R::minus(R::toInt(R::minus(R::div(ts[0], ts[1])))), 
           guards(R::less(false, ts[1], R::zero())))
        );
    return out;
  };
  switch(theory->interpretFunction(f)) {
    case Interpretation::EQUAL: 

    case Interpretation::INT_IS_INT: 
    case Interpretation::INT_IS_RAT: 
    case Interpretation::INT_IS_REAL: 
    case Interpretation::INT_GREATER: 
    case Interpretation::INT_GREATER_EQUAL: 
    case Interpretation::INT_LESS: 
    case Interpretation::INT_LESS_EQUAL: 
    case Interpretation::INT_DIVIDES: 
    case Interpretation::RAT_IS_INT:
    case Interpretation::RAT_IS_RAT:
    case Interpretation::RAT_IS_REAL:
    case Interpretation::RAT_GREATER:
    case Interpretation::RAT_GREATER_EQUAL:
    case Interpretation::RAT_LESS:
    case Interpretation::RAT_LESS_EQUAL:
    case Interpretation::REAL_IS_INT:
    case Interpretation::REAL_IS_RAT:
    case Interpretation::REAL_IS_REAL:
    case Interpretation::REAL_GREATER:
    case Interpretation::REAL_GREATER_EQUAL:
    case Interpretation::REAL_LESS:
    case Interpretation::REAL_LESS_EQUAL:
      ASSERTION_VIOLATION_REP("Not a function interpretation")

      //numeric functions

    case Interpretation::INT_SUCCESSOR:   return fn(1, [](TermList* ts) { return R::add(ts[0], R::one()); });
    case Interpretation::INT_UNARY_MINUS: return fn(1, [](TermList* ts) { return R::minus(ts[0]); });
    case Interpretation::INT_PLUS:        return fn(2, [](TermList* ts) { return R::add(ts[0], ts[1]); });
    case Interpretation::INT_MINUS:       return fn(2, [](TermList* ts) { return R::add(ts[0], R::minus(ts[1])); });
    case Interpretation::INT_MULTIPLY:    return fn(2, [](TermList* ts) { return R::mul(ts[0], ts[1]); });

    case Interpretation::INT_CEILING:
    case Interpretation::INT_TRUNCATE:
    case Interpretation::INT_ROUND: 
                                          // TODO check differenc between RAT_TO_INT and RAT_FLOOR
    case Interpretation::INT_TO_INT:
    case Interpretation::INT_FLOOR:       return fn(1, [](auto ts) { return ts[0]; });

    case Interpretation::INT_QUOTIENT_F:  return fn(2, quotientF);
    case Interpretation::INT_REMAINDER_F: return fn(2, remainder(quotientF));

    case Interpretation::INT_QUOTIENT_E:  return fng(2, quotientE);
    case Interpretation::INT_REMAINDER_E: return fng(2, remainderG(quotientE));

    case Interpretation::INT_QUOTIENT_T:
    case Interpretation::INT_REMAINDER_T:
    case Interpretation::INT_ABS:
        ASSERTION_VIOLATION_REP("TODO: look up the semantics of this and implement a translation")
        return {};

    case Interpretation::RAT_UNARY_MINUS:
    case Interpretation::RAT_PLUS:
    case Interpretation::RAT_MINUS:
    case Interpretation::RAT_MULTIPLY:
    case Interpretation::RAT_QUOTIENT:
    case Interpretation::RAT_QUOTIENT_E:
    case Interpretation::RAT_QUOTIENT_T:
    case Interpretation::RAT_QUOTIENT_F:
    case Interpretation::RAT_REMAINDER_E:
    case Interpretation::RAT_REMAINDER_T:
    case Interpretation::RAT_REMAINDER_F:
    case Interpretation::RAT_FLOOR:
    case Interpretation::RAT_ROUND:
    case Interpretation::REAL_UNARY_MINUS:
    case Interpretation::REAL_PLUS:
    case Interpretation::REAL_MINUS:
    case Interpretation::REAL_MULTIPLY:
    case Interpretation::REAL_QUOTIENT:
    case Interpretation::REAL_QUOTIENT_E:
    case Interpretation::REAL_QUOTIENT_T:
    case Interpretation::REAL_QUOTIENT_F:
    case Interpretation::REAL_REMAINDER_E:
    case Interpretation::REAL_REMAINDER_T:
    case Interpretation::REAL_REMAINDER_F:
    case Interpretation::REAL_FLOOR:
    case Interpretation::REAL_ROUND:
    case Interpretation::RAT_TO_INT:
    case Interpretation::RAT_TO_RAT:
    case Interpretation::RAT_TO_REAL:
    case Interpretation::REAL_TO_INT:
    case Interpretation::REAL_TO_RAT:
    case Interpretation::REAL_TO_REAL:
        return {}; // rat and real functions

    case Interpretation::INT_TO_RAT:
    case Interpretation::INT_TO_REAL:
        ASSERTION_VIOLATION_REP("TODO implement. needs to be guarded to be sound i think")
        return {}; // rat and real functions

      // array functions
    case Interpretation::ARRAY_SELECT: 
    // {
    //     auto ty = env.signature->getFunction(f)->fnType();
    //     if (ty->result() == IntTraits::sort() || ty->arg(1) == IntTraits::sort()) {
    //
    //     }
    // }
    case Interpretation::ARRAY_STORE:
        ASSERTION_VIOLATION_REP("TODO integrate with arrays")
        return {};

    case Interpretation::INVALID_INTERPRETATION:
    case Interpretation::ARRAY_BOOL_SELECT:
        ASSERTION_VIOLATION_REP("not a function interpretation")
        return {};

    case Interpretation::REAL_TRUNCATE:
    case Interpretation::RAT_TRUNCATE:
        ASSERTION_VIOLATION_REP("TODO: translated to ite + floor")
        return {};
    case Interpretation::REAL_CEILING:
    case Interpretation::RAT_CEILING:
        ASSERTION_VIOLATION_REP("TODO: this should translate to -floor(-x)")
        return {};
    }
  ASSERTION_VIOLATION
}
Option<std::function<Literal*(TermList*)>> translateInterpretedPredicate(unsigned f)
{
  if(!theory->isInterpretedPredicate(f))
    return {};

  auto fn = [](auto x) { return some(std::function<Literal*(TermList*)>(std::move(x))); };

  switch(theory->interpretPredicate(f)) {
    case Interpretation::EQUAL: return fn([](auto x) -> Literal* { ASSERTION_VIOLATION_REP("this should never be called bc alas equality is special") });

    case Interpretation::INT_IS_INT:  
    case Interpretation::INT_IS_RAT: 
    case Interpretation::INT_IS_REAL: 
        ASSERTION_VIOLATION_REP("TODO")
      return {};

    case Interpretation::INT_GREATER:       return fn([](auto ts){ return R::greater(true, ts[0], ts[1]); });
    case Interpretation::INT_GREATER_EQUAL: return fn([](auto ts){ return R::geq    (true, ts[0], ts[1]); });
    case Interpretation::INT_LESS:          return fn([](auto ts){ return R::less   (true, ts[0], ts[1]); }); 
    case Interpretation::INT_LESS_EQUAL:    return fn([](auto ts){ return R::leq    (true, ts[0], ts[1]); }); 
    case Interpretation::INT_DIVIDES:       return fn([](auto ts){ return R::isInt  (true, R::div(ts[1], ts[0])); });

    case Interpretation::RAT_IS_INT:
    case Interpretation::RAT_IS_RAT:
    case Interpretation::RAT_IS_REAL:
    case Interpretation::RAT_GREATER:
    case Interpretation::RAT_GREATER_EQUAL:
    case Interpretation::RAT_LESS:
    case Interpretation::RAT_LESS_EQUAL:
    case Interpretation::REAL_IS_INT:
    case Interpretation::REAL_IS_RAT:
    case Interpretation::REAL_IS_REAL:
    case Interpretation::REAL_GREATER:
    case Interpretation::REAL_GREATER_EQUAL:
    case Interpretation::REAL_LESS:
    case Interpretation::REAL_LESS_EQUAL:
      return {};
    case Interpretation::ARRAY_BOOL_SELECT:
      ASSERTION_VIOLATION_REP("TODO integrate with arrays")
      return {};

    case Interpretation::INT_SUCCESSOR:
    case Interpretation::INT_UNARY_MINUS:
    case Interpretation::INT_PLUS:
    case Interpretation::INT_MINUS:
    case Interpretation::INT_MULTIPLY:
    case Interpretation::INT_QUOTIENT_E:
    case Interpretation::INT_QUOTIENT_T:
    case Interpretation::INT_QUOTIENT_F:
    case Interpretation::INT_REMAINDER_E:
    case Interpretation::INT_REMAINDER_T:
    case Interpretation::INT_REMAINDER_F:
    case Interpretation::INT_FLOOR:
    case Interpretation::INT_CEILING:
    case Interpretation::INT_TRUNCATE:
    case Interpretation::INT_ROUND:
    case Interpretation::INT_ABS:
    case Interpretation::INT_TO_INT:
    case Interpretation::INT_TO_RAT:
    case Interpretation::INT_TO_REAL:
    case Interpretation::ARRAY_SELECT:
    case Interpretation::ARRAY_STORE:
    case Interpretation::RAT_UNARY_MINUS:
    case Interpretation::RAT_PLUS:
    case Interpretation::RAT_MINUS:
    case Interpretation::RAT_MULTIPLY:
    case Interpretation::RAT_QUOTIENT:
    case Interpretation::RAT_QUOTIENT_E:
    case Interpretation::RAT_QUOTIENT_T:
    case Interpretation::RAT_QUOTIENT_F:
    case Interpretation::RAT_REMAINDER_E:
    case Interpretation::RAT_REMAINDER_T:
    case Interpretation::RAT_REMAINDER_F:
    case Interpretation::RAT_FLOOR:
    case Interpretation::RAT_CEILING:
    case Interpretation::RAT_TRUNCATE:
    case Interpretation::RAT_ROUND:
    case Interpretation::REAL_UNARY_MINUS:
    case Interpretation::REAL_PLUS:
    case Interpretation::REAL_MINUS:
    case Interpretation::REAL_MULTIPLY:
    case Interpretation::REAL_QUOTIENT:
    case Interpretation::REAL_QUOTIENT_E:
    case Interpretation::REAL_QUOTIENT_T:
    case Interpretation::REAL_QUOTIENT_F:
    case Interpretation::REAL_REMAINDER_E:
    case Interpretation::REAL_REMAINDER_T:
    case Interpretation::REAL_REMAINDER_F:
    case Interpretation::REAL_FLOOR:
    case Interpretation::REAL_CEILING:
    case Interpretation::REAL_TRUNCATE:
    case Interpretation::REAL_ROUND:
    case Interpretation::RAT_TO_INT:
    case Interpretation::RAT_TO_RAT:
    case Interpretation::RAT_TO_REAL:
    case Interpretation::REAL_TO_INT:
    case Interpretation::REAL_TO_RAT:
    case Interpretation::REAL_TO_REAL:
    case Interpretation::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION_REP("not a predicate interpretation")
      return {};
    }
  ASSERTION_VIOLATION
}

// GuardedOptions<TermList> liftGuarded(unsigned functor, unsigned arity, GuardedOptions<TermList>* ts, unsigned i) {
//
//   if (i == arity) {
//
//   }
// }

void InequalityNormalizer::realization(Problem& p)
{
  auto trans = tranlateSignature();
  auto& realizedFs  = trans.first;
  auto& realizedPs  = trans.second;

  auto translateTerm = [&](TermList t) -> GuardedOptions<TermList> { 
    return evalBottomUp<GuardedOptions<TermList>>(t, [&](auto orig, auto* evalArgs) {
        GuardedOptions<TermList> out;
        if (orig.isVar()) {
          out.opts->push(guardedOption(orig, Guards()));
          return out;
        } else {
          auto f = orig.term()->functor();
          auto arity = orig.term()->arity();
          GuardedOptions<RStack<TermList>> args = flipGuarded(slice(evalArgs, arity));
          auto itp = translateInterpretedFunction_(f);
          if (itp) {
            return gflatmap([&](auto args) { return (*itp)(args->begin()); })(std::move(args));
          } else {
            return gmap([&](auto args) { return TermList(Term::create(realizedFs[f], arity, args->begin())); })(std::move(args));
          }
        }
    });
  };


  auto translateLit = [&](Literal* lit) -> GuardedOptions<Literal*> {
    auto p = lit->functor();
    Recycled<Stack<GuardedOptions<TermList>>> args;
    args->loadFromIterator(
        anyArgIter(lit)
          .map([&](TermList t) 
            { return translateTerm(t); }));

    return liftGuarded(args->size(), args->begin(), 
        [&](unsigned arity, TermList* args) -> Literal* {
          if (lit->isEquality()) {
            auto s = SortHelper::getEqualityArgumentSort(lit);
            return Literal::createEquality(lit->polarity(), args[0], args[1], s == IntTraits::sort() ? R::sort() : s);
          }

          auto itp = translateInterpretedPredicate(p);

          if (itp) {
            auto res = (*itp)(args);
            return lit->polarity() != res->polarity() ? Literal::complementaryLiteral(res) : res;
          } else {
            return Literal::create(
                realizedPs[lit->functor()], 
                arity,
                lit->polarity(),
                /* commutative */ false,
                args);
          }


        });

    // if (lit->isEquality()) {
    //   auto s = SortHelper::getEqualityArgumentSort(lit);
    //   return Literal::createEquality(lit->polarity(), translateTerm(lit->termArg(0)), translateTerm(lit->termArg(1)), s == IntTraits::sort() ? R::sort() : s);
    // }
    // auto itp = translateInterpretedPredicate(p);
    //
    // Recycled<Stack<TermList>> args;
    // args->loadFromIterator(
    //     anyArgIter(lit).map([&](auto arg) { return translateTerm(arg); }));
    // if (itp) {
    //   auto res = (*itp)(args->begin());
    //   return lit->polarity() != res->polarity() ? Literal::complementaryLiteral(res) : res;
    // } else {
    //   return Literal::createFromIter(
    //       lit->polarity(),
    //       realizedPs[lit->functor()], 
    //       args->iterFifo()
    //       );
    // }

  };
  p.mapUnits([&](auto c_) {
      Recycled<Stack<Unit*>> out;
      ASS(c_->isClause());
      auto input =  static_cast<Clause*>(c_);

      Recycled<Stack<GuardedOptions<Literal*>>> lits;

      
      for (auto l : iterTraits(input->iterLits())) {
        

        auto itp = normalizeLasca<IntTraits>(l);
        if (itp) {
          for (auto nl : itp->value) {
            auto trm = translateTerm(nl.term().denormalize());
            lits->push(liftGuarded(1, &trm,
                  [](auto _arity, auto args) { return R::isInt(false, args[0]); }));
            // lits->push(R::isInt(false, trm));
          }
        }
        lits->push(translateLit(l));

      }

      GuardedOptions<Recycled<Stack<Literal*>>> clauses = liftGuarded(lits->size(), lits->begin(),
          [](auto arity, auto args) {
            Recycled<Stack<Literal*>> ls;
            ls->loadFromIterator(range(0, arity).map([&](auto i) { return args[i]; }));
            return ls;
          });

      out->loadFromIterator(
          iterTraits(clauses.opts->iter())
          .map([input](GuardedOption<RStack<Literal*>>& cl) -> Unit* {
              auto out = std::move(cl.value);
              out->loadFromIterator(cl.guards->iter());
              return Clause::fromStack(*out, Inference(FormulaTransformation(InferenceRule::ALASCAI_REALIZATION, input)));
            })
          );



      return out;
  });

  // TODO replace these axioms by rules (?)
  auto x = TermList::var(0);

  p.units() = 
    /* isInt(x) -> toInt(x) == x */
        UnitList::cons(Clause::fromStack({ R::isInt(false, x), R::eq(true, x, R::toInt(x))}, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
    /* isInt(toInt(x)) */
      , UnitList::cons(Clause::fromStack({ R::isInt(true, R::toInt(x)) }, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
    /* 0 <= x - toInt(x) */
      , UnitList::cons(Clause::fromStack({ R::leq(true, R::zero(), R::add(x, R::minus(R::toInt(x)))) }, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
    /* x - toInt(x) < 1 */
      , UnitList::cons(Clause::fromStack({ R::less(true, R::add(x, R::minus(R::toInt(x))), R::one()) }, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
      , p.units())
      )))
    ;

  for (auto origF : range(0, realizedFs.size())) {
    auto newF = realizedFs[origF];
    Recycled<Stack<TermList>> args;
    if (newF != unsigned(-1) && newF != origF) {
      // ^^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^^^-> has been transformed
      //     \->not interpreted

      auto arity = env.signature->getFunction(newF)->arity();
      while(args->size() < arity) {
        args->push(TermList::var(args->size()));
      }

      if (env.signature->getFunction(origF)->fnType()->result() == IntTraits::sort()) {


        // adding isInt(newF(x1, ..., xn))
        auto cl = Clause::fromStack({ R::isInt(true, TermList(Term::create(newF, arity, args->begin()))) }, Inference(TheoryAxiom(InferenceRule::ALASCAI_REALIZATION_AXIOM)));
        p.units() = UnitList::cons(cl, p.units());
      }
    }
  }

}

pair<Stack<unsigned>, Stack<unsigned>> InequalityNormalizer::tranlateSignature()
{
  Stack<unsigned> realizedFs;

  auto reals = R::sort();
  auto ints  = IntTraits::sort();

  auto iterArgs = [&](OperatorType* o)  
    { return range(0, o->arity())
               .map([=](auto i) { return o->arg(i); }); };


  auto mappedArgs = [&](OperatorType* o)  { 
      Recycled<Stack<TermList>> out;
      out->loadFromIterator(iterArgs(o)
          .map([&](auto a) {  return a == ints ? reals : a; }));
      return out;
    };

  auto hasIntArgs = [&](OperatorType* o)  
    { return iterArgs(o).any([&](auto a) { return a == ints; }); };

  for (auto f : range(0, env.signature->functions())) {
    auto f_ = translateInterpretedFunction_(f);
    if (f_) {
      realizedFs.push(unsigned(-1)); // <- dummy. should never be accessed
    } else {
      auto sym = env.signature->getFunction(f);
      auto op = sym->fnType();
      if (hasIntArgs(op) || op->result() == ints) {
        Recycled<Stack<TermList>> args = mappedArgs(op);
        auto res = op->result() == ints ? reals : op->result();
        
        realizedFs.push(env.signature->addFreshFunction(
                OperatorType::getFunctionType(*args, res), 
                sym->name().c_str()));
      } else {
        realizedFs.push(f);
      }
    }
  }

  Stack<unsigned> realizedPs;
  for (auto p : range(0, env.signature->predicates())) {
    auto p_ = translateInterpretedPredicate(p);
    if (p_) {
      realizedPs.push(-1); // <- dummy. should never be accessed
    } else {
      auto sym = env.signature->getPredicate(p);
      auto op = sym->predType();
      if (hasIntArgs(op)) {
        Recycled<Stack<TermList>> args = mappedArgs(op);
        realizedPs.push(
              env.signature->addFreshPredicate(
                OperatorType::getPredicateType(*args),
                sym->name().c_str()));
      } else {
        realizedPs.push(p);
      }
    }
  }
  return make_pair(std::move(realizedFs), std::move(realizedPs));
}

} // namespace Kernel


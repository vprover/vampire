#ifndef __POLYNOMIAL__H__
#define __POLYNOMIAL__H__

#include "Lib/STLAllocator.hpp"
#include "Kernel/NumTraits.hpp"
#include <cassert>
#include "Lib/Coproduct.hpp"
#include "Lib/Optional.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Theory.hpp"
#include <map> // TODO replace by Map
#include "Lib/UniqueShared.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include <type_traits>


namespace Kernel {


class TypedTermList : public TermList
{
  unsigned _sort;
public:
  TypedTermList(TermList t, unsigned sort) : TermList(t), _sort(sort) {}
  TypedTermList(Term* t) : TypedTermList(TermList(t), SortHelper::getResultSort(t)) {}
  unsigned sort() const { return _sort; }
};



/** newtype for wrapping varible ids */
class Variable 
{
  unsigned _num;
public: 
  Variable() : _num() {}
  explicit Variable(unsigned num) : _num(num) {}
  unsigned id() const { return _num; }
  friend bool operator==(Variable lhs, Variable rhs) 
  { return lhs._num == rhs._num; }

  friend bool operator!=(Variable lhs, Variable rhs) 
  { return !(lhs == rhs); }

  friend struct std::hash<Variable>;

  friend bool operator<(Variable const& lhs, Variable const& rhs)
  { return lhs._num < rhs._num; }

  friend std::ostream& operator<<(std::ostream& out, const Variable& self) 
  { return out << "X" << self._num; }
};


/** newtype for wrapping function ids (also often called functors in vampire) */
class FuncId 
{
  unsigned _num;
  
  Signature::Symbol* symbol() const { return env.signature->getFunction(_num); }
public: 
  explicit FuncId(unsigned num) : _num(num) {}
  unsigned arity() { return symbol()->arity(); }

  friend bool operator==(FuncId const& lhs, FuncId const& rhs) 
  { return lhs._num == rhs._num; }

  friend bool operator!=(FuncId const& lhs, FuncId const& rhs) 
  { return !(lhs == rhs); }

  friend struct std::hash<FuncId>;

  friend std::ostream& operator<<(std::ostream& out, const FuncId& self) 
  { return out << self.symbol()->name(); }

  unsigned id() const 
  { return _num; }

  Theory::Interpretation interpretation() const 
  { return theory->interpretFunction(_num); }

  bool isInterpreted() const
  { return theory->isInterpretedFunction(_num); }

  Optional<Theory::Interpretation> tryInterpret() const
  { 
    return isInterpreted() ? some<Theory::Interpretation>(interpretation())
                           : none<Theory::Interpretation>();
  }

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const
  { 
    using Const = typename Number::ConstantType;
    Const out;
    if (theory->tryInterpretConstant(_num, out)) {
      return Optional<Const>(out);
    } else {
      return Optional<Const>();
    }
  }

  // template<class ConstantType>
  // static PolyNf fromNumeral(ConstantType c) const
  // {
  //   TODO
  // }
};

class PolyNf;
template<class Number> class        Polynom;
template<class Number> class        Monom;

/** 
 * Represents a summand in a polynom of the number type Number 
 * e.g. a term like 3 * (a*x) would be represented as 
 * PolyPair { 3, Monom { a, x }}
 */
template<class Number> 
struct PolyPair {
  CLASS_NAME(MonomPair)

  using Coeff = typename Number::ConstantType;

  Coeff coeff;
  UniqueShared<Monom<Number>> monom;

  PolyPair(typename Number::ConstantType coeff, UniqueShared<Monom<Number>> monom) 
    : coeff(coeff), monom(monom)
  {}

  friend bool operator<(PolyPair const& l, PolyPair const& r)
  { return std::tie(l.monom, l.coeff) < std::tie(r.monom, r.coeff); }

  friend bool operator==(PolyPair const& l, PolyPair const& r)
  { return std::tie(l.monom, l.coeff) == std::tie(r.monom, r.coeff); }

  friend bool operator!=(PolyPair const& l, PolyPair const& r)
  { return !(l == r); }

  static PolyPair zero() 
  { 
    static PolyPair p = PolyPair(Coeff(0), unique(Monom<Number>()));
    return p; 
  }

  friend std::ostream& operator<<(std::ostream& out, const PolyPair& self)
  { 
    if (self.coeff != Coeff(1)) {
      out << self.coeff;
    }
    return out << self.monom; 
  }

  Optional<Variable> tryVar() const 
  {
    using Opt = Optional<Variable>;
    if (coeff == Coeff(1)) {
      return  monom->tryVar();
    } else {
      return  Opt();
    }
  }

  ~PolyPair() {
    CALL("~PolyPair")
  }

};

class AnyPoly;

std::ostream& operator<<(std::ostream& out, const PolyNf& self);
bool operator==(PolyNf const& lhs, PolyNf const& rhs);

/**
 * Represents an ordenary complex term, in the PolyNF term tree.
 */
class FuncTerm 
{
  FuncId _fun;
  Stack<PolyNf> _args;
public:
  FuncTerm(FuncId f, Stack<PolyNf>&& args) : _fun(f), _args(std::move(args)) { }
  FuncTerm(FuncId f, PolyNf* args) : _fun(f), _args(Stack<PolyNf>::fromIterator(getArrayishObjectIterator(args, f.arity()))) { }

  friend bool operator==(FuncTerm const& lhs, FuncTerm const& rhs) 
  { return lhs._fun == rhs._fun && lhs._args == rhs._args; }

  friend bool operator!=(FuncTerm const& lhs, FuncTerm const& rhs) 
  { return !(lhs == rhs); }

  unsigned arity() const 
  { return _args.size(); }

  friend struct std::hash<FuncTerm>;

  friend std::ostream& operator<<(std::ostream& out, const FuncTerm& self) ;

  FuncId function() const { return _fun; }
  PolyNf const& arg(unsigned i) const { return _args[i]; }


  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const
  { return _fun.template tryNumeral<Number>(); }

};

POLYMORPHIC_FUNCTION(TermList, toTerm   , const& t, TermList* results; ) { return t->toTerm(results); }
POLYMORPHIC_FUNCTION(unsigned, nSummands, const& t,            ) { return t->nSummands(); }
POLYMORPHIC_FUNCTION(unsigned, nFactors , const& t, unsigned i;) { return t->nFactors(i); }
POLYMORPHIC_FUNCTION(PolyNf const&, termAt   , const& t, unsigned summand; unsigned factor;) { return t->monomAt(summand)->termAt(factor); }

using IntPoly = Polynom<IntTraits>;
using RatPoly = Polynom<RatTraits>;
using RealPoly = Polynom<RealTraits>;

using AnyPolySuper = Coproduct< 
  UniqueShared<Polynom<NumTraits<IntegerConstantType>>>, 
  UniqueShared<Polynom<NumTraits<RationalConstantType>>>, 
  UniqueShared<Polynom<NumTraits<RealConstantType>>>
  > ;



template<class NumIn, class NumOut>
struct __ToNumeralHelper 
{
  Optional<typename NumOut::ConstantType> operator()(UniqueShared<Polynom<NumIn>>) const
  { return Optional<typename NumOut::ConstantType>(); }
};

template<class Num>
struct __ToNumeralHelper<Num,Num>
{
  Optional<typename Num::ConstantType> operator()(UniqueShared<Polynom<Num>> p) const
  { return p->toNumber(); }
};

template<class NumOut>  
struct PolymorphicToNumeral 
{
  template<class NumIn>
  Optional<typename NumOut::ConstantType> operator()(UniqueShared<Polynom<NumIn>> const& p) const
  { return __ToNumeralHelper<NumIn, NumOut>{}(p); }
};

class AnyPoly : public AnyPolySuper
{
public:
  
  template<class C>
  using Poly = UniqueShared<Polynom<NumTraits<C>>>;

  AnyPoly(Poly< IntegerConstantType> x) : Coproduct(variant<0>(std::move(x))) {  }
  AnyPoly(Poly<RationalConstantType> x) : Coproduct(variant<1>(std::move(x))) {  }
  AnyPoly(Poly<    RealConstantType> x) : Coproduct(variant<2>(std::move(x)))  {  }

  // TODO make this return the UniqueShared<...>
  template<class Number> 
  Polynom<Number> const& downcast() const& { return *unwrap<UniqueShared<Polynom<Number>>>(); }

  template<class Number> 
  UniqueShared<Polynom<Number>> unwrapType() const& { return unwrap<UniqueShared<Polynom<Number>>>(); }

  template<class Number> 
  bool isType() const { return is<UniqueShared<Polynom<Number>>>(); }

  AnyPoly replaceTerms(PolyNf* newTs) const;

  unsigned nSummands() const { return apply(Polymorphic::nSummands{}); }
  unsigned nFactors(unsigned i) const { return apply(Polymorphic::nFactors{i}); }
  const PolyNf& termAt(unsigned summand, unsigned factor) {  return apply(Polymorphic::termAt{summand, factor}); }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self) {
    if (self.is<0>()) return out << self.unwrap<0>();
    if (self.is<1>()) return out << self.unwrap<1>();
    if (self.is<2>()) return out << self.unwrap<2>();
    ASSERTION_VIOLATION
  }


  friend struct std::hash<AnyPoly>;

  TermList toTerm(TermList* results) const
  { return apply(Polymorphic::toTerm{results}); }

  AnyPoly simplify(PolyNf* simplifiedArgs) const;

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const&
  { return apply(PolymorphicToNumeral<Number>{}); }
};

POLYMORPHIC_FUNCTION(AnyPoly, replaceTerms, const& t, PolyNf* newTs;) { return AnyPoly(unique(t->replaceTerms(newTs))); }

inline AnyPoly AnyPoly::replaceTerms(PolyNf* newTs) const { return apply(Polymorphic::replaceTerms{newTs}); }

using PolyNfSuper = Lib::Coproduct<UniqueShared<FuncTerm>, Variable, AnyPoly>;
/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * TODO add more documentation
 */
class PolyNf : public PolyNfSuper
{
public:
  CLASS_NAME(PolyNf)
  // USE_ALLOCATOR(PolyNf)


  PolyNf(UniqueShared<FuncTerm> t) : Coproduct(t) {}
  PolyNf(Variable               t) : Coproduct(t) {}
  PolyNf(AnyPoly                t) : Coproduct(t) {}
  static PolyNf normalize(TypedTermList t);

  friend bool operator==(PolyNf const& lhs, PolyNf const& rhs) 
  { return static_cast<Coproduct const&>(lhs) == static_cast<Coproduct const&>(rhs); }

  friend bool operator!=(PolyNf const& lhs, PolyNf const& rhs) 
  { return !(lhs == rhs); }

  friend struct std::hash<PolyNf>;

  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self)
  { 
    self.match(
        [&](UniqueShared<FuncTerm> t) { out << t; }, 
        [&](Variable               t) { out << t; },
        [&](AnyPoly                t) { out << t; }
      );
    return out;

  }

  bool    isPoly() const { return is<2>(); }
  AnyPoly const& asPoly() const& { return unwrap<2>(); }
  AnyPoly     && asPoly()     && { return std::move(unwrap<2>()); }
  AnyPoly      & asPoly()      & { return unwrap<2>(); }

  TermList toTerm() const
  { 
    CALL("PolyNf::toTerm")
    DEBUG("converting ", *this)
    struct Eval 
    {
      using Arg    = PolyNf;
      using Result = TermList;

      TermList operator()(PolyNf orig, TermList* results)
      { return orig.match(
          [&](UniqueShared<FuncTerm> t) { return TermList(Term::create(t->function().id(), t->arity(), results)); },
          [&](Variable               v) { return TermList::var(v.id()); },
          [&](AnyPoly                p) { return p.toTerm(results); }
          ); }
    };
    static Memo::Hashed<PolyNf, TermList> memo;
    return evaluateBottomUp(*this, Eval{}, memo);
  }

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const
  { 
    using Const = typename Number::ConstantType;
    return match(
        [](UniqueShared<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
        [](Variable               t) { return Optional<Const>();              },
        [](AnyPoly                t) { return t.template tryNumeral<Number>(); }
      );
  }

  Optional<Variable> tryVar() const 
  { return as<Variable>().template innerInto<Variable>(); }

  class Iter;
  IterTraits<Iter> iter() const;
};

inline bool operator<(const PolyNf& lhs, const PolyNf& rhs)  // TODO get rid of that and use the vampire sorting method 
{ return std::less<PolyNfSuper>{}(lhs,rhs); }


/** 
 * Represents a factor in a monom. Each unique term contained in the monom is stored 
 * together with the number of occurences of the term within that monom.
 *
 * e.g. a term like (x * x * a * x) is represented as 
 * Monom { MonomPair(x, 3), MonomPair(a, 1) }
 */
template<class Number> 
struct MonomPair {
  CLASS_NAME(MonomPair)
  // USE_ALLOCATOR(MonomPair)
  int power;
  PolyNf term;

  MonomPair(PolyNf term, int power) 
    : power(power), term(term)
  {}

  friend bool operator<(MonomPair const& l, MonomPair const& r)
  { return std::tie(l.term, l.power) < std::tie(r.term, r.power); }

  friend bool operator==(MonomPair const& l, MonomPair const& r)
  { return std::tie(l.term, l.power) == std::tie(r.term, r.power); }

  friend bool operator!=(MonomPair const& l, MonomPair const& r)
  { return !(l == r); }

  friend std::ostream& operator<<(std::ostream& out, const MonomPair& self) {
    out << self.term; 
    if (self.power != 1) 
      out << "^" << self.power;
    return out;
  }

  Optional<Variable> tryVar() const 
  { return power == 1 ? term.tryVar() : none<Variable>(); }

};



template<class Number>
class Monom 
{
  using MonomTermOrdering = std::less<PolyNf>;
  using MonomPair = ::Kernel::MonomPair<Number>;
  using PolyPair  = ::Kernel::PolyPair<Number>;
  using Polynom   = ::Kernel::Polynom<Number>;
  using Const = typename Number::ConstantType;
  Stack<MonomPair> _factors;
  friend struct std::hash<Monom>;

public:
  Monom(Stack<MonomPair>&& factors) : _factors(std::move(factors)) { }
  Monom() : Monom(decltype(_factors)()) { }
  Monom(PolyNf t) : _factors { MonomPair ( t, 1 ) }  { }
  Monom(PolyNf t1, PolyNf t2) 
    : _factors(t1 == t2 ? decltype(_factors) ({MonomPair ( t1, 2 )  }) : 
               MonomTermOrdering{}(t1, t2) ? decltype(_factors) ({ MonomPair ( t1, 1 ), MonomPair ( t2, 1 ) }) 
                                           : decltype(_factors) ({ MonomPair ( t2, 1 ), MonomPair ( t1, 1 ) }) 
                          )  { }

  unsigned nFactors() const 
  { return _factors.size(); }

  MonomPair & factorAt(unsigned i) 
  { return _factors[i]; }

  MonomPair const& factorAt(unsigned i) const
  { return _factors[i]; }

  PolyNf const& termAt(unsigned i) const
  { return _factors[i].term; }

  bool isPolynom() const
  { return nFactors() == 1 
      && _factors[0].power == 1 
      && _factors[0].term.template is<AnyPoly>(); }

  UniqueShared<Polynom> asPolynom() const
  { 
    ASS(isPolynom());
    return _factors[0].term
      .template unwrap<AnyPoly>()
      .template unwrap<UniqueShared<Polynom>>(); 
  }

            // && simpl.monom->nFactors() == 1 
            // && simpl.monom->_factors[0].template is<AnyPoly>()

public:

  USE_ALLOCATOR(Monom)
  CLASS_NAME(Monom)

  PolyPair simplify(PolyNf* simplifiedArgs) const
  { 

    auto pow = [](Const c, int power) -> Const {
      ASS(power > 0)
      auto out = c;
      while (--power > 0) {
        out = out * c;
      }
      return out;
    };

    Stack<MonomPair> args(nFactors());
    for (unsigned i = 0; i < nFactors(); i++) {
      args.push(MonomPair(simplifiedArgs[i], _factors[i].power));
    }

    std::sort(args.begin(), args.end());
    // std::sort(args.begin(), args.end(), 
    //     []( const MonomPair& lhs, const MonomPair& rhs) 
    //     { return lhs.term < rhs.term; });

    auto offs = 0;
    auto coeff = Const(1);
    for (unsigned i = 0; i < nFactors(); i++) {
      auto& arg = args[i];
      auto c = arg.term.template tryNumeral<Number>();
      if (c.isSome()) {
        // arg is a number constant
        coeff = coeff * pow(c.unwrap(), arg.power);
      } else {
        // arg is a non-number term
        auto term  = arg.term;
        auto power = arg.power;
        while (i + 1 < nFactors() && args[i + 1].term == term) {
          power += args[i + 1].power;
          i++;
        }
        if (power != 0)
          args[offs++] = MonomPair(term, power);
      }
    }
    args.truncate(offs);
   
    return PolyPair(coeff, unique(Monom(std::move(args)))); 
  }

  static Monom one()
  { return Monom(); }

  bool isOne() const 
  { return _factors.begin() == _factors.end(); }

  friend std::ostream& operator<<(std::ostream& out, const Monom& self) 
  {
    out << "(";
    if (self._factors.size() == 0) {
      out << "Monom()";
    } else {
      auto iter  = self._factors.begin();
      out << *iter;
      iter++;
      for (; iter != self._factors.end(); iter++) {
        out << " " << *iter;
      }
    }
    out << ")";
    return out;
  }


  friend bool operator==(const Monom& l, const Monom& r) {
    return l._factors == r._factors;
  }

  Monom& operator=(Monom&&) = default;
  Monom(Monom&&) = default;

  explicit Monom(const Monom&) = default;
  explicit Monom(Monom&) = default;

  friend class Kernel::Polynom<Number>;

  TermList toTerm(TermList* results)  const
  {
    CALL("Monom::toTerm()")

    if (_factors.size() == 0) {
      return Number::one();
    } else {

      auto powerTerm = [](TermList t, int pow) -> TermList {
        ASS(pow > 0)
        TermList out = t;
        for (int i = 1; i < pow; i++) {
          out = Number::mul(t,out);
        }
        return out;
      };

      TermList out = powerTerm(results[0], _factors[0].power);

      for (unsigned i = 1; i < nFactors(); i++) {
        out = Number::mul(out, powerTerm(results[i], _factors[i].power));
      }

      return out;
    }
  }

  Optional<Variable> tryVar() const 
  {
    using Opt = Optional<Variable>;
    if (nFactors() == 1 ) {

      return _factors[0].tryVar();
    } else {
      return  Opt();
    }
  }

  void integrity() const {
#if VDEBUG
    if (_factors.size() > 0) {
      auto iter = this->_factors.begin();
      auto last = iter++;
      while (iter != _factors.end()) {
        ASS_REP(last->term < iter->term, *this);
        last = iter++;
      }
    }
#endif
  }

  Monom replaceTerms(PolyNf* simplifiedTerms) const 
  {
    int offs = 0;
    Monom out;
    out._factors.reserve(nFactors());

    for (auto& pair : _factors) {
      out._factors.push(MonomPair(simplifiedTerms[offs++], pair.power));
    }

    return std::move(out);
  }


  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_factors)>::type, no_ref_t>>;
  ConstIter iter() const&
  { return iterTraits(getArrayishObjectIterator<no_ref_t>(_factors)); }

  // template<class NumTraits>
  // Optional<Polynom<NumTraits> tryPoly() 
  // { TODO }
};

template<class Number>
class Polynom 
{
  friend struct std::hash<Polynom>;

  using Coeff    = typename Number::ConstantType;
  using Monom    = Kernel::Monom<Number>;
  using PolyPair = Kernel::PolyPair<Number>;

  Stack<PolyPair> _summands;

public:
  USE_ALLOCATOR(Polynom)
  CLASS_NAME(Polynom)

  Polynom(Stack<PolyPair>&& summands) : _summands(summands.isEmpty() ? Stack<PolyPair>{PolyPair::zero()} : std::move(summands)) { }
  // Polynom() : Polynom(Stack<PolyPair>()) {}
  Polynom(Coeff coeff, UniqueShared<Monom> term) 
    : Polynom(coeff == Coeff(0)
        ? Stack<PolyPair>() 
        : Stack<PolyPair> {  PolyPair(coeff, term)  }) {  }

  static Polynom zero() 
  { return Polynom(Stack<PolyPair>{}); }

  Polynom(Coeff coeff, PolyNf term) : Polynom(coeff, unique(Monom(term))) {  }
  Polynom(PolyNf t) : Polynom(Coeff(1), t) {  }
  explicit Polynom(Coeff constant) : Polynom(constant, unique(Monom::one())) {}

  Optional<Coeff> toNumber() const& 
  { 
    if (isNumber()) {
      return Optional<Coeff>(unwrapNumber());
    } else {
      return Optional<Coeff>();
    }
  }


  bool isNumber() const& 
  { 
    return _summands.size() == 0  /* <- empty polynomial == 0 */
    || (_summands.size() == 1 && _summands[0].monom->nFactors() == 0);
  }

  Coeff unwrapNumber() const& 
  { ASS(isNumber()); return _summands.size() == 0 ? Coeff(0) : _summands[0].coeff; }


  friend bool operator==(const Polynom<Number>& lhs, const Polynom<Number>& rhs)
  { return std::tie(lhs._summands) == std::tie(rhs._summands); }

  struct CancelAdd {
    Polynom lhs;
    Polynom rhs;
  };

  static CancelAdd cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr) 
  {
    CALL("Polynom::cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr)")
    DEBUG("in:  ", oldl, " <> ", oldr)

    using CoeffVec = Stack<PolyPair>;
    // auto zero = Number::zeroC;
    auto itl = oldl._summands.begin();
    auto itr = oldr._summands.begin();
    auto endl = oldl._summands.end();
    auto endr = oldr._summands.end();

    auto safeMinus = [](Coeff l, Coeff r) 
    { 
      try {
        return Optional<Coeff>(l - r);
      } catch (MachineArithmeticException) 
      {
        return Optional<Coeff>();
      }
    };

    auto push = [](CoeffVec& vec, UniqueShared<Monom> m, Coeff c) 
    { vec.push(PolyPair(c, m)); };

    auto cmpPrecedence = [](Optional<Coeff> lOpt, Coeff r) 
    { 
      if (lOpt.isNone()) return false;
      auto l = lOpt.unwrap();
      return Coeff::comparePrecedence(l,r) == Comparison::LESS;
    };

    CoeffVec newl;
    CoeffVec newr;
    while(itl != endl && itr !=  endr) {
      auto cl = itl->coeff;
      auto cr = itr->coeff;
      const UniqueShared<Monom>& ml = itl->monom;
      const UniqueShared<Monom>& mr = itr->monom;
      if (ml == mr) {
        auto& m = ml;
        auto lMinusR = safeMinus(cl, cr);
        auto rMinusL = safeMinus(cr, cl);
        auto pushLeft  = [&]() { push(newl, m, lMinusR.unwrap()); };
        auto pushRight = [&]() { push(newr, m, rMinusL.unwrap()); };
        auto pushSmaller = [&] () {
          if (cmpPrecedence(rMinusL, lMinusR.unwrap())) {
            pushRight();
          } else {
            pushLeft();
          }
        };

        if (cl == cr) {
           // 10 x + ... ~~  10 x + ... ==> ... ~~ ... 
           // we remove the term
        } else if (cmpPrecedence(lMinusR, cl) 
                && cmpPrecedence(rMinusL, cr)) {

          pushSmaller();
        } else if (cmpPrecedence(lMinusR, cl) ) {
          // 10 x + ... ~~  8 x + ... ==> 2 x + ... ~~ ... 
          // ^^ cl          ^ cr          ^ lMinusR
          pushLeft();

        } else if (cmpPrecedence(rMinusL, cr)) {
          //   7 x + ... ~~  8 x + ... ==> ... ~~ 1 x + ... 
          //   ^ cl          ^ cr                 ^ rMinusL
          pushRight();
        } else {

          DEBUG("### not cancellable coeffs: ", cl, " ", cr, " (diffs: ", lMinusR, " and ", rMinusL, ")")
            /* TODO INCOMP */
          if (lMinusR.isSome() && rMinusL.isSome()){
            pushSmaller();
          } else if (lMinusR.isSome()) {
            pushLeft();
          } else if (rMinusL.isSome()) {
            pushRight();
          } else {
            push(newl, m, cl);
            push(newr, m, cr);
          }
        }
        itl++;
        itr++;
      } else if (ml < mr) {
        push(newl, ml, cl);
        itl++;
      } else {
        ASS(mr < ml)
        push(newr, mr, cr);
        itr++;
      }
    }
    for(; itl != endl; itl++) {
      push(newl, itl->monom, itl->coeff);
    }
    for(; itr != endr; itr++) {
      push(newr, itr->monom, itr->coeff);
    }
    auto outl = Polynom<Number>(std::move(newl));
    auto outr = Polynom<Number>(std::move(newr));
    DEBUG("out: ", outl, " <> ", outr)
    // return make_pair( std::move(outl), std::move(outr)); 
    return CancelAdd { 
      .lhs = std::move(outl), 
      .rhs = std::move(outr), 
    };
  }

  TermList toTerm() const;

  TermList toTerm(TermList* results) const
  {
    CALL("Polynom::toTerm()")

    auto pairToTerm = [](PolyPair const& pair, TermList* t) -> TermList {
      auto c = TermList(theory->representConstant(pair.coeff));
      if (pair.monom->isOne()) {
        return c;
      } else {
        auto mon = pair.monom->toTerm(t);
        if (pair.coeff == Number::oneC) {
          return mon;
        } else if (pair.coeff == Number::constant(-1)) {
          return Number::minus(mon);
        } else {
          return Number::mul(c, mon);
        }
      }
    };

    if (_summands.size() == 0) {
      return Number::zero();
    } else {

      TermList out = pairToTerm(_summands[0], results);
      auto flatIdx = _summands[0].monom->nFactors();

      for (unsigned i = 1; i < nSummands(); i++) {
        auto& pair = _summands[i];
        out = Number::add(pairToTerm(pair, &results[flatIdx]), out);
        flatIdx += pair.monom->nFactors();
      }
      return out;
    }
  }

public:

  Polynom flipSign() const
  { 
    CALL("Polynom::flipSign() const") 
    Polynom out(*this);
    for (unsigned i = 0; i < nSummands(); i++) {
      out._summands[i].coeff = out._summands[i].coeff * Coeff(-1);
    }
    return std::move(out);
  }


  Polynom simplify(PolyNf* simplifiedArgs) const
  { 
    CALL("Polynom::simplify(PolyNf* simplifiedArgs) const") 
    try {

      // first we simplify all the monoms containted in this polynom
      Stack<PolyPair> out;
      {
        auto offs = 0;
        for (unsigned i = 0; i < nSummands(); i++) {
          auto pair  = _summands[i];
          auto simpl = pair.monom->simplify(&simplifiedArgs[offs]);
          auto coeff = pair.coeff * simpl.coeff;
          if (coeff == Number::zeroC) {
            /* we don't add it */

          // } else if (
          //        coeff == Coeff(-1) // TODO lift this
          //     && simpl.monom->isPolynom()) {
          //   // pushing in unary minus:
          //   //   Poly((-1) * Poly(t1 + t2 + t3 + ...) )
          //   auto& poly = *simpl.monom->asPolynom();
          //   out.reserve(out.size() + poly.nSummands()  - 1);
          //   for (unsigned j = 0; j < poly.nSummands(); j++) {
          //     auto& pair = poly._summands[j];
          //     out.push(PolyPair(coeff * pair.coeff, pair.monom));
          //   }
          } else {
            out.push(PolyPair(coeff, simpl.monom));
          }
          offs += pair.monom->nFactors();
        }
      }

      // then we sort them by their monom, in order to add up the coefficients efficiently
      std::sort(out.begin(), out.end());
      // std::sort(out.begin(), out.end(), 
      //     []( const PolyPair& lhs, const PolyPair& rhs) { return std::less<UniqueShared<Monom>>{}(lhs.monom, rhs.monom); });

      // add up the coefficient (in place)
      {
        auto offs = 0;
        for (unsigned i = 0; i < out.size(); i++) { 
          auto pair = out[i];
          auto coeff = pair.coeff;
          auto monom = pair.monom;
          while ( i + 1 < out.size() && out[i+1].monom == monom ) {
            coeff = coeff + out[i+1].coeff;
            i++;
          }
          if (coeff != Number::zeroC) 
            out[offs++] = PolyPair(coeff, monom);
        }
        out.truncate(offs);

      }

      return Polynom(std::move(out));
    } catch (ArithmeticException) { 
      return replaceTerms(simplifiedArgs);
    }
  }

  Polynom replaceTerms(PolyNf* simplifiedTerms) const 
  {
    int offs = 0;
    Stack<PolyPair> out;
    out.reserve(nSummands());

    for (auto& pair : _summands) {
      out.push(PolyPair(
            pair.coeff, 
            unique(pair.monom->replaceTerms(&simplifiedTerms[offs]))));
      offs += pair.monom->nFactors();
    }
    return Polynom(std::move(out));
  }


  unsigned nSummands() const
  { return _summands.size(); }

  unsigned nFactors(unsigned summand) const
  { return _summands[summand].monom->nFactors(); }

  PolyPair summandAt(unsigned summand) const
  { return _summands[summand]; }

  UniqueShared<Monom> monomAt(unsigned summand) const
  { return _summands[summand].monom; }

  void integrity() const {
#if VDEBUG
    if (_summands.size() > 0) {
      auto iter = this->_summands.begin();
      auto last = iter++;
      while (iter != _summands.end()) {
        ASS_REP(std::less<UniqueShared<Monom>>{}(last->monom, iter->monom), *this);
        iter->monom->integrity();
        last = iter++;
      }
    }
#endif
  }

  friend std::ostream& operator<<(std::ostream& out, const Polynom& self) {
    auto iter = self._summands.begin();
    out << "Poly(";
    if ( iter == self._summands.end() ) {
      out << "0";
    } else {
      out << *iter;
      iter++;
      for (; iter != self._summands.end(); iter++) {
        out << " + " << *iter;
      }
    }
    out << ")";
    return out;

  }


  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_summands)>::type, no_ref_t>>;
  ConstIter iter() const&
  { return iterTraits(getArrayishObjectIterator<no_ref_t>(_summands)); }

};


inline std::ostream& operator<<(std::ostream& out, const FuncTerm& self) 
{ 
  out << self._fun;
  auto& stack = self._args;
  auto iter = stack.iterFifo();

  if (iter.hasNext()) {
    out << "(" << iter.next();
    while (iter.hasNext()) {
      out << ", " << iter.next();
    }
    out << ")";
  }

  return out;
}

//TODO simplify this call in order to get rid of the unique(..) call
template<class Number> 
TermList Polynom<Number>::toTerm()  const
{ return PolyNf(AnyPoly(unique(Polynom(*this)))).toTerm(); }

POLYMORPHIC_FUNCTION(AnyPoly, simplify  , const& t, PolyNf* ts;) { return AnyPoly(unique(t->simplify(ts))); }

inline AnyPoly AnyPoly::simplify(PolyNf* ts) const
{ return apply(Polymorphic::simplify{ ts }); }


} // namespace Kernel


template<> struct std::less<Kernel::AnyPoly> 
{
  bool operator()(Kernel::AnyPoly const& lhs, Kernel::AnyPoly const& rhs) const 
  { return PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};


template<> struct std::hash<Kernel::AnyPoly> 
{
  size_t operator()(Kernel::AnyPoly const& self) const 
  { return std::hash<Kernel::AnyPolySuper>{}(self); }
};

template<class NumTraits>
struct std::hash<Kernel::Polynom<NumTraits>> 
{
  size_t operator()(Kernel::Polynom<NumTraits> const& x) const noexcept 
  {
    using namespace Lib;
    using namespace Kernel;

    unsigned out = HashUtils::combine(0,0);
    for (auto c : x._summands) {
      out = HashUtils::combine(
              stlHash(c.monom),
              stlHash(c.coeff),
              out);
    }
    return out;
  }
};


template<class NumTraits>
struct std::hash<Kernel::MonomPair<NumTraits>> 
{
  size_t operator()(Kernel::MonomPair<NumTraits> const& x) const noexcept 
  {
    using namespace Lib;
    using namespace Kernel;

    return HashUtils::combine(stlHash(x.term), stlHash(x.power));
  }
};

template<class NumTraits>
struct std::hash<Kernel::Monom<NumTraits>> 
{
  size_t operator()(Kernel::Monom<NumTraits> const& x) const noexcept 
  {
    using namespace Lib;
    using namespace Kernel;

    unsigned out = HashUtils::combine(84586,10);
    for (auto f : x._factors) {
      out = HashUtils::combine(stlHash(f), out);
    }
    return out;
  }
};

#endif // __POLYNOMIAL__H__

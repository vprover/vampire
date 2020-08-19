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

#define POLYMORPHIC_FUNCTION(type, Name, polyArg, constArgs) \
  namespace Polymorphic { \
    struct Name  \
    { \
      constArgs \
      template<class T> \
      type operator()(T polyArg); \
    }; \
  } \
  template<class T> type Polymorphic::Name::operator()(T polyArg) 


namespace Kernel {

/** newtype for wrapping varible ids */
class Variable 
{
  unsigned _num;
public: 
  explicit Variable(unsigned num) : _num(num) {}
  unsigned id() const { return _num; }
  friend bool operator==(Variable lhs, Variable rhs) 
  { return lhs._num == rhs._num; }

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
    return isInterpreted() ? interpretation()
                           : none<Theory::Interpretation>();
  }

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const
  { 
    using Const = typename Number::ConstantType;
    Const out;
    if (theory->tryInterpretConstant(_num, out)) {
      return out;
    } else {
      return Optional<Const>();
    }
  }
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
  { return std::tie(l.coeff, l.monom) < std::tie(r.coeff, r.monom); }

  friend bool operator==(PolyPair const& l, PolyPair const& r)
  { return std::tie(l.coeff, l.monom) == std::tie(r.coeff, r.monom); }

  friend bool operator!=(PolyPair const& l, PolyPair const& r)
  { return !(l == r); }

  friend std::ostream& operator<<(std::ostream& out, const PolyPair& self)
  { 
    if (self.coeff != Coeff(1)) {
      out << self.coeff;
    }
    return out << self.monom; 
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

  explicit AnyPoly(Poly< IntegerConstantType> x) : Coproduct(variant<0>(std::move(x))) {  }
  explicit AnyPoly(Poly<RationalConstantType> x) : Coproduct(variant<1>(std::move(x))) {  }
  explicit AnyPoly(Poly<    RealConstantType> x) : Coproduct(variant<2>(std::move(x)))  {  }

  template<class Number> 
  Polynom<Number> const& downcast() const& { return *as<UniqueShared<Polynom<Number>>>(); }

  unsigned nSummands() const { return collapsePoly<unsigned>(Polymorphic::nSummands{}); }
  unsigned nFactors(unsigned i) const { return collapsePoly<unsigned>(Polymorphic::nFactors{i}); }
  const PolyNf& termAt(unsigned summand, unsigned factor) {  return collapsePoly<PolyNf const&>(Polymorphic::termAt{summand, factor}); }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self) {
    if (self.is<0>()) return out << self.unwrap<0>();
    if (self.is<1>()) return out << self.unwrap<1>();
    if (self.is<2>()) return out << self.unwrap<2>();
    ASSERTION_VIOLATION
  }


  friend struct std::hash<AnyPoly>;

  TermList toTerm(TermList* results) const
  { return collapsePoly<TermList>(Polymorphic::toTerm{results}); }

  AnyPoly simplify(PolyNf* simplifiedArgs) const;

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const&
  { 
    return collapsePoly<Optional<typename Number::ConstantType>>(PolymorphicToNumeral<Number>{});
    // using Const = typename Number::ConstantType;
    // using ConstPoly = UniqueShared<Polynom<Number>;
    // if (isType<ConstPoly>()) {
    //   return self.as<ConstPoly>().tryNumeral();
    // } else {
    //   return Optional<Const>();
    // }
    // return match<Optional<Const>>(
    //     [](UniqueShared<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
    //     [](Variable               t) { return Optional<Const>();              },
    //     [](AnyPoly                t) { return t.template tryNumeral<Number>(); }
    //   );
  }
};

template<class K, class V, class Compare = std::less<K>> using map  = std::map<K, V, Compare, STLAllocator<std::pair<const K, V > > >;

/** Merges two map-like vectors into a new map-like vector. 
 * A vector is map-like if has key-value pairs as entry, is sorted by keys and each key is unique within the vector.
 *
 * If there is a key present in both lhs and rhs, the corresponding the two corresponding values will be combined 
 * with the closure @b add. After that the result of combining is then used as argument for @b filter() and will 
 * be discarded if filter returns false.
 */
template<class A, class Combine, class Filter, class Compare>
Stack<A> merge_sort_with(const Stack<A>& lhs, const Stack<A>& rhs, Combine combine, Filter filter, Compare cmp) 
{
    CALL("merge_sort_with()")

    /* is needed at least */
    Stack<A> out(max(lhs.size(), rhs.size()));

    auto l = lhs.begin();
    auto r = rhs.begin();
    auto insert = [&](const A& value) {
      ASS(filter(value));
      out.push(value);
    };
    while (l != lhs.end() && r != rhs.end() ) {
      if (cmp(*l, *r)) {
        insert(*l);
        l++;
      } else if (cmp(*r, *l)) {
        insert(*r);
        r++;
      } else {
        // equal. must be added up
        auto sum = combine(*l, *r);
        if (filter(sum))
          insert(sum);
        l++;
        r++;
      }
      if (out.size() >= 2) {
        ASS(cmp(out[out.size() - 2], out[out.size() - 1]))
      }
    }
    while (l != lhs.end()) {
      insert(*l);
      l++;
    }
    while (r != rhs.end()) {
      insert(*r);
      r++;
    }
    ASS(l == lhs.end() && r == rhs.end());
    return std::move(out);
}

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
  static PolyNf normalize(TermList t);

  friend bool operator==(PolyNf const& lhs, PolyNf const& rhs) 
  { return static_cast<Coproduct const&>(lhs) == static_cast<Coproduct const&>(rhs); }

  friend bool operator!=(PolyNf const& lhs, PolyNf const& rhs) 
  { return !(lhs == rhs); }

  friend struct std::hash<PolyNf>;

  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self)
  { 
    self.match<void>(
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
      { return orig.template match<TermList>(
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
    return match<Optional<Const>>(
        [](UniqueShared<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
        [](Variable               t) { return Optional<Const>();              },
        [](AnyPoly                t) { return t.template tryNumeral<Number>(); }
      );
  }

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
  { return std::tie(l.power, l.term) < std::tie(r.power, r.term); }

  friend bool operator==(MonomPair const& l, MonomPair const& r)
  { return std::tie(l.power, l.term) == std::tie(r.power, r.term); }

  friend bool operator!=(MonomPair const& l, MonomPair const& r)
  { return !(l == r); }

  friend std::ostream& operator<<(std::ostream& out, const MonomPair& self) {
    out << self.term; 
    if (self.power != 1) 
      out << "^" << self.power;
    return out;
  }


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

  PolyNf const& termAt(unsigned i) const
  { return _factors[i].term; }

  bool isPolynom() const
  { return nFactors() == 1 
      && _factors[0].power == 1 
      && _factors[0].term.template isType<AnyPoly>(); }

  UniqueShared<Polynom> asPolynom() const
  { 
    ASS(isPolynom());
    return _factors[0].term
      .template as<AnyPoly>()
      .template as<UniqueShared<Polynom>>(); 
  }

            // && simpl.monom->nFactors() == 1 
            // && simpl.monom->_factors[0].template isType<AnyPoly>()

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

    std::sort(args.begin(), args.end(), 
        []( const MonomPair& lhs, const MonomPair& rhs) 
        { return lhs.term < rhs.term; });

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
      out << "1";
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

  public:

  Monom& operator=(Monom&&) = default;
  Monom(Monom&&) = default;

  static Monom monomMul(const Monom& lhs, const Monom& rhs);

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

};

template<class Number>
inline Monom<Number> Monom<Number>::monomMul(const Monom<Number>& lhs, const Monom<Number>& rhs) 
{
  return Monom(merge_sort_with(lhs._factors,rhs._factors,
        [](MonomPair const& l, MonomPair const& r)  -> MonomPair
        { 
          ASS_EQ(l.term, r.term); 
          return MonomPair(l.term, l.power + r.power);
        },
        [](MonomPair const& l) { return l.power != 0; },
        [](MonomPair const& l, MonomPair const& r) { return l.term < r.term; }
      ));
}

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

  Polynom(Stack<PolyPair>&& summands) : _summands(std::move(summands)) { }
  Polynom() : Polynom(Stack<PolyPair>()) {}
  Polynom(Coeff coeff, UniqueShared<Monom> term) 
    : Polynom(coeff == Coeff(0)
        ? Stack<PolyPair>() 
        : Stack<PolyPair> {  PolyPair(coeff, term)  }) {  }

  Polynom(Coeff coeff, PolyNf term) : Polynom(coeff, unique(Monom(term))) {  }
  Polynom(PolyNf t) : Polynom(Coeff(1), t) {  }
  explicit Polynom(Coeff constant) : Polynom(constant, unique(Monom::one())) {}

  Optional<Coeff> toNumber() const& 
  { 
    if (isNumber()) {
      return unwrapNumber();
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

  static Polynom<Number> polyAdd(const Polynom<Number>& lhs, const Polynom<Number>& rhs);

  static Polynom<Number> polyMul(const Polynom<Number>& lhs, const Polynom<Number>& rhs) 
  {

    CALL("Polynom::polyMul");
    DEBUG("lhs: ", lhs);
    DEBUG("rhs: ", rhs);
    lhs.integrity();
    rhs.integrity();

    //TODO use Map instead
    map<UniqueShared<Monom>, Coeff> prods;

    for (auto& l : lhs._summands) {
      for (auto& r : rhs._summands) {
        auto monom = unique(Monom::monomMul( l.monom, r.monom));
        auto coeff = l.coeff * r.coeff;
        auto res = prods.emplace(make_pair(std::move(monom), coeff));
        if (!res.second) {
          auto& iter = res.first;
          ASS(iter != prods.end());
          iter->second = iter->second + coeff;
        }
      }
    }

    Polynom<Number> out;
    out._summands.reserve(prods.size());
    for (auto iter = prods.begin(); iter != prods.end(); iter++) {
      auto coeff = iter->second;
      if (coeff != Number::zeroC) {
        out._summands.pushMv(PolyPair(coeff, iter->first)); 
      }
    }
    //TODO use stack instead of vector
    std::sort(out._summands.begin(), out._summands.end(), 
        []( const PolyPair& lhs, const PolyPair& rhs) { return std::less<UniqueShared<Monom>>{}(lhs.monom, rhs.monom); });
    out.integrity();
    DEBUG("out: ", out);
    return out;
  }

  static std::pair<Polynom, Polynom> cancel(Polynom<Number> const& oldl, Polynom<Number> const& oldr) 
  {
    CALL("Polynom::cancel(Polynom<Number> const& oldl, Polynom<Number> const& oldr)")
    DEBUG("in:  ", oldl, " <> ", oldr)

    using CoeffVec = Stack<PolyPair>;
    auto zero = Number::zeroC;
    auto itl = oldl._summands.begin();
    auto itr = oldr._summands.begin();
    auto endl = oldl._summands.end();
    auto endr = oldr._summands.end();
    auto push = [](CoeffVec& vec, const Monom& m, Coeff c) 
    { vec.pushMv(PolyPair(c, unique(Monom(m)))); };

    CoeffVec newl;
    CoeffVec newr;
    while(itl != endl && itr !=  endr) {
      auto cl = itl->coeff;
      auto cr = itr->coeff;
      const UniqueShared<Monom>& ml = itl->monom;
      const UniqueShared<Monom>& mr = itr->monom;
      if (ml == mr) {
        auto& m = ml;
        ASS_NEQ(cl, zero);
        ASS_NEQ(cr, zero);
        if (cl == cr) {
          // 10 x + ... ~~  10 x + ... ==> ... ~~ ... 
        } else if (cl > zero && cr > zero) {
          // 10 x + ... ~~  8 x + ... ==> 2 x + ... ~~ ... 
          if  ( cl > cr ) {
            push(newl, m, cl - cr);
          } else {
            push(newr, m, cr - cl);
          }
        } else if (cl < zero && cr < zero) {
          // -10 x + ... ~~  -8 x + ... ==> -2 x + ... ~~ ... 
          if  ( cl < cr ) {
            push(newl, m, cl - cr);
          } else {
            push(newr, m, cr - cl);
          }
        } else {
          if (cl < zero) {
            // -10 x + ... ~~  8 x + ... ==> ... ~~ 18 x + ... 
            push(newr, m, cr - cl);
          } else {
            //  10 x + ... ~~ -8 x + ... ==> 18 x + ... ~~ ... 
            push(newl, m, cl - cr);
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
    return make_pair( std::move(outl), std::move(outr)); 
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
        } else if (
               coeff == Coeff(-1) // TODO lift this
            && simpl.monom->isPolynom()) {
          // pushing in unary minus:
          //   Poly((-1) * Poly(t1 + t2 + t3 + ...) )
          auto& poly = *simpl.monom->asPolynom();
          out.reserve(out.size() + poly.nSummands()  - 1);
          for (unsigned j = 0; j < poly.nSummands(); j++) {
            auto& pair = poly._summands[j];
            out.push(PolyPair(coeff * pair.coeff, pair.monom));
          }
        } else {
          out.push(PolyPair(coeff, simpl.monom));
        }
        offs += pair.monom->nFactors();
      }
    }

    // then we sort them by their monom, in order to add up the coefficients efficiently
    std::sort(out.begin(), out.end(), 
        []( const PolyPair& lhs, const PolyPair& rhs) { return std::less<UniqueShared<Monom>>{}(lhs.monom, rhs.monom); });

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
  }

  unsigned nSummands() const
  { return _summands.size(); }

  unsigned nFactors(unsigned summand) const
  { return _summands[summand].monom->nFactors(); }

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

};


inline std::ostream& operator<<(std::ostream& out, const FuncTerm& self) 
{ 
  out << self._fun;
  auto& stack = self._args;
  Stack<PolyNf>::ConstIterator iter(stack);

  if (iter.hasNext()) {
    out << "(" << iter.next();
    while (iter.hasNext()) {
      out << ", " << iter.next();
    }
    out << ")";
  }

  return out;
}


template<class Number>
Polynom<Number> Polynom<Number>::polyAdd(const Polynom<Number>& lhs, const Polynom<Number>& rhs) 
{
  CALL("Polynom::polyAdd")
  lhs.integrity();
  rhs.integrity();
  auto newCoeffs = merge_sort_with(lhs._summands, rhs._summands, 
      /* combine */
      [](PolyPair const& l, PolyPair const& r)
      { ASS_EQ(l.monom, r.monom); return PolyPair( l.coeff + r.coeff, l.monom ); },

      /* filter */
      [](PolyPair const& x)
      { return x.coeff != Number::zeroC; },

      /* compare */
      [](PolyPair const& l, PolyPair const& r){ return l.monom < r.monom; }
    );
  if (newCoeffs.isEmpty())  {
    return Polynom(Coeff(0));
  } else {
    return Polynom<Number>(std::move(newCoeffs));
  }
}


//TODO simplify this call in order to get rid of the unique(..) call
template<class Number> 
TermList Polynom<Number>::toTerm()  const
{ return PolyNf(AnyPoly(unique(Polynom(*this)))).toTerm(); }

POLYMORPHIC_FUNCTION(AnyPoly, simplify  , const& t, PolyNf* ts;) { return AnyPoly(unique(t->simplify(ts))); }

inline AnyPoly AnyPoly::simplify(PolyNf* ts) const
{ return collapsePoly<AnyPoly>(Polymorphic::simplify{ ts }); }


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

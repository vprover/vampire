/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html and in the source directory
 */

#ifndef __POLYNOMIAL__H__
#define __POLYNOMIAL__H__

/**
 * @file Kernel/Polynomial.hpp
 * This file mainly provides POLYnomial Normal Forms for terms PolyNf. In this normal form a term is defined as follows:
 *
 * PolyNf ::= FuncId [PolyNf]  // a normal function term
 *          | Variable         // a normal variable
 *          | AnyPoly          // a dynamically typed polynom
 *
 * AnyPoly ::= Polynom<IntTraits > 
 *           | Polynom<RatTraits >
 *           | Polynom<RealTraits>
 *
 * Polynom<Number> ::= [Monom<Number>]              // a sorted list of monoms
 * Monom<Number>   ::= Number [MonomFactor<Number>] // a numeral as factor, and a sorted list of other factors
 * MonomFactor     ::= PolyNf int                   // the term of the factor, and its power
 */

#include "Lib/Reflection.hpp"
#include "Lib/STLAllocator.hpp"
#include "Kernel/NumTraits.hpp"
#include <cassert>
#include "Lib/Coproduct.hpp"
#include "Lib/Option.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include <type_traits>
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TypedTermList.hpp"
#include "Lib/Metaiterators.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
#define OUTPUT_NICE 1

#define POLYNF_NICE_OUTPUT 1
#if VDEBUG
#define POLYNF_INTEGRITY_CHECKS 1
#else 
#define POLYNF_INTEGRITY_CHECKS 0
#endif
namespace Kernel {


/**
 * iterator over all terms t{i} in  a term (t1 + (t2 + (t3 + ... + t{n} ...)))
 * where t{n} are variables or terms with a function symbol different from +
 * the AC operation + can be passed as a constructor argument.
 */
class AcChainIter  {
  unsigned _functor;
  Option<TermList> _current;
public:
  AcChainIter(TermList current, unsigned functor)
    : _functor(functor)
    , _current(current) {}

  DECL_ELEMENT_TYPE(TermList);
  auto next() {
    auto out = _current.take().unwrap();
    if (out.isTerm() && out.term()->functor() == _functor)  {
      ASS_EQ(out.term()->numTermArguments(), 2);
      _current = some(out.term()->termArg(1));
      return out.term()->termArg(0);
    } else {
      return out;
    }
  }

  bool hasNext() {
    return _current.isSome();
  }
};

// TODO use this newtype in Term.hpp
/** newtype for wrapping varible ids */
class Variable 
{
  unsigned _num;
  TermList _sort;

public: 
  MAKE_DERIVABLE(Variable, _num)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  Variable();
  explicit Variable(unsigned num, TermList sort);
  unsigned id() const;

  TermList sort() const { return _sort; }

  void integrity() const {  }
  friend struct std::hash<Variable>;
  friend std::ostream& operator<<(std::ostream& out, const Variable& self);
  TermList denormalize() const { return TermList::var(_num); }
};

// TODO use this newtype in Term.hpp
/** newtype for wrapping function ids (also often called functors in vampire) */
class FuncId 
{
  unsigned _num;
  const TermList* _typeArgs; // private field not used
  
  explicit FuncId(unsigned num, const TermList* typeArgs);
public: 
  MAKE_DERIVABLE(FuncId, _num, _typeArgs)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  static FuncId symbolOf(Term* term);
  unsigned numTermArguments() const;
  unsigned numTypeArguments() const;
  TermList typeArg(unsigned i) const;

  auto iterTypeArgs() const
  { return range(0, numTypeArguments()).map([this](auto i) { return typeArg(i); }); }

  friend std::ostream& operator<<(std::ostream& out, const FuncId& self);

  Signature::Symbol* symbol() const;

  unsigned id() const;
  Theory::Interpretation interpretation() const;
  bool isInterpreted() const;
  Option<Theory::Interpretation> tryInterpret() const;

  template<class Number>
  Option<typename Number::ConstantType> tryNumeral() const;
};

} // namespace Kernel




/////////////////////////////////////////////////////////////////////////////////////////////
// forward declarations, needed to define PolyNf structure
/////////////////////////////////////////////////////////

namespace Kernel {

class PolyNf;
template<class Number> class Polynom;
template<class Number> class MonomFactors;
class AnyPoly;

////////////////////////////////////////////////////////////////////////////////////////////////////
// class declartions for PolyNf
/////////////////////////////////////////////////////////

struct ImmediateSubterms;

/** 
 * Represents a factor in a monom. Each unique term contained in the monom is stored 
 * together with the number of occurences of the term within that monom.
 *
 * e.g. a term like (x * x * a * x) is represented as 
 * MonomFactors { MonomFactor(x, 3), MonomFactor(a, 1) }
 */
template<class Number> 
class MonomFactor 
{
  TermList _term;
  int _power;
public:

  using Numeral = typename Number::ConstantType;
  CLASS_NAME(MonomFactor)
  MAKE_DERIVABLE(MonomFactor, _term, _power)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  friend struct ImmediateSubterms;
  template<class N>
  friend std::ostream& operator<<(std::ostream& out, MonomFactor<N> const& self);

  MonomFactor(PolyNf term, int power);

   
  /** if this monomfactor is a Variable and has power one it is turned into a variable */
  Option<Variable> tryVar() const;

  MonomFactor replaceTerm(PolyNf const& t) const
  { return MonomFactor(t, _power); }

  static MonomFactor fromNormalized(TermList);
  TermList denormalize() const;

  PolyNf term() const;

  int power() const 
  { return _power; }

  void integrity() const 
  { 
#if POLYNF_INTEGRITY_CHECKS
    term().integrity(); 
#endif
  }
  // Option<Polynom<Number>> tryPolynom() const;
  // bool isPolynom() const { return tryPolynom().isSome(); }
  //
  // PolyNf::SubtermIter iterSubterms() const;
};

template<class Add, class Zero, class Iter>
TermList denormalizeAndNormalizedFromIterator(Add add, Zero zero, Iter iter)
{
  return normalizedFromIterator(add, zero, 
      iterTraits(iter)
        .map([](auto a){ return a.denormalize(); }));
}

template<class Add, class Zero, class Iter>
TermList normalizedFromIterator(Add add, Zero zero, Iter iter)
{
  // TODO check whether the iterator is reverable (?)
  auto ts = Stack<TermList>::fromIterator(iter);
  auto rev = range(0, ts.size()).map([&](auto i) { return ts[ts.size() - 1 - i]; });
  if (!rev.hasNext()) {
    return zero();
  } else {
    auto out = rev.next();
    while (rev.hasNext()) {
      out = add(rev.next(), out);
    }
    return out;
  }
}

/** 
 * Represents the non-numeral part of a monom. this means it is a sorted list of MonomFactor s.
 */
template<class Number>
class MonomFactors 
{
  using MonomFactor = Kernel::MonomFactor<Number>;
  using Polynom     = Kernel::Polynom<Number>;
  using Numeral = typename Number::ConstantType;

  TermList _inner;

public:
  CLASS_NAME(MonomFactors)
  USE_ALLOCATOR(MonomFactors)
  MAKE_DERIVABLE(MonomFactors, _inner)
    DERIVE_EQ
    DERIVE_CMP
    // DERIVE_CMP_OPERATORS_FROM_LESS
    DERIVE_HASH

  // friend bool operator<(MonomFactors const& l, MonomFactors const& r)
  // {
  //   if (l == r) return false;
  //   auto li = l.iter();
  //   auto ri = l.iter();
  //   auto le = li.tryNext();
  //   auto re = ri.tryNext();
  //   while (le.isSome() && re.isSome()) {
  //     if (le.unwrap() < re.unwrap()) {
  //       return true;
  //     } else if (re.unwrap() < le.unwrap()) {
  //       return false;
  //     }
  //     ASS_EQ(le,re)
  //     le = li.tryNext();
  //     re = ri.tryNext();
  //   }
  //   if (le.isSome()) return false;
  //   if (re.isSome()) return true;
  //   ASS_EQ(l, r)
  //   return false;
  // }

  friend struct ImmediateSubterms;

  /** 
   * constructs a new MonomFactors. 
   * \pre factors must be sorted
   */
  MonomFactors(Stack<MonomFactor> const& factors);
  MonomFactors(MonomFactor const& f) : MonomFactors(Stack<MonomFactor>{f}) {}

  // \pre iter must be sorted
  template<class Iter>
  static MonomFactors fromIterator(Iter iter)
  { return MonomFactors::fromNormalized(
      denormalizeAndNormalizedFromIterator(Number::mul, Number::one, iter)); }


  MonomFactors(TermList factors);

  /** constructs an empty product, which corresponds to the numeral one.  */
  MonomFactors();

  /** constructs a singleton product */
  MonomFactors(PolyNf t);

  /** constructs the product of t1 and t2. There is no precondigion on the ordering of t1 and t2. */
  MonomFactors(PolyNf t1, PolyNf t2);

  /** returns the number of factors */
  unsigned cntFactors() const;

  /** returns the nth factor */
  MonomFactor      & factorAt(unsigned i);

  /** returns the nth factor */
  MonomFactor const& factorAt(unsigned i) const;

  /** returns the number of factors */
  PolyNf const& termAt(unsigned i) const;

  /** returns the (empty) product one */
  static MonomFactors one();

  /** returns whether this is an empty product */
  bool isOne() const;


  // Option<MonomFactor> asSingleFactor() const 
  // {
  //   auto iter = iter();
  //   if (!iter.hasNext()) {
  //     return none<MonomFactor>();
  //   } else {
  //       auto out = iter.tryNext();
  //       if (iter.hasNext()) {
  //         return none<MonomFactor>();
  //       } else {
  //         return out;
  //       }
  //   }
  // }
  /** if this MonomFactors consist of a single variable if will be returnd  */
  Option<MonomFactor> tryMonomFactor() const;
  /** if this MonomFactors consist of a single variable if will be returnd  */
  Option<Variable> tryVar() const;

  /** performs an integrity check on the datastructure, only has an effect in debug mode */
  void integrity() const;

  MonomFactors replaceTerms(PolyNf* simplifiedTerms, unsigned& cnt) const;

  /** replaces all the factors, by new ones, keeping the power of each term the same  */
  MonomFactors replaceTerms(PolyNf* simplifiedTerms) const
  { unsigned cnt; return replaceTerms(simplifiedTerms, cnt); }

  /** returns an iterator over all factors */
  // auto iter() const -> IterTraits<VirtualIterator<MonomFactor>>;
  // { return iterTraits(_factors.iter()); }

  struct Iter {
    Option<TermList> _rest;
  public:
    Iter(TermList self) 
      : _rest(some(self))
    {}

    DECL_ELEMENT_TYPE(MonomFactor);

    bool hasNext() const
    { return  _rest.isSome(); }

    OWN_ELEMENT_TYPE next() 
    {
      ASS(_rest.isSome())
      TermList t = _rest.take().unwrap();
      if (!theory->isInterpretedFunction(t, Number::mulI)) {
        // singleton monom t^1
        return MonomFactor::fromNormalized(t);
      } else {
        // multiplication lhs * rhs
        TermList lhs = t.term()->termArg(0);
        TermList rhs = t.term()->termArg(1);
        if (theory->isInterpretedFunction(lhs, Number::mulI)) {
          // (( x * x * ... ) * rhs)
          //  ^^^^^^^^^^^^^^^ <- lhs
          _rest = some(rhs);
          return MonomFactor::fromNormalized(lhs);
        } else if (rhs == lhs 
            // t = (lhs * lhs)
            || (theory->isInterpretedFunction(rhs, Number::mulI) && lhs == rhs.term()->termArg(0))) {
            // t = (lhs * ( lhs * ... ))
          return MonomFactor::fromNormalized(t);
        } else {
          // (lhs * rhs)
          _rest = some(rhs);
          return MonomFactor::fromNormalized(lhs);
        }
      }
    }
  };
  
  // auto iterSubterms() const
  // { return concatIters(
  //     getSingletonIterator(PolyNf(*this)),
  //     ImmediateSubterms{}(*this).flatMap([](auto t) { return t.iterSubterms(); })
  //   ); 
  // }

  auto iter() const 
  { return iterTraits(Iter(this->_inner)); }

  template<class N> friend std::ostream& operator<<(std::ostream& out, const MonomFactors<N>& self);

  TermList denormalize() const;
  Stack<MonomFactor>& raw();
  static MonomFactors fromNormalized(TermList);
};


/** 
 * Represents a summand in a polynom of the number type Number 
 * e.g. a term like 3 * (a*x) would be represented as 
 * Monom { 3, MonomFactors { a, x }}
 */
template<class Number> 
struct Monom 
{
  using Numeral = typename Number::ConstantType;

  Numeral numeral;
  MonomFactors<Number> factors;

  CLASS_NAME(Monom)
  USE_ALLOCATOR(Monom)
  MAKE_DERIVABLE(Monom, factors, numeral)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  friend struct ImmediateSubterms;

  Monom(Numeral numeral, MonomFactors<Number> factors);
  Monom(MonomFactors<Number> factors) : Monom(Numeral(1), std::move(factors)) {}

  static Monom zero();

  Option<Variable> tryVar() const;

  /** performs an integrity check on the datastructure, only has an effect in debug mode */
  void integrity() const;

  static Monom fromNormalized(TermList);
  TermList denormalize() const;

  friend Monom operator*(Numeral k, Monom const& self)
  { return Monom(self.numeral * k, MonomFactors<Number>(self.factors)); }

  friend Monom operator/(Monom const& self, Numeral k)
  { 
    ASS_NEQ(k, Numeral(0))
    return (Numeral(1) / k) * self;
  }

  friend Monom operator-(Monom const& self)
  { return Numeral(-1) * self; }

  Monom replaceTerms(PolyNf* toReplace, unsigned& cnt) 
  { return Monom(numeral, factors.replaceTerms(toReplace, cnt)); }

};


/**
 * Represents an ordenary complex term, in the PolyNF term tree.
 */
class FuncTerm 
{
  friend class PolyNf;
  template<class NumTraits>
  friend class MonomFactor;
  Term* _self;
  FuncTerm(Term* t);
public:
  CLASS_NAME(FuncTerm)
  USE_ALLOCATOR(FuncTerm)
  MAKE_DERIVABLE(FuncTerm, _self)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  friend struct ImmediateSubterms;

  // FuncTerm(FuncId f, Stack<PolyNf>&& args);
  FuncTerm(FuncId f, PolyNf* args);

  unsigned numTermArguments() const;
  FuncId function() const;
  PolyNf arg(unsigned i) const;

  TermList sort() const 
  { return SortHelper::getResultSort(_self); }

  template<class Number> 
  Option<typename Number::ConstantType> tryNumeral() const;
  static FuncTerm fromNormalized(Term* t) { return FuncTerm(t); }
  friend std::ostream& operator<<(std::ostream& out, const FuncTerm& self);
  TermList denormalize() const { return TermList(_self); }
  void integrity() const;
};

template<class N> bool operator!=(const MonomFactors<N>& l, const MonomFactors<N>& r) { return !(l == r); }

template<class Number>
class Polynom 
{
  friend struct std::hash<Polynom>;

  using Numeral      = typename Number::ConstantType;
  using MonomFactors = Kernel::MonomFactors<Number>;
  using Monom        = Kernel::Monom<Number>;

  TermList _inner;
  explicit Polynom(TermList inner) : _inner(inner) { integrity(); }

public:
  USE_ALLOCATOR(Polynom)
  CLASS_NAME(Polynom)
  MAKE_DERIVABLE(Polynom, _inner)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  friend struct ImmediateSubterms;

  /** 
   * constructs a new Polynom with a list of summands 
   * \pre summands must be sorted
   */
  // TODO get rid of this?
  explicit Polynom(Stack<Monom> const& summands) 
        : Polynom(Polynom::fromIterator(summands.iterFifo())) 
  {}

  Polynom(Polynom const& summands)  = default;

  TermList sort() const { return Number::sort(); }

  template<class Iter>
  static Polynom fromIterator(Iter iter)
  { return Polynom::fromNormalized(
      denormalizeAndNormalizedFromIterator(Number::add, Number::zero, iter)); }

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(Monom m);

  /** creates a Polynom that consists of only one summand, that is a product of numeral, and term */
  explicit Polynom(Numeral numeral, PolyNf term);

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(PolyNf t);

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(Numeral constant);

  /** creates the empty Polynom that is interpreted as zero */
  static Polynom zero();

  /** if this Polynom consists only of one summand that is a numeral the numeral is returned */
  Option<Numeral> toNumber() const&;

  /** turns this Polynom into a numeral if it consists only of one summand that is a numeral, or throws an assertion violation 
   * \pre isNumeral is true*
   */
  Numeral unwrapNumber() const&;

  /** returns whether this Monom consists of only one summand that is a numeral */
  bool isNumber() const&;

  /** turns this polynom into a term */
  TermList denormalize() const 
  { return _inner; }

  Option<Monom> asMonom() const 
  {
    auto iter = iterSummands();
    if (!iter.hasNext()) {
      return none<Monom>();
    } else {
        auto out = iter.tryNext();
        if (iter.hasNext()) {
          return none<Monom>();
        } else {
          return out;
        }
    }
  }

  /**
   * replaces all subterms of this poly, by given array of subterms. the resulting polynom will be sorted correctly. 
   * here a monom does not count as a subterm, but all the subterms of the monom themselves do:
   *      Polynom(Monom(3, { f(x), y }), Monom(1, { z }))
   *         .replaceTerms({a,b,c})
   * ===> Polynom(Monom(3, { a   , b }), Monom(1, { c }))
   */
  Polynom replaceTerms(PolyNf* simplifiedTerms) const;

  unsigned cntSummands() const
  { return iterSummands().count(); }
  // /** returns the number of summands of this polynom */
  // unsigned nSummands() const;
  //
  // /** returns the number of factors of the summand with the given index */
  // unsigned nFactors(unsigned summand) const;
  //
  // /** returns the summand with the given index */
  // Monom const& summandAt(unsigned summand) const;
  //
  // /** returns the summand with the given index */
  // Monom      & summandAt(unsigned summand);

  Option<Monom> tryMonom() const;

  /** integrity check of the data structure. does noly have an effect in debug mode */
  void integrity() const;

  /** returns iterator over all summands of this Polyom */
  auto iterSummands() const 
  { return iterTraits(AcChainIter(_inner, Number::addF()))
        .map([](auto t) { return Monom::fromNormalized(t); }); }


  friend Polynom operator*(Numeral const& k, Polynom const& self)
  {
    return Polynom::fromIterator(
        self.iterSummands()
                .map([&](auto m) { return k * m; }));
  }

  friend Polynom operator/(Polynom const& self, Numeral const& k)
  { return (Numeral(1) / k) * self; }

  friend Polynom operator*(Polynom const& self, Numeral const& k)
  { return k * self; }

  friend Polynom operator-(Polynom const& self)
  { return Numeral(-1) * self; }

  static Option<Polynom> tryFromNormalized(TypedTermList t);
  static Polynom fromNormalized(TermList t)
  {
    // TODO assertnormalized
    ASS(t.isVar() || SortHelper::getResultSort(t.term()) == Number::sort());
    return Polynom(t);
  }


  template<class N> friend std::ostream& operator<<(std::ostream& out, const Polynom<N>& self);
}; 

class AnyPoly
{
  AnyPoly(Term* t);
  AnyPoly(Term const* t);
  Coproduct< 
      Polynom< IntTraits>
    , Polynom< RatTraits>
    , Polynom<RealTraits>
    > _self;
  friend class PolyNf;
public:
  CLASS_NAME(AnyPoly)
  USE_ALLOCATOR(AnyPoly)
  MAKE_DERIVABLE(AnyPoly, _self)
    DERIVE_EQ
    DERIVE_CMP
    DERIVE_HASH

  friend struct ImmediateSubterms;
  AnyPoly() = delete;
  AnyPoly(AnyPoly const&) = default;

  /** creates a new dynamically typed polynom from a statically typed one */
  template<class NumTraits> AnyPoly(Polynom<NumTraits> self) 
    : _self(std::move(self)) 
  {}

  TermList sort() const
  { return _self.apply([](auto& x) { return x.sort(); }); }

  /** tries to turn this polynom into a polynom of the given NumTraits. */
  template<class NumTraits> Option<Polynom<NumTraits> const&> downcast() const;
  template<class NumTraits> Option<Polynom<NumTraits>      &> downcast();

  /** returns wether this is a Polynom of the given NumTraits. */
  template<class NumTraits> bool isType() const;

  /** if this polynom has the right sort, and consist of a single summand that is a numeral, then this numeral
   * is returned. otherwise an empty Option is returned. */
  template<class NumTraits> Option<typename NumTraits::ConstantType> tryNumeral() const&;

  /** \see template<class N> Polynom<N>::replaceTerms */
  AnyPoly replaceTerms(PolyNf* newTs) const;

  template<class F> auto apply(F f) const { return _self.apply(std::move(f)); }
  template<class F> auto apply(F f)       { return _self.apply(std::move(f)); }

  // /** \see template<class N> Polynom<N>::nSummands */
  // unsigned nSummands() const;
  //
  // /** \see template<class N> Polynom<N>::nFactors */
  // unsigned nFactors(unsigned i) const;
  //
  // /** \see template<class N> Polynom<N>::termAt */
  // PolyNf const& termAt(unsigned summand, unsigned factor) const;

  TermList denormalize() const 
  { return _self.apply([](auto& x) { return x.denormalize(); }); }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self);

  static Option<AnyPoly> tryFromNormalized(TypedTermList t)
  { return tryNumTraits([&](auto numTraits) 
        { return Polynom<decltype(numTraits)>::tryFromNormalized(t)
                   .map([](auto x) { return AnyPoly(std::move(x)); }); }); }

  void integrity() { 
#if POLYNF_INTEGRITY_CHECKS
    return _self.apply([](auto& a) { return a.integrity(); }); 
#endif
  }
};


/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * See the file-level documentation for how this datatype is composed.
 */
class PolyNf 
{
  Coproduct<FuncTerm, Variable, AnyPoly> _self;
public:
  CLASS_NAME(PolyNf)
  MAKE_DERIVABLE(PolyNf, _self)
    DERIVE_HASH
    DERIVE_EQ
    DERIVE_CMP

  friend struct ImmediateSubterms;

  PolyNf(FuncTerm t);
  PolyNf(Variable t);
  PolyNf(AnyPoly  t);

  static PolyNf normalize(TypedTermList t, bool& evaluated);
  static PolyNf normalize(TypedTermList t) 
  { bool ev; return PolyNf::normalize(t, ev); }

  template<class FUnint, class FVar, class FPoly>
  auto match(FUnint unint, FVar var, FPoly poly) const
  { return _self.match(unint, var, poly); }

  Option<Variable> asVar() const { return _self.as<Variable>().toOwned(); }
  Option<FuncTerm> asFuncTerm() const { return _self.as<FuncTerm>().toOwned(); }
  Option<AnyPoly>  asPoly() const { return _self.as<AnyPoly>().toOwned(); }

  Variable unwrapVar() const { return asVar().unwrap(); }
  bool isVar() const { return asVar().isSome(); }

  /** 
   * If this term is a polynomial of sort NumTraits, it is downcasted to that sort,
   * otherwise an empty Option is returned
   */
  template<class NumTraits> Option<Polynom<NumTraits> const&> downcast() const;
  template<class NumTraits> Option<Polynom<NumTraits>      &> downcast();

  /** turns the normal form term PolyNf into an ordenary vampire term TermList. */
  TermList denormalize() const { return _self.apply([](auto& x) { return x.denormalize(); }); }

  /** 
   * Turns this PolyNf term into a typed polynom of sort Number.
   * this must have the same sort as Number. 
   * If this is already a polynom it will just be downcasted, 
   * otherwise (when it is a Variable, or a FuncTerm) it will be 
   * wrapped in a polynom.
   */
  template<class Number> 
  Polynom<Number> wrapPoly() const;

  TermList sort() const
  { return _self.apply([](auto& x) { return x.sort(); }); }

  Option<AnyPoly> wrapAnyPoly() const { 
    return sort() ==  IntTraits::sort() ? some(AnyPoly(wrapPoly< IntTraits>()))
         : sort() == RealTraits::sort() ? some(AnyPoly(wrapPoly<RealTraits>()))
         : sort() ==  RatTraits::sort() ? some(AnyPoly(wrapPoly< RatTraits>()))
         : none<AnyPoly>()
    ;
  }


  /** if this PolyNf is a numeral, the numeral is returned */
  template<class Number>
  Option<typename Number::ConstantType> tryNumeral() const;

  // TODO why do we have both tryVar and asVar
  /** if this PolyNf is a Variable, the variable is returned */
  Option<Variable> tryVar() const { return asVar(); }

  /** an iterator over all PolyNf s that are subterms of this one */
  class SubtermIter;

  /** returns an iterator over all PolyNf s that are subterms of this one */
  IterTraits<SubtermIter> iterSubterms() const;

  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self);

  static PolyNf fromNormalized(TypedTermList);
  void integrity() { 
#if POLYNF_INTEGRITY_CHECKS
    _self.apply([](auto& x) -> void { x.integrity(); }); 
#endif
  }
};


template<class N> bool operator!=(const Polynom<N>& l, const Polynom<N>& r) { return !(l == r); }

/** an iterator over a literal's arguments. The arguments are mapped to their corresponding PolNf s */
class IterArgsPnf
{
  Literal* _lit;
  unsigned _idx;
public:
  DECL_ELEMENT_TYPE(PolyNf);

  IterArgsPnf(Literal* lit);

  bool hasNext() const;
  PolyNf next();
};

/** convienent constructor for IterArgsPnf */
IterTraits<IterArgsPnf> iterArgsPnf(Literal* lit);

struct ImmediateSubterms {

  template<class N>
  auto operator()(Monom<N> const& self) const 
  { return ImmediateSubterms{}(self.factors); }

  template<class N>
  auto operator()(MonomFactor<N> const& self) const 
  { return iterTraits(getSingletonIterator(PolyNf::fromNormalized(TypedTermList(self._term, N::sort())))); }

  template<class N>
  auto operator()(MonomFactors<N> const& self) const 
  { return self.iter().flatMap([](auto fac) { return ImmediateSubterms{}(fac); }); }

  template<class N>
  auto operator()(Polynom<N> const& self) const 
  { return self.iterSummands().flatMap([](auto monom) { return ImmediateSubterms{}(monom); }); }

  // template<class C>
  // auto operator()(C const& self) const 
  // {
  //   static_assert(std::is_same<C, AnyPoly>::value, "this is the last fallback option for the template lookup");
  //   return iterTraits(self._self.apply([](auto& poly) 
  //         { return pvi(ImmediateSubterms{}(poly)); }));
  // }

  auto operator()(AnyPoly const& self) const 
  {
    return iterTraits(self._self.apply([](auto& poly) 
          { return pvi(ImmediateSubterms{}(poly)); }));
  }

  auto operator()(FuncTerm self) const 
  {
    return range(0, self.numTermArguments())
      .map([=](auto i) { return self.arg(i); });
  }

};

} // namespace Kernel

// include needs to go here, since we need the specialization BottomUpChildIter<PolyNf> to declare Iter
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

namespace Kernel {

class PolyNf::SubtermIter {
  Stack<BottomUpChildIter<PolyNf>> _stack;
public:
  DECL_ELEMENT_TYPE(PolyNf);

  SubtermIter(SubtermIter&&) = default;
  SubtermIter& operator=(SubtermIter&&) = default;

  SubtermIter(PolyNf p);

  PolyNf next();

  bool hasNext() const;
};

} // namespace Kernel

////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
// TEMPLATE STUFF IMPLEMENTATIONS
//////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////
// impl Monom template stuff
////////////////////////////
namespace Kernel {

template<class Number>
Monom<Number>::Monom(Monom<Number>::Numeral numeral, MonomFactors<Number> factors) 
  : numeral(numeral), factors(factors)
{ }


template<class Number>
Monom<Number> Monom<Number>::zero() 
{ 
  static Monom p = Monom(Numeral(0), MonomFactors<Number>());
  return p; 
}

// template<class Number>
// Option<typename Monom<Number>::Numeral> Monom<Number>::tryNumeral() const 
// {
//   using Opt = Option<Numeral>;
//   if (this->factors->isOne()) {
//     return Opt(numeral);
//   } else {
//     return Opt();
//   }
// }

template<class Number>
Option<Variable> Monom<Number>::tryVar() const 
{
  using Opt = Option<Variable>;
  if (numeral == Numeral(1)) {
    return  factors.tryVar();
  } else {
    return  Opt();
  }
}

template<class Number>
void Monom<Number>::integrity() const 
{
#if POLYNF_INTEGRITY_CHECKS
  this->factors.integrity();
#endif // VDEBUG
}
template<class Number>
bool operator<(Monom<Number> const& l, Monom<Number> const& r)
{ return std::tie(l.factors, l.numeral) < std::tie(r.factors, r.numeral); }

template<class Number>
bool operator!=(Monom<Number> const& l, Monom<Number> const& r)
{ return !(l == r); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const Monom<Number>& self)
{ 
  if (self.numeral != typename Number::ConstantType(1)) {
    out << self.numeral << " ";
  }
  return out << self.factors; 
}


template<class Number>
TermList MonomFactor<Number>::denormalize() const
{
  CALL("MonomFactors::denormalize()")

  ASS(_power > 0)
  auto t = this->_term;
  TermList out = t;
  for (int i = 1; i < _power; i++) {
    out = Number::mul(t, out);
  }
  return out;
}


template<class Number>
PolyNf MonomFactor<Number>::term() const
{ return PolyNf::fromNormalized(TypedTermList(_term, Number::sort())); }


template<class Number>
TermList MonomFactors<Number>::denormalize() const
{ return _inner; }


} // namespace Kernel





/////////////////////////////////////////////////////////
// impl FuncId template stuff
////////////////////////////

namespace Kernel {

template<class Number>
Option<typename Number::ConstantType> FuncId::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  Numeral out;
  if (theory->tryInterpretConstant(_num, out)) {
    return Option<Numeral>(out);
  } else {
    return Option<Numeral>();
  }
}

} // namespace Kernel


/////////////////////////////////////////////////////////
// impl FuncTerm template stuff
////////////////////////////


namespace Kernel {

// template<class Args> FuncTerm::FuncTerm(FuncId f, Args const& args) 
//   : _fun(f)
//   , _args(f.arity())
// {
//   static_assert(std::is_same< typename std::remove_const<typename std::remove_reference<decltype(args[0u])>::type>::type
//                             , PolyNf
//                             >::value, "args must return a PolyNf on a call  operator[](unsigned)");
//   for (unsigned i = 0; i < f.arity(); i++) 
//     _args.push(args[i]);
// }

template<class Number>
Option<typename Number::ConstantType> FuncTerm::tryNumeral() const
{ return function().template tryNumeral<Number>(); }

} // namespace Kernel


/////////////////////////////////////////////////////////
// impl AnyPoly  template stuff
////////////////////////////

namespace Kernel {

template<class NumTraits> Option<Polynom<NumTraits> const&>  AnyPoly::downcast() const
{ return _self.as<Polynom<NumTraits>>(); }

template<class NumTraits> Option<Polynom<NumTraits>      &>  AnyPoly::downcast()
{ return _self.as<Polynom<NumTraits>>(); }

template<class NumTraits> 
bool AnyPoly::isType() const 
{ return _self.is<Polynom<NumTraits>>(); }

/* helper function for AnyPoly::tryNumeral */
template<class NumIn, class NumOut>
struct __ToNumeralHelper 
{
  Option<typename NumOut::ConstantType> operator()(Polynom<NumIn> const&) const
  { return Option<typename NumOut::ConstantType>(); }
};

/* helper function for AnyPoly::tryNumeral */
template<class Num>
struct __ToNumeralHelper<Num,Num>
{
  Option<typename Num::ConstantType> operator()(Polynom<Num> const& p) const
  { return p.toNumber(); }
};

template<class NumOut>  
struct PolymorphicToNumeral 
{
  template<class NumIn>
  Option<typename NumOut::ConstantType> operator()(Polynom<NumIn> const& p) const
  { return __ToNumeralHelper<NumIn, NumOut>{}(p); }
};


template<class NumTraits>
Option<typename NumTraits::ConstantType> AnyPoly::tryNumeral() const&
{ return apply(PolymorphicToNumeral<NumTraits>{}); }

} // namespace Kernel

/////////////////////////////////////////////////////////
// impl PolyNf  template stuff
////////////////////////////

namespace Kernel {


template<class NumTraits>
Option<Polynom<NumTraits> const&> PolyNf::downcast() const
{ auto poly = asPoly(); return poly.andThen([](auto& p) { return p.template downcast<NumTraits>(); }); }

template<class NumTraits>
Option<Polynom<NumTraits>      &> PolyNf::downcast()
{ auto poly = asPoly(); return poly.andThen([](auto& p) { return p.template downcast<NumTraits>(); }); }



// TODO maybe get rid of copying here?
template<class Number> 
Polynom<Number> PolyNf::wrapPoly() const
{
  auto poly = this->asPoly();
  if (poly.isSome()) {
    return Polynom<Number>(poly.unwrap().downcast<Number>().unwrap());
  } else {
    return Polynom<Number>(*this);
  }
}

// template<class Number> 
// Monom<Number> PolyNf::wrapMonom() const
// {
//   return this->wrapPoly<Number>()->tryMonom() || [&]() -> Monom<Number> { return Monom<Number>(*this); };
// }

template<class Number>
Option<typename Number::ConstantType> PolyNf::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  return match(
      [](FuncTerm t) { return t.tryNumeral<Number>(); },
      [](Variable t) { return Option<Numeral>();              },
      [](AnyPoly  t) { return t.template tryNumeral<Number>(); }
    );
}

} // namespace Kernel

/////////////////////////////////////////////////////////
// impl MonomFactor  tempalte stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactor<Number>::MonomFactor(PolyNf term, int power) 
  : _term( power == 0 ? Number::one() : term.denormalize())
  , _power(power == 0 ? 1             : power)
{}


// template<class Number>
// PolyNf::SubtermIter MonomFactor<Number>::iterSubterms() const
// { return term.iterSubterms(); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const MonomFactor<Number>& self) {
  // out << self._term;
#if POLYNF_NICE_OUTPUT
  out << self.term();
  if (self.power() != 1) 
    out << "^" << self.power();
  return out;
#else 
  out << "pow(" self.term() << ", " << self.power() << ")";
#endif
}


template<class Number>
Option<Variable> MonomFactor<Number>::tryVar() const 
{ return _power == 1 ? term().tryVar() : none<Variable>(); }

// template<class Number>
// Option<Polynom<Number>> MonomFactor<Number>::tryPolynom() const 
// { return power == 1 ? term.downcast<Number>() : none<Polynom<Number>>(); }

} // namespace Kernel

/////////////////////////////////////////////////////////
// impl MonomFactors  tempalte stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactors<Number>::MonomFactors(TermList t) 
  : _inner(t) { integrity(); }

template<class Number>
MonomFactors<Number>::MonomFactors(Stack<MonomFactor> const& factors) 
  : MonomFactors(MonomFactors::fromIterator(factors.iterFifo())) { }

template<class Number>
MonomFactors<Number>::MonomFactors() 
  : MonomFactors(MonomFactors::fromNormalized(Number::one())) { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t) 
  : MonomFactors(MonomFactors::fromNormalized(t.denormalize())) { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t1, PolyNf t2) 
  : MonomFactors(t1 == t2 ? Stack<MonomFactor>({ MonomFactor ( t1, 2 )  }) : 
                 t1 <  t2 ? Stack<MonomFactor>({ MonomFactor ( t1, 1 ), MonomFactor ( t2, 1 ) }) 
                          : Stack<MonomFactor>({ MonomFactor ( t2, 1 ), MonomFactor ( t1, 1 ) }) 
                            )  { }

template<class Number>
unsigned MonomFactors<Number>::cntFactors() const 
{ return iter().count(); }

// template<class Number>
// MonomFactor<Number> & MonomFactors<Number>::factorAt(unsigned i) 
// { return _factors[i]; }
//
// template<class Number>
// MonomFactor<Number> const& MonomFactors<Number>::factorAt(unsigned i) const
// { return _factors[i]; }
//
// template<class Number>
// PolyNf const& MonomFactors<Number>::termAt(unsigned i) const
// { return _factors[i].term; }
//
// template<class Number>
// Stack<MonomFactor<Number>> & MonomFactors<Number>::raw()
// { return _factors; }
//

template<class Number>
Option<MonomFactor<Number>> MonomFactors<Number>::tryMonomFactor() const
{ 
  auto i = iter();
  if (i.hasNext()) {
    auto f = i.next();
    if (i.hasNext()) {
      return Option<MonomFactor>();
    } else {
      return Option<MonomFactor>(std::move(f));
    }
  } else {
    return Option<MonomFactor>();
  }
}


// template<class Number>
// Option<Polynom<Number>> MonomFactors<Number>::tryPolynom() const
// { return tryMonomFactor()
//     .andThen([](auto f) { return f.tryPolynom(); }); }

template<class Number>
MonomFactors<Number> MonomFactors<Number>::one()
{ return MonomFactors(); }

template<class Number>
bool MonomFactors<Number>::isOne() const 
{ return _inner == Number::one(); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const MonomFactors<Number>& self) 
{
#if POLYNF_NICE_OUTPUT
  auto iter = self.iter();
  auto first = iter.next();
  if (iter.hasNext()) {
    out << "(";
    out << first;
    while (iter.hasNext())
      out << " " << iter.next();
    out << ")";
  } else {
    out << first;
  }
  return out;
#else
  out << "prod(";
  auto iter = self.iter();
  out << iter.next();
  while (iter.hasNext())
    out << " " << iter.next();
  out << ")";
  return out;
#endif
}


template<class Number>
Option<Variable> MonomFactors<Number>::tryVar() const 
{ return tryMonomFactor()
    .andThen([](auto f) { return f.tryVar(); }); }

template<class Number>
void MonomFactors<Number>::integrity() const 
{
#if POLYNF_INTEGRITY_CHECKS
  for (auto fac : this->iter()) {
    fac.integrity();
    ASS_REP(!theory->isInterpretedFunction(fac.term().denormalize(), Number::mulI), fac)
  }
  auto iter = this->iter();
  ASS(iter.hasNext())
  auto x0 = iter.next();
  while (iter.hasNext()) {
    auto x1 = iter.next();
    ASS_LE(x0.term(), x1.term())
    x0 = std::move(x1);
  }
#endif
}

template<class Number>
MonomFactors<Number> MonomFactors<Number>::replaceTerms(PolyNf* simplifiedTerms, unsigned& cnt) const
{
  int offs = 0;
  auto out = MonomFactors(iter()
      .map([&](MonomFactor f) { return f.replaceTerm(simplifiedTerms[offs++]); })
      .template collect<Stack>());
  cnt = offs;
  return out;
}

} // namespace Kernel

/////////////////////////////////////////////////////////
// impl Polynom tempalte stuff
////////////////////////////

namespace Kernel {



template<class Number>
Polynom<Number>::Polynom(Monom m) 
  : Polynom(
      Stack<Monom>{m})
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral numeral, PolyNf term) 
  : Polynom(Monom(numeral, MonomFactors(term)))
{  }

template<class Number>
Polynom<Number>::Polynom(PolyNf t) 
  : Polynom(Numeral(1), t) 
{ integrity();  }

template<class Number>
Polynom<Number>::Polynom(Numeral constant) 
  : Polynom(Monom(constant, MonomFactors::one())) 
{ }


template<class Number>
std::ostream& operator<<(std::ostream& out, const Polynom<Number>& self) {
  auto iter = self.iterSummands();
#if POLYNF_NICE_OUTPUT
  auto first = iter.next();
  if (!iter.hasNext()) {
    return out << first;
  } else {
    out << "(" << first;
    while (iter.hasNext()) {
      out << " + " << iter.next();
    }
    return out << ")";
  }
#else
  out << "Poly(";
  if (!iter.hasNext()) {
    out << "<empty>";
  } else {
    out << iter.next();
    while (iter.hasNext()) {
      out << " + " << iter.next();
    }
  }
#if !OUTPUT_NICE 
  out << ")";
#endif 
  return out;
#endif
}



template<class Number>
Polynom<Number> Polynom<Number>::zero() 
{ 
  auto out = Polynom::fromNormalized(Number::zero()); 
  out.integrity();
  return std::move(out);
}

template<class Number>
Option<typename Number::ConstantType> Polynom<Number>::toNumber() const& 
{ return Number::tryNumeral(_inner); }

template<class Number>
bool Polynom<Number>::isNumber() const& 
{ 
  return toNumber().isSome();
}

template<class Number>
typename Number::ConstantType Polynom<Number>::unwrapNumber() const& 
{ return toNumber().unwrap(); }

template<class NumTraits>
Option<Polynom<NumTraits>> Polynom<NumTraits>::tryFromNormalized(TypedTermList t)
{
  if (t.sort() != NumTraits::sort()) {
    return Option<Polynom>();
  } else {
    // auto isAdd = [](auto t) 
    // { return t.isTerm() && t.term()->functor() == NumTraits::addF(); };
    //
    // auto isMul = [](auto t) 
    // { return t.isTerm() && t.term()->functor() == NumTraits::mulF(); };

    return some(Polynom(t));
  }
}


template<class NumTraits>
Monom<NumTraits> Monom<NumTraits>::fromNormalized(TermList t)
{
  ASS(t.isVar() || SortHelper::getResultSort(t.term()) == NumTraits::sort())
  if (t.isTerm()) {
    auto trm = t.term();

    if (trm->functor() == NumTraits::mulF()) {
      auto num = NumTraits::tryNumeral(trm->termArg(0));
      if (num.isSome()) {
        ASS(num.unwrap() != Numeral(1))
        ASS(num.unwrap() != Numeral(-1))
        return Monom(num.unwrap(), MonomFactors<NumTraits>::fromNormalized(t.term()->termArg(1)));
      }
    } else if (trm->functor() == NumTraits::minusF()) {
      return Monom(Numeral(-1), MonomFactors<NumTraits>::fromNormalized(t.term()->termArg(0)));

    } else if (NumTraits::tryNumeral(t).isSome()) {
      auto num = NumTraits::tryNumeral(t).unwrap();
      return Monom(num, MonomFactors<NumTraits>::one());
    }

  }
  return Monom(Numeral(1), MonomFactors<NumTraits>::fromNormalized(t));
}


template<class NumTraits>
MonomFactors<NumTraits> MonomFactors<NumTraits>::fromNormalized(TermList t)
{
  ASS(t.isVar() || SortHelper::getResultSort(t.term()) == NumTraits::sort())
  return MonomFactors(t);
  // auto isMul = [](auto t) 
  // { return t.isTerm() && t.term()->functor() == NumTraits::mulF(); };
  //
  // Stack<MonomFactor> factors(1);
  // TermList curr = t;
  // while (isMul(curr)) {
  //   // ASS(!isMul(curr.term()->termArg(0)))
  //   factors.push(MonomFactor::fromNormalized(curr.term()->termArg(0)));
  //   curr = curr.term()->termArg(1);
  // }
  // // TODO sorted assertions
  // return MonomFactors(std::move(factors));
}


template<class NumTraits>
MonomFactor<NumTraits> MonomFactor<NumTraits>::fromNormalized(TermList t)
{
  ASS(t.isVar() || SortHelper::getResultSort(t.term()) == NumTraits::sort())
  auto isMul = [](auto t) 
  { return t.isTerm() && t.term()->functor() == NumTraits::mulF(); };

  unsigned cnt;
  TermList inner;
  if (isMul(t)) {
    inner = t.term()->termArg(0);
    TermList curr = t;
    cnt = 1;
    
    while (isMul(curr)) {
      ASS_EQ(curr.term()->termArg(0), inner)
      curr = curr.term()->termArg(1);
      cnt++;
    }

  } else {
    inner = t;
    cnt = 1;
  }
  // TODO sorted assertions
  return MonomFactor(PolyNf::fromNormalized(TypedTermList(inner, NumTraits::sort())), cnt);
}


template<class Number>
TermList Monom<Number>::denormalize() const
{
  CALL("Monom::denormalize()")
  auto c = TermList(theory->representConstant(this->numeral));
  if (this->factors.isOne()) {
    return c;
  } else {
    auto mon = this->factors.denormalize();
    if (this->numeral == Number::oneC()) {
      return mon;
    } else if (this->numeral == Number::constant(-1)) {
      return Number::minus(mon);
    } else {
      return Number::mul(c, mon);
    }
  }
}


// template<class Number>
// TermList Polynom<Number>::denormalize() const
// { return _inner; }

// template<class Number>
// TermList Polynom<Number>::denormalize() const
// {
//   CALL("Polynom::denormalize()")
//
//   auto monomToTerm = [](Monom const& monom) -> TermList {
//     auto c = TermList(theory->representConstant(monom.numeral));
//     if (monom.factors.isOne()) {
//       return c;
//     } else {
//       auto mon = monom.factors.denormalize();
//       if (monom.numeral == Number::oneC()) {
//         return mon;
//       } else if (monom.numeral == Number::constant(-1)) {
//         return Number::minus(mon);
//       } else {
//         return Number::mul(c, mon);
//       }
//     }
//   };
//
//   if (_summands.size() == 0) {
//     return Number::zero();
//   } else {
//
//     TermList out = monomToTerm(_summands[_summands.size() - 1]);
//
//     for (unsigned i = 1; i < nSummands(); i++) {
//       auto& monom = _summands[_summands.size() - i - 1];
//       out = Number::add(monomToTerm(monom), out);
//     }
//     return out;
//   }
// }

// template<class Number>
// Stack<Monom<Number>>& Polynom<Number>::raw()
// { return _summands; }

template<class Number>
Polynom<Number> Polynom<Number>::replaceTerms(PolyNf* simplifiedTerms) const 
{
  CALL("Polynom::replaceTerms(PolyNf*)")
  return Polynom::fromIterator(this->iterSummands()
    .map([&](Monom summand) -> Monom {
        unsigned cnt;
        auto newSummand = summand.replaceTerms(simplifiedTerms, cnt);
        simplifiedTerms += cnt;
        return newSummand;
    }));
}

// template<class Number>
// unsigned Polynom<Number>::nSummands() const
// { return _summands.size(); }
//
// template<class Number>
// unsigned Polynom<Number>::nFactors(unsigned summand) const
// { return _summands[summand].factors.nFactors(); }
//
// template<class Number>
// Monom<Number> const& Polynom<Number>::summandAt(unsigned summand) const
// { return _summands[summand]; }
//
// template<class Number>
// Monom<Number>      & Polynom<Number>::summandAt(unsigned summand)
// { return _summands[summand]; }

template<class Number>
void Polynom<Number>::integrity() const {
#if POLYNF_INTEGRITY_CHECKS
  for (auto s : this->iterSummands()) {
    s.integrity();
    ASS_REP(!theory->isInterpretedFunction(s.denormalize(), Number::addI), s)
  }
  auto iter = this->iterSummands();
  ASS(iter.hasNext())
  auto x0 = iter.next();
  while (iter.hasNext()) {
    auto x1 = iter.next();
    ASS_LE(x0.factors, x1.factors)
    x0 = std::move(x1);
  }
#endif
}

} // namespace Kernel

#undef DEBUG
#endif // __POLYNOMIAL__H__

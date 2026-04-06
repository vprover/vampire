/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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

#include "Kernel/NumTraits.hpp"
#include <cassert>
#include "Lib/Coproduct.hpp"
#include "Lib/Option.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "ALASCA/Signature.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Perfect.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Hash.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
#define OUTPUT_NICE 1

namespace Kernel {

// TODO use this newtype in Term.hpp
/** newtype for wrapping variable ids */
class Variable 
{
  unsigned _num;
public: 
  Variable();
  explicit Variable(unsigned num);
  unsigned id() const;

  void integrity() const {  }
  friend struct std::hash<Variable>;
  friend std::ostream& operator<<(std::ostream& out, const Variable& self);
  auto asTuple() const { return std::make_tuple(_num); }
  IMPL_HASH_FROM_TUPLE(Variable);
  IMPL_COMPARISONS_FROM_TUPLE(Variable);
};

} // namespace Kernel

template<> struct std::hash<Kernel::Variable>
{
  size_t operator()(Kernel::Variable const& self)
  { return std::hash<unsigned>{}(self._num); }
};

namespace Kernel {

// TODO use this newtype in Term.hpp
/** newtype for wrapping function ids (also often called functors in vampire) */
class FuncId 
{
  unsigned _num;
  const TermList* _typeArgs;
  
  explicit FuncId(unsigned num, const TermList* typeArgs);
public: 

  template<class Numeral> 
  static FuncId numeralConstant(Numeral const& num) 
  { return FuncId(NumTraits<Numeral>::constantF(num), nullptr); }

  template<class Numeral> 
  static FuncId linMul(Numeral const& num) 
  { return FuncId(NumTraits<Numeral>::linMulF(num), nullptr); }

  static FuncId fromInterpretation(Theory::Interpretation i)
  { return FuncId(env.signature->getInterpretingSymbol(i), nullptr); }

  static FuncId symbolOf(Term* term);
  unsigned numTermArguments() const;
  unsigned numTypeArguments() const;
  TermList typeArg(unsigned i) const;

  template<class NumTraits>
  bool isFloor(NumTraits) const { return NumTraits::isFloor(id()); }

  bool isFloor(IntTraits) const { return false; }

  template<class NumTraits>
  bool isFloor() const 
  { return isFloor(NumTraits{}); }

  bool isFloor() const 
  { return forAnyNumTraits([&](auto n) { return isFloor<decltype(n)>(); }); }

  friend std::ostream& operator<<(std::ostream& out, const FuncId& self);
  auto iterTypeArgs() const 
  { return range(0, numTypeArguments()).map([&](auto i) { return typeArg(i); }); }

  Signature::Symbol* symbol() const;

  unsigned id() const;
  Theory::Interpretation interpretation() const;
  bool isInterpreted() const;
  Option<Theory::Interpretation> tryInterpret() const;

  template<class Number>
  Option<typename Number::ConstantType> tryNumeral() const;
  
  auto asTuple() const { return std::tuple(_num, iterContOps(iterTypeArgs())); }
  IMPL_COMPARISONS_FROM_TUPLE(FuncId)
  IMPL_HASH_FROM_TUPLE(FuncId)
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
// class declarations for PolyNf
/////////////////////////////////////////////////////////

/** 
 * Represents a summand in a polynom of the number type Number 
 * e.g. a term like 3 * (a*x) would be represented as 
 * Monom { 3, MonomFactors { a, x }}
 */
template<class Number> 
struct Monom 
{
  USE_ALLOCATOR(Monom)

  using Numeral = typename Number::ConstantType;

  Numeral numeral;
  Perfect<MonomFactors<Number>> factors;

  Monom(Numeral numeral, Perfect<MonomFactors<Number>> factors);
  Monom(Perfect<MonomFactors<Number>> factors) : Monom(Numeral(1), std::move(factors)) {}
  // Monom(Numeral numeral, PolyNf t); //: Monom(numeral, perfect(MonomFactors(t))) {}
  Monom(Numeral numeral) : Monom(numeral, perfect(MonomFactors<Number>::one())) {}
  Monom(int num) : Monom(Numeral(num)) {}
  Monom(int n1, int n2) : Monom(Numeral(n1, n2)) {}
  Monom(PolyNf);
  Monom(MonomFactors<Number> factors) : Monom(Numeral(1), perfect(std::move(factors))) {}

  static Monom zero();
  bool isZeroMul() const;
  bool isZeroConst() const;

  Option<Variable> tryVar() const;
  Option<Numeral> tryNumeral() const;
  bool isVar()     const { return tryVar().isSome(); }
  bool isNumeral() const { return tryNumeral().isSome(); }
  TermList denormalize() const;

  template<class F> Monom mapVars(F f) const;

  /** performs an integrity check on the datastructure, only has an effect in debug mode */
  void integrity() const;

  friend Monom operator*(Numeral n, Monom const& self) 
  { return Monom(n * self.numeral, self.factors); }

  friend Monom operator/(Monom const& self, Numeral n) 
  { return Monom(self.numeral / n, self.factors); }

  friend Monom operator-(Monom const& self) 
  { return Numeral(-1) * self; }
};


/**
 * Represents an ordenary complex term, in the PolyNF term tree.
 */
class FuncTerm 
{
  FuncId _fun;
  Stack<PolyNf> _args;
public:
  USE_ALLOCATOR(FuncTerm)

  FuncTerm(FuncId f, Stack<PolyNf>&& args);
  FuncTerm(FuncId f, PolyNf* args);

  template<class NumTraits>
  bool isSort() const { return _fun.symbol()->fnType()->result() == NumTraits::sort(); }

  unsigned numTermArguments() const;
  FuncId function() const;
  PolyNf const& arg(unsigned i) const;

  template<class Number> 
  Option<typename Number::ConstantType> tryNumeral() const;

  template<class F> FuncTerm mapVars(F f) const;

  void integrity() const;

  auto iterArgs() const  { return iterTraits(_args.iterFifo()); }

  friend std::ostream& operator<<(std::ostream& out, const FuncTerm& self);
  friend bool operator==(FuncTerm const& lhs, FuncTerm const& rhs);
  friend bool operator!=(FuncTerm const& lhs, FuncTerm const& rhs);
  friend struct std::hash<FuncTerm>;

};

using AnyPolySuper = Coproduct< 
    Perfect<Polynom< IntTraits>>
  , Perfect<Polynom< RatTraits>>
  , Perfect<Polynom<RealTraits>>
  >;

class AnyPoly : public AnyPolySuper
{
public:
  /** creates a new dynamically typed polynom from a statically typed one */
  template<class NumTraits> AnyPoly(Perfect<Polynom<NumTraits>> x);

  /** tries to turn this polynom into a polynom of the given NumTraits. */
  template<class NumTraits> Option<Perfect<Polynom<NumTraits>> const&> downcast() const&;

  /** returns whether this is a Polynom of the given NumTraits. */
  template<class NumTraits> bool isType() const;

  /** if this polynom has the right sort, and consist of a single summand that is a numeral, then this numeral
   * is returned. otherwise an empty Option is returned. */
  template<class NumTraits> Option<typename NumTraits::ConstantType> tryNumeral() const&;

  /** \see template<class N> Polynom<N>::replaceTerms */
  AnyPoly replaceTerms(PolyNf* newTs) const;

  template<class Numeral>
  static AnyPoly fromNumeral(Numeral n) 
  { return perfect(Polynom<NumTraits<Numeral>>::fromNumeral(n)); }

  template<class F> AnyPoly mapVars(F f) const;

  /** \see template<class N> Polynom<N>::nSummands */
  unsigned nSummands() const;

  /** \see template<class N> Polynom<N>::nFactors */
  unsigned nFactors(unsigned i) const;

  /** \see template<class N> Polynom<N>::termAt */
  PolyNf const& termAt(unsigned summand, unsigned factor) const;

  /** \see template<class N> Polynom<N>::denormalize */
  TermList denormalize(TermList* results) const;

  void integrity() const;

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self);
  friend struct std::hash<AnyPoly>;
};

using PolyNfSuper = Lib::Coproduct<Perfect<FuncTerm>, Variable, AnyPoly>;

template<class A> A & deref(A          & x) { return  x; }
template<class A> A & deref(A          * x) { return *x; }
template<class A> A & deref(Perfect<A> & x) { return *x; }

template<class A> A const& deref(A          const& x) { return  x; }
template<class A> A const& deref(A          const* x) { return *x; }
template<class A> A const& deref(Perfect<A> const& x) { return *x; }

/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * See the file-level documentation for how this datatype is composed.
 */
class PolyNf : public PolyNfSuper
{
public:

  PolyNf(Perfect<FuncTerm> t);
  PolyNf(Variable               t);
  PolyNf(AnyPoly                t);
  template<class NumTraits>
  PolyNf(Perfect<Polynom<NumTraits>>     t) : PolyNf(AnyPoly(std::move(t))) {}
  template<class NumTraits>
  PolyNf(Polynom<NumTraits>     t) : PolyNf(perfect(std::move(t))) {}
  template<class NumTraits>
  PolyNf(Monom<NumTraits>     t) : PolyNf(Polynom<NumTraits>(std::move(t))) {}
  template<class NumTraits>
  PolyNf(Perfect<MonomFactors<NumTraits>> t) : PolyNf(Monom<NumTraits>(std::move(t))) {}
  template<class NumTraits>
  PolyNf(MonomFactors<NumTraits>     t) : PolyNf(perfect(std::move(t))) {}

  static PolyNf normalize(TypedTermList t, bool& simplified);
  static PolyNf normalize(TypedTermList t);

  /** 
   * If this term is a polynomial of sort NumTraits, it is downcasted to that sort,
   * otherwise an empty Option is returned
   */
  template<class NumTraits>
  Option<Perfect<Polynom<NumTraits>>> downcast() const;

  /** turns the normal form term PolyNf into an ordenary vampire term TermList. */
  TermList denormalize() const;

  /** 
   * Turns this PolyNf term into a typed polynom of sort Number.
   * this must have the same sort as Number. 
   * If this is already a polynom it will just be downcasted, 
   * otherwise (when it is a Variable, or a FuncTerm) it will be 
   * wrapped in a polynom.
   */
  template<class Number> 
  Perfect<Polynom<Number>> wrapPoly() const;
  
  /** 
   * Turns this PolyNf term into a typed polynom of sort Number.
   * this must have the same sort as Number. 
   * If this is already a polynom it will just be downcasted, 
   * otherwise (when it is a Variable, or a FuncTerm) it will be 
   * wrapped in a polynom.
   */
  template<class Number> 
  Monom<Number> wrapMonom() const;
  

  /** if this PolyNf is a numeral, the numeral is returned */
  template<class Number>
  Option<typename Number::ConstantType> tryNumeral() const;

  template<class Num>
  static PolyNf fromNumeral(Num n)
  { return PolyNf(AnyPoly::fromNumeral(n)); }

  /** if this PolyNf is a Variable, the variable is returned */
  Option<Variable> tryVar() const;

  /** an iterator over all PolyNf s that are subterms of this one */
  class SubtermIter;

  /** returns an iterator over all PolyNf s that are subterms of this one */
  SubtermIter iterSubterms() const;

  template<class F> PolyNf mapVars(F f) const;

  Option<Perfect<FuncTerm>> tryFuncTerm() const { return as<Perfect<FuncTerm>>().toOwned(); }

  void integrity() const {  apply([](auto const& x) -> void { deref(x).integrity(); }); }

  friend struct std::hash<PolyNf>;
  friend bool operator==(PolyNf const& lhs, PolyNf const& rhs);
  friend bool operator!=(PolyNf const& lhs, PolyNf const& rhs);
  friend bool operator<(const PolyNf& lhs, const PolyNf& rhs);
  friend bool operator<=(const PolyNf& lhs, const PolyNf& rhs);
  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self);
};


/** 
 * Represents a factor in a monom. Each unique term contained in the monom is stored 
 * together with the number of occurrences of the term within that monom.
 *
 * e.g. a term like (x * x * a * x) is represented as 
 * MonomFactors { MonomFactor(x, 3), MonomFactor(a, 1) }
 */
template<class Number> 
struct MonomFactor 
{
  PolyNf term;
  int power;

  MonomFactor(PolyNf term, int power);

  template<class F> MonomFactor mapVars(F f) const;

  void integrity() const { term.integrity(); }
  /** if this monomfactor is a Variable and has power one it is turned into a variable */
  Option<Variable> tryVar() const;
  Option<Perfect<Polynom<Number>>> tryPolynom() const;
  bool isPolynom() const { return tryPolynom().isSome(); }

  PolyNf::SubtermIter iterSubterms() const;
};



/** 
 * Represents the non-numeral part of a monom. this means it is a sorted list of MonomFactor s.
 */
template<class Number>
class MonomFactors 
{
  using MonomFactor = Kernel::MonomFactor<Number>;
  using Monom       = Kernel::Monom<Number>;
  using Polynom     = Kernel::Polynom<Number>;
  using Numeral = typename Number::ConstantType;
  Stack<MonomFactor> _factors;
  friend struct std::hash<MonomFactors>;

public:
  USE_ALLOCATOR(MonomFactors)

  /** 
   * constructs a new MonomFactors. 
   * \pre factors must be sorted
   */
  MonomFactors(Stack<MonomFactor>&& factors);

  /** constructs an empty product, which corresponds to the numeral one.  */
  MonomFactors();

  /** constructs a singleton product */
  MonomFactors(PolyNf t);

  /** constructs the product of t1 and t2. There is no precondigion on the ordering of t1 and t2. */
  MonomFactors(PolyNf t1, PolyNf t2);

  /** returns the number of factors */
  unsigned nFactors() const;

  /** returns the nth factor */
  MonomFactor      & factorAt(unsigned i);

  /** returns the nth factor */
  MonomFactor const& factorAt(unsigned i) const;

  /** returns the number of factors */
  PolyNf const& termAt(unsigned i) const;

  /** returns whether this monom is a polynom, i.e. if its only factor is a polynom */
  bool isPolynom() const;

  /** turns this monom into a polynom. 
   * \pre isPolynom  must be true
   */
  Perfect<Polynom> asPolynom() const;

  /** returns the (empty) product one */
  static MonomFactors one();

  /** returns whether this is an empty product */
  bool isOne() const;


  /** if this MonomFactors consist of a single variable if will be returned  */
  Option<Variable> tryVar() const;

  /** performs an integrity check on the datastructure, only has an effect in debug mode */
  void integrity() const;

  /** replaces all the factors, by new ones, keeping the power of each term the same  */
  MonomFactors replaceTerms(PolyNf* simplifiedTerms) const;


  /** returns an iterator over all factors */
  auto iter() const&
  { return arrayIter(_factors); }

  auto iterSubterms() const;

  template<class F> MonomFactors mapVars(F f) const;

  explicit MonomFactors(const MonomFactors&) = default;
  explicit MonomFactors(MonomFactors&) = default;

  MonomFactors& operator=(MonomFactors&&) = default;
  MonomFactors(MonomFactors&&) = default;

  template<class N> friend std::ostream& operator<<(std::ostream& out, const MonomFactors<N>& self);
  template<class N> friend bool operator==(const MonomFactors<N>& l, const MonomFactors<N>& r);
  template<class N> friend bool operator!=(const MonomFactors<N>& l, const MonomFactors<N>& r);

  /** helper function for PolyNf::denormalize() */
  TermList denormalize(TermList* results) const;

  TermList denormalize() const;
  Stack<MonomFactor>& raw();
};

template<class N> bool operator!=(const MonomFactors<N>& l, const MonomFactors<N>& r) { return !(l == r); }

template<class Number>
class Polynom 
{
  friend struct std::hash<Polynom>;

  using Numeral      = typename Number::ConstantType;
  using MonomFactors = Kernel::MonomFactors<Number>;
  using Monom        = Kernel::Monom<Number>;

  Stack<Monom> _summands;

public:
  using NumTraits = Number;
  USE_ALLOCATOR(Polynom)

  /** 
   * constructs a new Polynom with a list of summands 
   * \pre summands must be sorted
   */
  explicit Polynom(Stack<Monom>&& summands);

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(Monom m);

  /** creates a Polynom that consists of only one summand, that is a product of numeral, and term */
  explicit Polynom(Numeral numeral, PolyNf term);

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(PolyNf t);

  /** creates a Polynom that consists of only one summand */
  explicit Polynom(Numeral constant);
  
  static Polynom fromNumeral(Numeral constant) 
  { return Polynom(constant); }

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
  TermList denormalize() const;

  /** helper function for denormalize() */
  TermList denormalize(TermList* results) const;

  /**
   * replaces all subterms of this poly, by given array of subterms. the resulting polynom will be sorted correctly. 
   * here a monom does not count as a subterm, but all the subterms of the monom themselves do:
   *      Polynom(Monom(3, { f(x), y }), Monom(1, { z }))
   *         .replaceTerms({a,b,c})
   * ===> Polynom(Monom(3, { a   , b }), Monom(1, { c }))
   */
  Polynom replaceTerms(PolyNf* simplifiedTerms) const;

  /** returns the number of summands of this polynom */
  unsigned nSummands() const;

  /** returns the number of factors of the summand with the given index */
  unsigned nFactors(unsigned summand) const;

  /** returns the summand with the given index */
  Monom const& summandAt(unsigned summand) const
  { return _summands[summand]; }

  /** returns the summand with the given index */
  Monom      & summandAt(unsigned summand)
  { return _summands[summand]; }

  Option<Monom> tryMonom() const;

  /** integrity check of the data structure. does noly have an effect in debug mode */
  void integrity() const;

  /** returns iterator over all summands of this Polyom */
  auto iterSummands() const
  { return arrayIter(_summands); }

  Stack<Monom>& raw();

  template<class F> Polynom mapVars(F f) const;

  template<class N> friend bool operator==(const Polynom<N>& l, const Polynom<N>& r);
  template<class N> friend bool operator!=(const Polynom<N>& l, const Polynom<N>& r);
  template<class N> friend std::ostream& operator<<(std::ostream& out, const Polynom<N>& self);

  friend Polynom operator*(Numeral n, Polynom const& self) 
  { return Polynom(self.iterSummands()
      .map([&](auto m) { return n * m; })
      .template collect<Stack>()); }

  friend Polynom operator-(Polynom const& self) 
  { return Numeral(-1) * self; }
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

/** convenient constructor for IterArgsPnf */
IterTraits<IterArgsPnf> iterArgsPnf(Literal* lit);

} // namespace Kernel

// include needs to go here, since we need the specialization BottomUpChildIter<PolyNf> to declare Iter
#include "Kernel/BottomUpEvaluation.hpp"

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
Monom<Number>::Monom(Monom<Number>::Numeral numeral, Perfect<MonomFactors<Number>> factors) 
  : numeral(numeral), factors(factors)
{}


template<class Number>
template<class F>
Monom<Number> Monom<Number>::mapVars(F fun) const 
{ return Monom(numeral, perfect(factors->mapVars(fun))); }

template<class Number>
Monom<Number> Monom<Number>::zero() 
{ 
  static Monom p = Monom(Numeral(0), perfect(MonomFactors<Number>()));
  ASS(p.isZeroConst()) 
  return p; 
}

template<class Number>
bool Monom<Number>::isZeroConst() const
{ return isZeroMul() && this->factors->nFactors() == 0; }


template<class Number>
bool Monom<Number>::isZeroMul() const
{ return Numeral(0) == this->numeral; }

template<class Number>
Option<typename Monom<Number>::Numeral> Monom<Number>::tryNumeral() const 
{
  using Opt = Option<Numeral>;
  if (this->factors->isOne()) {
    return Opt(numeral);
  } else {
    return Opt();
  }
}

template<class Number>
Option<Variable> Monom<Number>::tryVar() const 
{
  using Opt = Option<Variable>;
  if (numeral == Numeral(1)) {
    return  factors->tryVar();
  } else {
    return  Opt();
  }
}

template<class Number>
void Monom<Number>::integrity() const 
{
#if VDEBUG
  this->factors->integrity();
#endif // VDEBUG
}
template<class Number>
TermList Monom<Number>::denormalize()  const
{
  return PolyNf(AnyPoly(perfect(Polynom<Number>(*this)))).denormalize(); 
}


template<class Number>
bool operator<(Kernel::Monom<Number> const& l, Kernel::Monom<Number> const& r)
{ return std::tie(l.factors, l.numeral) < std::tie(r.factors, r.numeral); }

template<class Number>
bool operator==(Kernel::Monom<Number> const& l, Kernel::Monom<Number> const& r)
{ return std::tie(l.factors, l.numeral) == std::tie(r.factors, r.numeral); }

template<class Number>
bool operator!=(Kernel::Monom<Number> const& l, Kernel::Monom<Number> const& r)
{ return !(l == r); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const Kernel::Monom<Number>& self)
{ 
#if !OUTPUT_NICE 
  out << "mon(";
#endif 
  if (self.factors->isOne()) {
    out << self.numeral;
  } else {
    if (self.numeral != typename Number::ConstantType(1))
      out << self.numeral << " ";
    out << self.factors; 
  }
#if !OUTPUT_NICE 
  out << ")";
#endif 
  return out;
}

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

template<class Number>
Option<typename Number::ConstantType> FuncTerm::tryNumeral() const
{ return _fun.template tryNumeral<Number>(); }

template<class F> FuncTerm FuncTerm::mapVars(F fun) const
{ return FuncTerm(_fun, iterTraits(_args.iterFifo())
                          .map([&](PolyNf t) { return t.mapVars(fun); })
                          .template collect<Stack>()); }

} // namespace Kernel


template<> struct std::hash<Kernel::FuncTerm> 
{
  size_t operator()(Kernel::FuncTerm const& f) const 
  { return Lib::HashUtils::combine(f._fun.defaultHash(), std::hash<Stack<Kernel::PolyNf>>{}(f._args));  }
};

/////////////////////////////////////////////////////////
// impl AnyPoly  template stuff
////////////////////////////

namespace Kernel {

template<class NumTraits>
AnyPoly::AnyPoly(Perfect<Polynom<NumTraits>> x) : Coproduct(std::move(x)) {  }

template<class NumTraits> 
Option<Perfect<Polynom<NumTraits>> const&>  AnyPoly::downcast() const& 
{ return as<Perfect<Polynom<NumTraits>>>(); }

template<class NumTraits> 
bool AnyPoly::isType() const 
{ return is<Perfect<Polynom<NumTraits>>>(); }

/* helper function for AnyPoly::tryNumeral */
template<class NumIn, class NumOut>
struct __ToNumeralHelper 
{
  Option<typename NumOut::ConstantType> operator()(Perfect<Polynom<NumIn>>) const
  { return Option<typename NumOut::ConstantType>(); }
};

/* helper function for AnyPoly::tryNumeral */
template<class Num>
struct __ToNumeralHelper<Num,Num>
{
  Option<typename Num::ConstantType> operator()(Perfect<Polynom<Num>> p) const
  { return p->toNumber(); }
};

template<class NumOut>  
struct PolymorphicToNumeral 
{
  template<class NumIn>
  Option<typename NumOut::ConstantType> operator()(Perfect<Polynom<NumIn>> const& p) const
  { return __ToNumeralHelper<NumIn, NumOut>{}(p); }
};


template<class NumTraits>
Option<typename NumTraits::ConstantType> AnyPoly::tryNumeral() const&
{ return apply(PolymorphicToNumeral<NumTraits>{}); }

template<class F> 
struct __MapVars {
  F _fun;
  template<class A> 
  AnyPoly operator()(A a) 
  { return AnyPoly(perfect(a->mapVars(_fun))); }
};

template<class F> AnyPoly AnyPoly::mapVars(F fun) const
{ return apply(__MapVars<F>{fun}); }

} // namespace Kernel

template<> struct std::hash<Kernel::AnyPoly> 
{
  size_t operator()(Kernel::AnyPoly const& self) const 
  { return std::hash<Kernel::AnyPolySuper>{}(self); }
};

/////////////////////////////////////////////////////////
// impl PolyNf  template stuff
////////////////////////////

namespace Kernel {


template<class NumTraits>
Option<Perfect<Polynom<NumTraits>>> PolyNf::downcast()  const
{
  using Result = Perfect<Polynom<NumTraits>>;
  return as<AnyPoly>()
    .andThen([](AnyPoly const& p) { return p.as<Result>(); })
    .map([](Result const& p) -> Result { return p; });
}


template<class Number> 
Perfect<Polynom<Number>> PolyNf::wrapPoly() const
{
  if (this->is<AnyPoly>()) {
    return this->unwrap<AnyPoly>()
            .unwrap<Perfect<Polynom<Number>>>();
  } else {
    return perfect(Polynom<Number>(*this));
  }
}

template<class Number> 
Monom<Number> PolyNf::wrapMonom() const
{
  return this->wrapPoly<Number>()->tryMonom() || [&]() -> Monom<Number> { return Monom<Number>(*this); };
}

template<class Number>
Option<typename Number::ConstantType> PolyNf::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  return match(
      [](Perfect<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
      [](Variable               t) { return Option<Numeral>();              },
      [](AnyPoly                t) { return t.template tryNumeral<Number>(); }
    );
}

template<class F> PolyNf PolyNf::mapVars(F fun) const
{ return match(
    [&](Perfect<FuncTerm> t) { return PolyNf(perfect(t->mapVars(fun))); },
    [&](Variable var       ) { return PolyNf(fun(var)                ); },
    [&](AnyPoly p)           { return PolyNf(p.mapVars(fun)          ); }); }

} // namespace Kernel

template<> struct std::hash<Kernel::PolyNf> 
{
  size_t operator()(Kernel::PolyNf const& f) const 
  { return std::hash<Kernel::PolyNfSuper>{}(f); }
};

/////////////////////////////////////////////////////////
// impl MonomFactor  template stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactor<Number>::MonomFactor(PolyNf term, int power) 
  : term(term)
  , power(power)
{}


template<class Number>
PolyNf::SubtermIter MonomFactor<Number>::iterSubterms() const
{ return term.iterSubterms(); }

template<class Number>
bool operator<(MonomFactor<Number> const& l, MonomFactor<Number> const& r)
{ return std::tie(l.term, l.power) < std::tie(r.term, r.power); }

template<class Number>
bool operator==(MonomFactor<Number> const& l, MonomFactor<Number> const& r)
{ return std::tie(l.term, l.power) == std::tie(r.term, r.power); }

template<class Number>
bool operator!=(MonomFactor<Number> const& l, MonomFactor<Number> const& r)
{ return !(l == r); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const MonomFactor<Number>& self) {
  out << self.term; 
  if (self.power != 1) 
    out << "^" << self.power;
  return out;
}


template<class Number>
template<class F>
MonomFactor<Number> MonomFactor<Number>::mapVars(F fun) const 
{ 
  auto mapped = this->term.template mapVars<F>(fun);
  auto poly_ = mapped.template downcast<Number>();
  if (poly_.isSome()) {
    auto poly  = poly_.unwrap();
    if (poly->nSummands() == 1 && poly->summandAt(0).numeral == Number(1)) {
      auto facs = poly->summandAt(0).factors;
      if (facs->nFactors() == 1 && facs->factorAt(0).power == 1) {
        return MonomFactor(facs->factorAt(0).term, this->power);
      }
    }
  }
  return MonomFactor(mapped, this->power); 
}

template<class Number>
Option<Variable> MonomFactor<Number>::tryVar() const 
{ return power == 1 ? term.tryVar() : none<Variable>(); }

template<class Number>
Option<Perfect<Polynom<Number>>> MonomFactor<Number>::tryPolynom() const 
{ return power == 1 ? term.downcast<Number>() : none<Perfect<Polynom<Number>>>(); }

} // namespace Kernel

template<class NumTraits>
struct std::hash<Kernel::MonomFactor<NumTraits>> 
{
  size_t operator()(Kernel::MonomFactor<NumTraits> const& x) const noexcept 
  {
    return HashUtils::combine(
      StlHash::hash(x.term),
      StlHash::hash(x.power)
    );
  }
};


/////////////////////////////////////////////////////////
// impl MonomFactors  template stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactors<Number>::MonomFactors(Stack<MonomFactor>&& factors) 
  : _factors(std::move(factors)) 
{ 
  ASS(!(
    _factors.size() == 1 
    && _factors[0].tryPolynom().isSome()
    && _factors[0].tryPolynom().unwrap()->nSummands() == 1
    && _factors[0].tryPolynom().unwrap()->summandAt(0).numeral == 1
  ))
}

template<class Number>
MonomFactors<Number>::MonomFactors() 
  : MonomFactors(decltype(_factors)()) { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t) 
  : MonomFactors( { MonomFactor ( t, 1 ) } ) { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t1, PolyNf t2) 
  : MonomFactors(t1 == t2 ? decltype(_factors) ({MonomFactor ( t1, 2 )  }) : 
                 t1 <  t2 ? decltype(_factors) ({ MonomFactor ( t1, 1 ), MonomFactor ( t2, 1 ) }) 
                          : decltype(_factors) ({ MonomFactor ( t2, 1 ), MonomFactor ( t1, 1 ) }) 
                            )  { }

template<class Number>
unsigned MonomFactors<Number>::nFactors() const 
{ return _factors.size(); }

template<class Number>
MonomFactor<Number> & MonomFactors<Number>::factorAt(unsigned i) 
{ return _factors[i]; }

template<class Number>
MonomFactor<Number> const& MonomFactors<Number>::factorAt(unsigned i) const
{ return _factors[i]; }

template<class Number>
PolyNf const& MonomFactors<Number>::termAt(unsigned i) const
{ return _factors[i].term; }


template<class Number>
template<class F>
MonomFactors<Number> MonomFactors<Number>::mapVars(F fun) const 
{ return MonomFactors(
        iterTraits(_factors.iterFifo()) 
          .map([&](MonomFactor const& fac) { return fac.mapVars(fun); })
          .template collect<Stack>()); }

template<class Number>
Stack<MonomFactor<Number>> & MonomFactors<Number>::raw()
{ return _factors; }

template<class Number>
bool MonomFactors<Number>::isPolynom() const
{ return nFactors() == 1 
    && _factors[0].power == 1 
    && _factors[0].term.template is<AnyPoly>(); }

template<class Number>
Perfect<Polynom<Number>> MonomFactors<Number>::asPolynom() const
{ 
  ASS(isPolynom());
  return _factors[0].term
    .template unwrap<AnyPoly>()
    .template unwrap<Perfect<Polynom>>(); 
}

template<class Number>
MonomFactors<Number> MonomFactors<Number>::one()
{ return MonomFactors(); }

template<class Number>
bool MonomFactors<Number>::isOne() const 
{ return _factors.begin() == _factors.end(); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const MonomFactors<Number>& self) 
{
  if (self._factors.size() == 0) {
    out << "1";
  } else {
    auto iter  = self._factors.begin();
    auto write = [&](MonomFactor<Number> const& f) { 
      if (f.tryPolynom().isSome()) 
        out << "(" << f << ")";
      else out << f;
    };
    write(*iter);
    iter++;
    for (; iter != self._factors.end(); iter++) {
      out << " ";
      write(*iter);
    }
  }
  return out;
}


template<class Number>
bool operator==(const MonomFactors<Number>& l, const MonomFactors<Number>& r) {
  return l._factors == r._factors;
}

template<class Number>
TermList MonomFactors<Number>::denormalize()  const
{
  return PolyNf(AnyPoly(perfect(Polynom(Monom(MonomFactors(*this)))))).denormalize(); 
}

template<class Number>
TermList MonomFactors<Number>::denormalize(TermList* results)  const
{
  if (_factors.size() == 0) {
    return Number::one();
  } else {

    auto prependPowerTerm = [](TermList t, int pow, TermList tail) -> TermList {
      TermList out = tail;
      for (int i = 0; i < pow; i++) {
        out = Number::mul(t,out);
      }
      return out;
    };

    auto end = nFactors() - 1;
    ASS(_factors[end].power > 0)
    TermList out = prependPowerTerm(results[end], _factors[end].power - 1, results[end]);

    for (unsigned i = 1; i < nFactors(); i++) {
      out = prependPowerTerm(results[end - i], _factors[end - i].power, out);
    }

    return out;
  }
}

template<class Number>
Option<Variable> MonomFactors<Number>::tryVar() const 
{
  using Opt = Option<Variable>;
  if (nFactors() == 1 ) {

    return _factors[0].tryVar();
  } else {
    return  Opt();
  }
}

template<class Number>
void MonomFactors<Number>::integrity() const 
{
#if VDEBUG
  if (_factors.size() == 1) {
    auto fac = _factors[0];
    if (fac.isPolynom()) {
      auto poly = fac.tryPolynom().unwrap();
      if (poly->nSummands() == 1) {
        auto sum = poly->summandAt(0);
        if (sum.numeral == Numeral(1)) {
          ASSERTION_VIOLATION_REP(*this)
        }
      }
    }
  }
  for (auto const& x : _factors)
    x.integrity();

  if (_factors.size() > 0) {
    auto iter = this->_factors.begin();
    auto last = iter++;
    while (iter != _factors.end()) {
      ASS_REP(last->term <= iter->term, *this);
      last = iter++;
    }
  }
#endif
}

template<class Number>
MonomFactors<Number> MonomFactors<Number>::replaceTerms(PolyNf* simplifiedTerms) const 
{
  int offs = 0;
  MonomFactors out;
  out._factors.reserve(nFactors());

  for (auto& fac : _factors) {
    out._factors.push(MonomFactor(simplifiedTerms[offs++], fac.power));
  }

  return out;
}

template<class Number>
auto MonomFactors<Number>::iterSubterms() const
{ return iter().flatMap([](auto fac) { return fac.iterSubterms(); }); }

} // namespace Kernel

template<class NumTraits>
struct std::hash<Kernel::MonomFactors<NumTraits>> 
{
  size_t operator()(Kernel::MonomFactors<NumTraits> const& x) const noexcept 
  {
    return StackHash<StlHash>::hash(x._factors);
  }
};


/////////////////////////////////////////////////////////
// impl Polynom template stuff
////////////////////////////

namespace Kernel {


template<class Number>
Polynom<Number>::Polynom(Stack<Monom>&& summands) 
  : _summands(
      summands.isEmpty() 
        ? Stack<Monom>{Monom::zero()} 
        : std::move(summands)) 
{ /* integrity(); */ }

template<class Number>
Polynom<Number>::Polynom(Monom m) 
  : Polynom(
      Stack<Monom>{m})
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral numeral, PolyNf term) 
  : Polynom(Monom(numeral, perfect(MonomFactors(term))))
{  }

template<class Number>
Polynom<Number>::Polynom(PolyNf t) 
  : Polynom(Numeral(1), t) 
{ integrity();  }

template<class Number>
Polynom<Number>::Polynom(Numeral constant) 
  : Polynom(Monom(constant, perfect(MonomFactors::one()))) 
{  }


template<class Number>
bool operator==(const Polynom<Number>& lhs, const Polynom<Number>& rhs)
{ return std::tie(lhs._summands) == std::tie(rhs._summands); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const Polynom<Number>& self) {
#if !OUTPUT_NICE 
  out << "poly(";
#endif 
  auto iter = self._summands.begin();
  if ( iter == self._summands.end() ) {
    out << "0";
  } else {
    out << *iter;
    iter++;
    for (; iter != self._summands.end(); iter++) {
      out << " + " << *iter;
    }
  }
#if !OUTPUT_NICE 
  out << ")";
#endif 
  return out;
}



template<class Number>
Polynom<Number> Polynom<Number>::zero() 
{ 
  auto out = Polynom(Stack<Monom>{Monom::zero()}); 
  out.integrity();
  return std::move(out);
}

template<class Number>
Option<typename Number::ConstantType> Polynom<Number>::toNumber() const& 
{ 
  if ( _summands.size() == 0) {
    return Option<Numeral>(Numeral(0));

  } else if (_summands.size() == 1 && _summands[0].factors->nFactors() == 0) {
    return Option<Numeral>(_summands[0].numeral);

  } else {
    return Option<Numeral>();
  }
}

template<class Number>
bool Polynom<Number>::isNumber() const& 
{ 
  return toNumber().isSome();
}

template<class Number>
template<class F>
Polynom<Number> Polynom<Number>::mapVars(F fun) const
{ return Polynom(iterTraits(_summands.iterFifo())
                  .map([&](Monom const& m) { return m.mapVars(fun); })
                  .template collect<Stack>());                       }

template<class Number>
typename Number::ConstantType Polynom<Number>::unwrapNumber() const& 
{ return toNumber().unwrap(); }

template<class Number>
TermList Polynom<Number>::denormalize(TermList* results) const
{
  auto monomToTerm = [](Monom const& monom, TermList* t) -> TermList {
      auto mon = monom.factors->denormalize(t);
      if (monom.factors->nFactors() == 0) {
        return AlascaSignature<Number>::numeralTl(monom.numeral);
      } else if (monom.numeral == 1) {
        return mon;
      } else {
        return Number::linMul(monom.numeral, mon);
      }
  };

  if (_summands.size() == 0) {
    return AlascaSignature<Number>::numeralTl(Numeral(0));
  } else {

    auto flatSize = iterTraits(_summands.iterFifo())
      .map([](Monom const& m) { return m.factors->nFactors(); })
      .sum();

    auto flatIdx =  flatSize - _summands.top().factors->nFactors();
    TermList out = monomToTerm(_summands.top(), &results[flatIdx]);

    for (unsigned i = 1; i < nSummands(); i++) {
      auto idx = _summands.size() - i - 1 ;
      auto& monom = _summands[idx];
      flatIdx -= monom.factors->nFactors();
      out = Number::add(monomToTerm(monom, &results[flatIdx]), out);
    }
    return out;
  }
}

template<class Number>
Stack<Monom<Number>>& Polynom<Number>::raw()
{ return _summands; }

template<class Number>
Polynom<Number> Polynom<Number>::replaceTerms(PolyNf* simplifiedTerms) const 
{
  int offs = 0;
  Stack<Monom> out;
  out.reserve(nSummands());

  for (auto& monom : _summands) {
    out.push(Monom(
          monom.numeral, 
          perfect(monom.factors->replaceTerms(&simplifiedTerms[offs]))));
    offs += monom.factors->nFactors();
  }
  return Polynom(std::move(out));
}


template<class Number>
unsigned Polynom<Number>::nSummands() const
{ return _summands.size(); }

template<class Number>
unsigned Polynom<Number>::nFactors(unsigned summand) const
{ return _summands[summand].factors->nFactors(); }


template<class Number>
void Polynom<Number>::integrity() const {
#if VDEBUG
  ASS(_summands.size() > 0)
  for (auto const& x : _summands)
    x.integrity();
  if (_summands.size() > 0) {
    auto iter = this->_summands.begin();
    auto last = iter++;
    while (iter != _summands.end()) {
      ASS_REP(last->factors <= iter->factors, *this);
      last = iter++;
    }
  } 
#endif
}

template<class Number>
Option<Monom<Number>> Polynom<Number>::tryMonom() const
{ return someIf(_summands.size() == 1, [&](){ return summandAt(0); }); }

template<class Number> 
TermList Polynom<Number>::denormalize()  const
{ return PolyNf(AnyPoly(perfect(Polynom(*this)))).denormalize(); }

} // namespace Kernel

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
        StlHash::hash(c.factors),
        StlHash::hash(c.numeral),
        out
      );
    }
    return out;
  }
};


#undef DEBUG
#endif // __POLYNOMIAL__H__

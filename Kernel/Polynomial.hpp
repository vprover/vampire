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

#include "Lib/STLAllocator.hpp"
#include "Kernel/NumTraits.hpp"
#include <cassert>
#include "Lib/Coproduct.hpp"
#include "Lib/Option.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Perfect.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include <type_traits>
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TypedTermList.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {

// TODO use this newtype in Term.hpp
/** newtype for wrapping varible ids */
class Variable 
{
  unsigned _num;
public: 
  Variable();
  explicit Variable(unsigned num);
  unsigned id() const;

  friend struct std::hash<Variable>;
  friend bool operator==(Variable lhs, Variable rhs);
  friend bool operator!=(Variable lhs, Variable rhs);
  friend bool operator<(Variable const& lhs, Variable const& rhs);
  friend std::ostream& operator<<(std::ostream& out, const Variable& self);
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
  
public: 
  explicit FuncId(unsigned num);
  unsigned arity();

  friend struct std::hash<FuncId>;
  friend bool operator==(FuncId const& lhs, FuncId const& rhs);
  friend bool operator!=(FuncId const& lhs, FuncId const& rhs);
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


template<> struct std::hash<Kernel::FuncId> 
{
  size_t operator()(Kernel::FuncId const& f) const 
  { return std::hash<unsigned>{}(f._num); }
};


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

/** 
 * Represents a summand in a polynom of the number type Number 
 * e.g. a term like 3 * (a*x) would be represented as 
 * Monom { 3, MonomFactors { a, x }}
 */
template<class Number> 
struct Monom 
{
  CLASS_NAME(MonomFactor)

  using Numeral = typename Number::ConstantType;

  Numeral numeral;
  Perfect<MonomFactors<Number>> factors;

  Monom(Numeral numeral, Perfect<MonomFactors<Number>> factors);

  static Monom zero();

  Option<Variable> tryVar() const;
};


/**
 * Represents an ordenary complex term, in the PolyNF term tree.
 */
class FuncTerm 
{
  FuncId _fun;
  Stack<PolyNf> _args;
public:
  FuncTerm(FuncId f, Stack<PolyNf>&& args);
  FuncTerm(FuncId f, PolyNf* args);

  unsigned arity() const;
  FuncId function() const;
  PolyNf const& arg(unsigned i) const;

  template<class Number> 
  Option<typename Number::ConstantType> tryNumeral() const;

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
  template<class NumTraits> Option<Perfect<Polynom<NumTraits>> const&> downcast() const&;
  template<class NumTraits> bool isType() const;
  template<class NumTraits> Option<typename NumTraits::ConstantType> tryNumeral() const&;

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self);
  friend struct std::hash<AnyPoly>;

  AnyPoly replaceTerms(PolyNf* newTs) const;
  unsigned nSummands() const;
  unsigned nFactors(unsigned i) const;
  PolyNf const& termAt(unsigned summand, unsigned factor) const;
  TermList denormalize(TermList* results) const;
};

using PolyNfSuper = Lib::Coproduct<Perfect<FuncTerm>, Variable, AnyPoly>;

/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * See the file-level documentation for how this datatype is composed.
 */
class PolyNf : public PolyNfSuper
{
public:
  CLASS_NAME(PolyNf)

  PolyNf(Perfect<FuncTerm> t);
  PolyNf(Variable               t);
  PolyNf(AnyPoly                t);

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
  

  /** if this PolyNf is a numeral, the numeral is returned */
  template<class Number>
  Option<typename Number::ConstantType> tryNumeral() const;

  /** if this PolyNf is a Variable, the variable is returned */
  Option<Variable> tryVar() const;

  /** an iterator over all PolyNf s that are subterms of this one */
  class IterSubterms;

  /** returns an iterator over all PolyNf s that are subterms of this one */
  IterTraits<IterSubterms> iterSubterms() const;

  friend struct std::hash<PolyNf>;
  friend bool operator==(PolyNf const& lhs, PolyNf const& rhs);
  friend bool operator!=(PolyNf const& lhs, PolyNf const& rhs);
  friend bool operator<(const PolyNf& lhs, const PolyNf& rhs);
  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self);
};


/** 
 * Represents a factor in a monom. Each unique term contained in the monom is stored 
 * together with the number of occurences of the term within that monom.
 *
 * e.g. a term like (x * x * a * x) is represented as 
 * MonomFactors { MonomFactor(x, 3), MonomFactor(a, 1) }
 */
template<class Number> 
struct MonomFactor 
{
  CLASS_NAME(MonomFactor)
  PolyNf term;
  int power;

  MonomFactor(PolyNf term, int power);
   
  /** if this monomfactor is a Variable and has power one it is turned into a variable */
  Option<Variable> tryVar() const;
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


  /** if this MonomFactors consist of a single variable if will be returnd  */
  Option<Variable> tryVar() const;

  /** performs an integrity check on the datastructure, only has an effect in debug mode */
  void integrity() const;

  /** replaces all the factors, by new ones, keeping the power of each term the same  */
  MonomFactors replaceTerms(PolyNf* simplifiedTerms) const;


  /** an iterator over all factors */
  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_factors)>::type, no_ref_t>>;

  /** returns an iterator over all factors */
  ConstIter iterFactors() const&;

  explicit MonomFactors(const MonomFactors&) = default;
  explicit MonomFactors(MonomFactors&) = default;

  MonomFactors& operator=(MonomFactors&&) = default;
  MonomFactors(MonomFactors&&) = default;

  template<class N> friend std::ostream& operator<<(std::ostream& out, const MonomFactors<N>& self);
  template<class N> friend bool operator==(const MonomFactors<N>& l, const MonomFactors<N>& r);

  /** helper function for PolyNf::denormalize() */
  TermList denormalize(TermList* results)  const;
};

template<class Number>
class Polynom 
{
  friend struct std::hash<Polynom>;

  using Numeral      = typename Number::ConstantType;
  using MonomFactors = Kernel::MonomFactors<Number>;
  using Monom        = Kernel::Monom<Number>;

  Stack<Monom> _summands;

public:
  USE_ALLOCATOR(Polynom)
  CLASS_NAME(Polynom)

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

  /** creates the empty Polynom that is interpreted as zero */
  static Polynom zero();

  /* if this Polynom consists only of one summand that is a numeral the numeral is returned */
  Option<Numeral> toNumber() const&;

  /* turns this Polynom into a numeral if it consists only of one summand that is a numeral, or throws an assertion violation 
   * \pre isNumeral is true*
   */
  Numeral unwrapNumber() const&;

  /* returns whether this Monom consists of only one summand that is a numeral */
  bool isNumber() const&;

  // TODO continue here
  struct CancelAdd {
    Polynom lhs;
    Polynom rhs;
  };

  static CancelAdd cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr);

  TermList denormalize() const;

  TermList denormalize(TermList* results) const;

  Polynom flipSign() const;

  Polynom replaceTerms(PolyNf* simplifiedTerms) const;

  unsigned nSummands() const;

  unsigned nFactors(unsigned summand) const;

  Monom summandAt(unsigned summand) const;

  void integrity() const;

  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_summands)>::type, no_ref_t>>;

  ConstIter iter() const&;

  template<class N> friend bool operator==(const Polynom<N>& lhs, const Polynom<N>& rhs);
  template<class N> friend std::ostream& operator<<(std::ostream& out, const Polynom<N>& self);
};

} // namespace Kernel

// include needs to go here, since we need the specialization BottomUpChildIter<PolyNf> to declare Iter
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

namespace Kernel {

class PolyNf::IterSubterms {
  Stack<BottomUpChildIter<PolyNf>> _stack;
public:
  DECL_ELEMENT_TYPE(PolyNf);

  IterSubterms(IterSubterms&&) = default;
  IterSubterms& operator=(IterSubterms&&) = default;

  IterSubterms(PolyNf p);

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
Monom<Number> Monom<Number>::zero() 
{ 
  static Monom p = Monom(Numeral(0), perfect(MonomFactors<Number>()));
  return p; 
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
bool operator<(Monom<Number> const& l, Monom<Number> const& r)
{ return std::tie(l.factors, l.numeral) < std::tie(r.factors, r.numeral); }

template<class Number>
bool operator==(Monom<Number> const& l, Monom<Number> const& r)
{ return std::tie(l.factors, l.numeral) == std::tie(r.factors, r.numeral); }

template<class Number>
bool operator!=(Monom<Number> const& l, Monom<Number> const& r)
{ return !(l == r); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const Monom<Number>& self)
{ 
  if (self.numeral != typename Number::ConstantType(1)) {
    out << self.numeral;
  }
  return out << self.factors; 
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

} // namespace Kernel


template<> struct std::hash<Kernel::FuncTerm> 
{
  size_t operator()(Kernel::FuncTerm const& f) const 
  { return Lib::HashUtils::combine(std::hash<Kernel::FuncId>{}(f._fun), std::hash<Stack<Kernel::PolyNf>>{}(f._args));  }
};

/////////////////////////////////////////////////////////
// impl AnyPoly  template stuff
////////////////////////////

namespace Kernel {

POLYMORPHIC_FUNCTION(TermList, denormalize   , const& t, TermList* results; ) { return t->denormalize(results); }
POLYMORPHIC_FUNCTION(unsigned, nSummands, const& t,            ) { return t->nSummands(); }
POLYMORPHIC_FUNCTION(unsigned, nFactors , const& t, unsigned i;) { return t->nFactors(i); }
POLYMORPHIC_FUNCTION(ostream&, outputOp , const& t, ostream& o;) { return o << t; }
POLYMORPHIC_FUNCTION(PolyNf const&, termAt   , const& t, unsigned summand; unsigned factor;) { return t->summandAt(summand).factors->termAt(factor); }
  
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
Option<typename Number::ConstantType> PolyNf::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  return match(
      [](Perfect<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
      [](Variable               t) { return Option<Numeral>();              },
      [](AnyPoly                t) { return t.template tryNumeral<Number>(); }
    );
}

} // namespace Kernel

template<> struct std::hash<Kernel::PolyNf> 
{
  size_t operator()(Kernel::PolyNf const& f) const 
  { return std::hash<Kernel::PolyNfSuper>{}(f); }
};

/////////////////////////////////////////////////////////
// impl MonomFactor  tempalte stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactor<Number>::MonomFactor(PolyNf term, int power) 
  : term(term)
  , power(power)
{}

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
Option<Variable> MonomFactor<Number>::tryVar() const 
{ return power == 1 ? term.tryVar() : none<Variable>(); }

} // namespace Kernel

template<class NumTraits>
struct std::hash<Kernel::MonomFactor<NumTraits>> 
{
  size_t operator()(Kernel::MonomFactor<NumTraits> const& x) const noexcept 
  {
    using namespace Lib;
    using namespace Kernel;

    return HashUtils::combine(stlHash(x.term), stlHash(x.power));
  }
};


/////////////////////////////////////////////////////////
// impl MonomFactors  tempalte stuff
////////////////////////////

namespace Kernel {

template<class Number>
MonomFactors<Number>::MonomFactors(Stack<MonomFactor>&& factors) 
  : _factors(std::move(factors)) { }

template<class Number>
MonomFactors<Number>::MonomFactors() 
  : MonomFactors(decltype(_factors)()) { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t) 
  : _factors { MonomFactor ( t, 1 ) }  { }

template<class Number>
MonomFactors<Number>::MonomFactors(PolyNf t1, PolyNf t2) 
  : _factors(t1 == t2 ? decltype(_factors) ({MonomFactor ( t1, 2 )  }) : 
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
  out << "(";
  if (self._factors.size() == 0) {
    out << "MonomFactors()";
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


template<class Number>
bool operator==(const MonomFactors<Number>& l, const MonomFactors<Number>& r) {
  return l._factors == r._factors;
}

template<class Number>
TermList MonomFactors<Number>::denormalize(TermList* results)  const
{
  CALL("MonomFactors::denormalize()")

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

template<class Number>
MonomFactors<Number> MonomFactors<Number>::replaceTerms(PolyNf* simplifiedTerms) const 
{
  int offs = 0;
  MonomFactors out;
  out._factors.reserve(nFactors());

  for (auto& fac : _factors) {
    out._factors.push(MonomFactor(simplifiedTerms[offs++], fac.power));
  }

  return std::move(out);
}

template<class Number>
typename MonomFactors<Number>::ConstIter MonomFactors<Number>::iterFactors() const&
{ return iterTraits(getArrayishObjectIterator<no_ref_t>(_factors)); }

} // namespace Kernel

template<class NumTraits>
struct std::hash<Kernel::MonomFactors<NumTraits>> 
{
  size_t operator()(Kernel::MonomFactors<NumTraits> const& x) const noexcept 
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


/////////////////////////////////////////////////////////
// impl Polynom tempalte stuff
////////////////////////////

namespace Kernel {


template<class Number>
Polynom<Number>::Polynom(Stack<Monom>&& summands) 
  : _summands(
      summands.isEmpty() 
        ? Stack<Monom>{Monom::zero()} 
        : std::move(summands)) 
{ }

template<class Number>
Polynom<Number>::Polynom(Monom m) 
  : Polynom(
      m.numeral == Numeral(0)
        ? Stack<Monom>() 
        : Stack<Monom> {  m  }) 
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral numeral, PolyNf term) 
  : Polynom(Monom(numeral, perfect(MonomFactors(term))))
{  }

template<class Number>
Polynom<Number>::Polynom(PolyNf t) 
  : Polynom(Numeral(1), t) 
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral constant) 
  : Polynom(Monom(constant, perfect(MonomFactors::one()))) 
{  }


template<class Number>
bool operator==(const Polynom<Number>& lhs, const Polynom<Number>& rhs)
{ return std::tie(lhs._summands) == std::tie(rhs._summands); }

template<class Number>
std::ostream& operator<<(std::ostream& out, const Polynom<Number>& self) {
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



template<class Number>
Polynom<Number> Polynom<Number>::zero() 
{ return Polynom(Stack<Monom>{}); }

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
typename Number::ConstantType Polynom<Number>::unwrapNumber() const& 
{ return toNumber().unwrap(); }

template<class Number>
typename Polynom<Number>::CancelAdd Polynom<Number>::cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr) 
{
  CALL("Polynom::cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr)")
  DEBUG("in:  ", oldl, " <> ", oldr)

  using NumeralVec = Stack<Monom>;
  // auto zero = Number::zeroC;
  auto itl = oldl._summands.begin();
  auto itr = oldr._summands.begin();
  auto endl = oldl._summands.end();
  auto endr = oldr._summands.end();

  auto safeMinus = [](Numeral l, Numeral r) 
  { 
    try {
      return Option<Numeral>(l - r);
    } catch (MachineArithmeticException) 
    {
      return Option<Numeral>();
    }
  };

  auto push = [](NumeralVec& vec, Perfect<MonomFactors> m, Numeral c) 
  { vec.push(Monom(c, m)); };

  auto cmpPrecedence = [](Option<Numeral> lOpt, Numeral r) 
  { 
    if (lOpt.isNone()) return false;
    auto l = lOpt.unwrap();
    return Numeral::comparePrecedence(l,r) == Comparison::LESS;
  };

  NumeralVec newl;
  NumeralVec newr;
  while(itl != endl && itr !=  endr) {
    auto cl = itl->numeral;
    auto cr = itr->numeral;
    const Perfect<MonomFactors>& ml = itl->factors;
    const Perfect<MonomFactors>& mr = itr->factors;
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
    push(newl, itl->factors, itl->numeral);
  }
  for(; itr != endr; itr++) {
    push(newr, itr->factors, itr->numeral);
  }
  auto outl = Polynom<Number>(std::move(newl));
  auto outr = Polynom<Number>(std::move(newr));
  DEBUG("out: ", outl, " <> ", outr)
  return CancelAdd { 
    .lhs = std::move(outl), 
    .rhs = std::move(outr), 
  };
}

template<class Number>
TermList Polynom<Number>::denormalize(TermList* results) const
{
  CALL("Polynom::denormalize()")

  auto monomToTerm = [](Monom const& monom, TermList* t) -> TermList {
    auto c = TermList(theory->representConstant(monom.numeral));
    if (monom.factors->isOne()) {
      return c;
    } else {
      auto mon = monom.factors->denormalize(t);
      if (monom.numeral == Number::oneC) {
        return mon;
      } else if (monom.numeral == Number::constant(-1)) {
        return Number::minus(mon);
      } else {
        return Number::mul(c, mon);
      }
    }
  };

  if (_summands.size() == 0) {
    return Number::zero();
  } else {

    TermList out = monomToTerm(_summands[0], results);
    auto flatIdx = _summands[0].factors->nFactors();

    for (unsigned i = 1; i < nSummands(); i++) {
      auto& monom = _summands[i];
      out = Number::add(monomToTerm(monom, &results[flatIdx]), out);
      flatIdx += monom.factors->nFactors();
    }
    return out;
  }
}

template<class Number>
Polynom<Number> Polynom<Number>::flipSign() const
{ 
  CALL("Polynom::flipSign() const") 
  Polynom out(*this);
  for (unsigned i = 0; i < nSummands(); i++) {
    out._summands[i].numeral = out._summands[i].numeral * Numeral(-1);
  }
  return std::move(out);
}

template<class Number>
Polynom<Number> Polynom<Number>::replaceTerms(PolyNf* simplifiedTerms) const 
{
  CALL("Polynom::replaceTerms(PolyNf*)")
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
Monom<Number> Polynom<Number>::summandAt(unsigned summand) const
{ return _summands[summand]; }

template<class Number>
void Polynom<Number>::integrity() const {
#if VDEBUG
  if (_summands.size() > 0) {
    auto iter = this->_summands.begin();
    auto last = iter++;
    while (iter != _summands.end()) {
      ASS_REP(std::less<Perfect<MonomFactors>>{}(last->factors, iter->factors), *this);
      iter->factors->integrity();
      last = iter++;
    }
  }
#endif
}

template<class Number>
typename Polynom<Number>::ConstIter Polynom<Number>::iter() const&
{ return iterTraits(getArrayishObjectIterator<no_ref_t>(_summands)); }


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
              stlHash(c.factors),
              stlHash(c.numeral),
              out);
    }
    return out;
  }
};

// TODO Option -> Option

#undef DEBUG
#endif // __POLYNOMIAL__H__

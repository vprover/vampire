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
#include "Lib/Optional.hpp"
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
  Optional<Theory::Interpretation> tryInterpret() const;

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const;
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

  Optional<Variable> tryVar() const;
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
  Optional<typename Number::ConstantType> tryNumeral() const;

  friend std::ostream& operator<<(std::ostream& out, const FuncTerm& self);
  friend bool operator==(FuncTerm const& lhs, FuncTerm const& rhs);
  friend bool operator!=(FuncTerm const& lhs, FuncTerm const& rhs);
  friend struct std::hash<FuncTerm>;
};

POLYMORPHIC_FUNCTION(TermList, toTerm   , const& t, TermList* results; ) { return t->toTerm(results); }
POLYMORPHIC_FUNCTION(unsigned, nSummands, const& t,            ) { return t->nSummands(); }
POLYMORPHIC_FUNCTION(unsigned, nFactors , const& t, unsigned i;) { return t->nFactors(i); }
POLYMORPHIC_FUNCTION(ostream&, outputOp , const& t, ostream& o;) { return o << t; }
POLYMORPHIC_FUNCTION(PolyNf const&, termAt   , const& t, unsigned summand; unsigned factor;) { return t->summandAt(summand).factors->termAt(factor); }

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
  template<class NumTraits> Optional<Perfect<Polynom<NumTraits>> const&> downcast() const&;
  template<class NumTraits> bool isType() const;
  template<class NumTraits> Optional<typename NumTraits::ConstantType> tryNumeral() const&;

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self);
  friend struct std::hash<AnyPoly>;

  AnyPoly replaceTerms(PolyNf* newTs) const;
  unsigned nSummands() const;
  unsigned nFactors(unsigned i) const;
  PolyNf const& termAt(unsigned summand, unsigned factor) const;
  TermList toTerm(TermList* results) const;
};

using PolyNfSuper = Lib::Coproduct<Perfect<FuncTerm>, Variable, AnyPoly>;

/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * See the file-level documentation for how this datatype is composed
 */
class PolyNf : public PolyNfSuper
{
public:
  CLASS_NAME(PolyNf)

  PolyNf(Perfect<FuncTerm> t);
  PolyNf(Variable               t);
  PolyNf(AnyPoly                t);

  static PolyNf normalize(TypedTermList t);

  template<class NumTraits>
  Optional<Perfect<Polynom<NumTraits>>> downcast() const;

  TermList toTerm() const;

  /** turns this PolyNf term into a typed polynom of sort Number.
   * this must have the same sort as Number. 
   * If this is already a polynom it will just be downcasted, 
   * otherwise (when it is a Variable, or a FuncTerm) it will be 
   * wrapped in a polynom.
   */
  template<class Number> 
  Perfect<Polynom<Number>> wrapPoly() const;
  

  template<class Number>
  Optional<typename Number::ConstantType> tryNumeral() const;

  Optional<Variable> tryVar() const;

  class Iter;
  IterTraits<Iter> iter() const;

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
struct MonomFactor {
  CLASS_NAME(MonomFactor)
  PolyNf term;
  int power;

  MonomFactor(PolyNf term, int power);

  Optional<Variable> tryVar() const;
};



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

  MonomFactors(Stack<MonomFactor>&& factors);
  MonomFactors();
  MonomFactors(PolyNf t);
  MonomFactors(PolyNf t1, PolyNf t2);

  explicit MonomFactors(const MonomFactors&) = default;
  explicit MonomFactors(MonomFactors&) = default;

  MonomFactors& operator=(MonomFactors&&) = default;
  MonomFactors(MonomFactors&&) = default;

  template<class N> friend std::ostream& operator<<(std::ostream& out, const MonomFactors<N>& self);
  template<class N> friend bool operator==(const MonomFactors<N>& l, const MonomFactors<N>& r);


  unsigned nFactors() const;
  MonomFactor      & factorAt(unsigned i);
  MonomFactor const& factorAt(unsigned i) const;
  PolyNf const& termAt(unsigned i) const;
  bool isPolynom() const;
  Perfect<Polynom> asPolynom() const;

  static MonomFactors one();

  bool isOne() const;
  // friend class Kernel::Polynom<Number>;

  TermList toTerm(TermList* results)  const;

  Optional<Variable> tryVar() const;
  

  void integrity() const;

  MonomFactors replaceTerms(PolyNf* simplifiedTerms) const;

  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_factors)>::type, no_ref_t>>;
  ConstIter iter() const&;
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

  Polynom(Stack<Monom>&& summands);
  Polynom(Numeral numeral, Perfect<MonomFactors> term);
  Polynom(Numeral numeral, PolyNf term);
  Polynom(PolyNf t);
  explicit Polynom(Numeral constant);

  template<class N> friend bool operator==(const Polynom<N>& lhs, const Polynom<N>& rhs);
  template<class N> friend std::ostream& operator<<(std::ostream& out, const Polynom<N>& self);


  static Polynom zero();

  Optional<Numeral> toNumber() const&;

  bool isNumber() const&;

  Numeral unwrapNumber() const&;

  struct CancelAdd {
    Polynom lhs;
    Polynom rhs;
  };

  static CancelAdd cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr);

  TermList toTerm() const;

  TermList toTerm(TermList* results) const;

  Polynom flipSign() const;

  Polynom replaceTerms(PolyNf* simplifiedTerms) const;

  unsigned nSummands() const;

  unsigned nFactors(unsigned summand) const;

  Monom summandAt(unsigned summand) const;

  void integrity() const;

  using ConstIter = IterTraits<ArrayishObjectIterator<typename std::remove_reference<decltype(_summands)>::type, no_ref_t>>;

  ConstIter iter() const&;
};

} // namespace Kernel

// include needs to go here, since we need the specialization BottomUpChildIter<PolyNf> to declare Iter
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

namespace Kernel {

class PolyNf::Iter {
  Stack<BottomUpChildIter<PolyNf>> _stack;
public:
  DECL_ELEMENT_TYPE(PolyNf);

  Iter(Iter&&) = default;
  Iter& operator=(Iter&&) = default;

  Iter(PolyNf p);

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
Optional<Variable> Monom<Number>::tryVar() const 
{
  using Opt = Optional<Variable>;
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
Optional<typename Number::ConstantType> FuncId::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  Numeral out;
  if (theory->tryInterpretConstant(_num, out)) {
    return Optional<Numeral>(out);
  } else {
    return Optional<Numeral>();
  }
}

} // namespace Kernel


/////////////////////////////////////////////////////////
// impl FuncTerm template stuff
////////////////////////////


namespace Kernel {

template<class Number>
Optional<typename Number::ConstantType> FuncTerm::tryNumeral() const
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
  
template<class NumTraits>
AnyPoly::AnyPoly(Perfect<Polynom<NumTraits>> x) : Coproduct(std::move(x)) {  }

template<class NumTraits> 
Optional<Perfect<Polynom<NumTraits>> const&>  AnyPoly::downcast() const& 
{ return as<Perfect<Polynom<NumTraits>>>(); }

// template<class NumTraits> 
// Perfect<Polynom<NumTraits>> AnyPoly::unwrapType() const& 
// { return unwrap<Perfect<Polynom<NumTraits>>>(); }

template<class NumTraits> 
bool AnyPoly::isType() const 
{ return is<Perfect<Polynom<NumTraits>>>(); }

/* helper function for AnyPoly::tryNumeral */
template<class NumIn, class NumOut>
struct __ToNumeralHelper 
{
  Optional<typename NumOut::ConstantType> operator()(Perfect<Polynom<NumIn>>) const
  { return Optional<typename NumOut::ConstantType>(); }
};

/* helper function for AnyPoly::tryNumeral */
template<class Num>
struct __ToNumeralHelper<Num,Num>
{
  Optional<typename Num::ConstantType> operator()(Perfect<Polynom<Num>> p) const
  { return p->toNumber(); }
};

template<class NumOut>  
struct PolymorphicToNumeral 
{
  template<class NumIn>
  Optional<typename NumOut::ConstantType> operator()(Perfect<Polynom<NumIn>> const& p) const
  { return __ToNumeralHelper<NumIn, NumOut>{}(p); }
};


template<class NumTraits>
Optional<typename NumTraits::ConstantType> AnyPoly::tryNumeral() const&
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
Optional<Perfect<Polynom<NumTraits>>> PolyNf::downcast()  const
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
Optional<typename Number::ConstantType> PolyNf::tryNumeral() const
{ 
  using Numeral = typename Number::ConstantType;
  return match(
      [](Perfect<FuncTerm> t) { return (*t).tryNumeral<Number>(); },
      [](Variable               t) { return Optional<Numeral>();              },
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
Optional<Variable> MonomFactor<Number>::tryVar() const 
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
TermList MonomFactors<Number>::toTerm(TermList* results)  const
{
  CALL("MonomFactors::toTerm()")

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
Optional<Variable> MonomFactors<Number>::tryVar() const 
{
  using Opt = Optional<Variable>;
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
typename MonomFactors<Number>::ConstIter MonomFactors<Number>::iter() const&
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
Polynom<Number>::Polynom(Numeral numeral, Perfect<MonomFactors> term) 
  : Polynom(
      numeral == Numeral(0)
        ? Stack<Monom>() 
        : Stack<Monom> {  Monom(numeral, term)  }) 
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral numeral, PolyNf term) 
  : Polynom(numeral, perfect(MonomFactors(term))) 
{  }

template<class Number>
Polynom<Number>::Polynom(PolyNf t) 
  : Polynom(Numeral(1), t) 
{  }

template<class Number>
Polynom<Number>::Polynom(Numeral constant) 
  : Polynom(constant, perfect(MonomFactors::one())) 
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
Optional<typename Number::ConstantType> Polynom<Number>::toNumber() const& 
{ 
  if (isNumber()) {
    return Optional<Numeral>(unwrapNumber());
  } else {
    return Optional<Numeral>();
  }
}

template<class Number>
bool Polynom<Number>::isNumber() const& 
{ 
  return _summands.size() == 0  /* <- empty polynomial == 0 */
  || (_summands.size() == 1 && _summands[0].factors->nFactors() == 0);
}

template<class Number>
typename Number::ConstantType Polynom<Number>::unwrapNumber() const& 
{ ASS(isNumber()); return _summands.size() == 0 ? Numeral(0) : _summands[0].numeral; }

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
      return Optional<Numeral>(l - r);
    } catch (MachineArithmeticException) 
    {
      return Optional<Numeral>();
    }
  };

  auto push = [](NumeralVec& vec, Perfect<MonomFactors> m, Numeral c) 
  { vec.push(Monom(c, m)); };

  auto cmpPrecedence = [](Optional<Numeral> lOpt, Numeral r) 
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
TermList Polynom<Number>::toTerm(TermList* results) const
{
  CALL("Polynom::toTerm()")

  auto monomToTerm = [](Monom const& monom, TermList* t) -> TermList {
    auto c = TermList(theory->representConstant(monom.numeral));
    if (monom.factors->isOne()) {
      return c;
    } else {
      auto mon = monom.factors->toTerm(t);
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
TermList Polynom<Number>::toTerm()  const
{ return PolyNf(AnyPoly(perfect(Polynom(*this)))).toTerm(); }

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

#undef DEBUG
#endif // __POLYNOMIAL__H__

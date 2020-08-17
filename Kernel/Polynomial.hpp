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
};

class PolyNf;
template<class Number> class ComplexPolynom;
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

  typename Number::ConstantType coeff;
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
};

struct AnyPoly;

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

};

/**
 * A polynomial of a specific interpreted Number sort. The type parameter is expected to be an instance of NumTraits<...>, 
 * defined in NumTraits.hpp.
 *
 * A polynomial can either be a number or a complex polynomial composted of monomials and number coefficients, 
 * hence it's represented as a coproduct of the two.
 */
template<class Number>
class Polynom 
{
public:
  using Coeff = typename Number::ConstantType;
  using PolyPair = Kernel::PolyPair<Number>;

private:
  friend struct std::hash<Polynom>;
  friend struct std::hash<ComplexPolynom<Number>>;


  // optimization in order to make handle polynomials that are only a single Number more efficiently
  using Inner = Coproduct<UniqueShared<ComplexPolynom<Number> >, Coeff>;
  Inner _inner;

  bool                      isComplex() const& { return _inner.template is<0>(); }
  const UniqueShared<ComplexPolynom<Number>>& unwrapComplex() const& { return _inner.template unwrap<0>(); }
        UniqueShared<ComplexPolynom<Number>>& unwrapComplex()      & { return _inner.template unwrap<0>(); }

public:
  friend bool operator==(Polynom const& lhs, Polynom const& rhs) 
  { return lhs._inner == rhs._inner; }

  bool isNumber() const& { return _inner.template is<1>(); }
  Coeff unwrapNumber() const& { return _inner.template unwrap<1>(); }

  friend ostream& operator<<(ostream& out, const Polynom& self) { 
    self._inner.template match<void>(
          [&](UniqueShared<ComplexPolynom<Number>> poly) { out << poly; }
        , [&](Coeff self          ) { out << self; }
        );
    return out;
  }


private:

  static Polynom<Number> polyAdd(const ComplexPolynom<Number>& lhs, const ComplexPolynom<Number>& rhs) ;
  

  inline static UniqueShared<ComplexPolynom<Number>> polyAdd(Coeff coeff, UniqueShared<ComplexPolynom<Number>> old_) 
  {
    CALL("ComplexPolynom::polyAdd(Coeff coeff, const ComplexPolynom& old) ")
    const auto& oldPoly = *old_;

    ASS(!oldPoly._summands.isEmpty())
    if (coeff == Coeff(0)) {
      return old_;
    } 

    ComplexPolynom<Number> newPoly;
    if (oldPoly._summands[0].monom->isOne()) {
      ASS(oldPoly._summands.begin() != oldPoly._summands.end())

      auto newVal = oldPoly._summands[0].coeff + coeff;
      if (newVal == Coeff(0)) {
        /* skipping zero constant value */
        newPoly._summands.reserve(oldPoly._summands.size() - 1);
        
        auto iter = oldPoly._summands.begin();
        iter++;
        for (; iter !=  oldPoly._summands.end(); iter++) {
          newPoly._summands.pushMv(PolyPair(*iter));
        }
      } else {
        /* skipping zero constant value */
        newPoly._summands = oldPoly._summands;
        newPoly._summands[0].coeff = newVal;
      }
    } else {
      newPoly._summands.reserve(oldPoly._summands.size() + 1);
      newPoly._summands.push(PolyPair(coeff, unique(Monom<Number>())));
      for (auto& f : oldPoly._summands) {
        newPoly._summands.push(PolyPair(f));
      }
    }


    newPoly.integrity();
    return unique(std::move(newPoly));
  }

  static Polynom<Number> polyMul(Coeff coeff, const UniqueShared<ComplexPolynom<Number>>& old_) {
    CALL("ComplexPolynom::polyMul(Coeff coeff, UniqueShared<ComplexPolynom> old) ")
    auto& old = *old_;
    old.integrity();

    if (coeff == Coeff(0)) {
      return Polynom(Coeff(0));

    } else if (coeff == Coeff(1)) {
      return Polynom(old_);

    } else {
      ComplexPolynom<Number> newPoly;
      newPoly._summands.reserve(old._summands.size());
      for (auto& p : old._summands) {
        newPoly._summands.pushMv(PolyPair(coeff * p.coeff, unique(Monom<Number>(p.monom))));
      }
      newPoly.integrity();

      return Polynom(unique(std::move(newPoly)));
    }
  }

  static UniqueShared<ComplexPolynom<Number>> polyMul(const ComplexPolynom<Number>& lhs, const ComplexPolynom<Number>& rhs) 
  {

    CALL("ComplexPolynom::polyMul");
    DEBUG("lhs: ", lhs);
    DEBUG("rhs: ", rhs);
    lhs.integrity();
    rhs.integrity();

    //TODO use Map instead
    map<UniqueShared<Monom<Number>>, Coeff> prods;

    for (auto& l : lhs._summands) {
      for (auto& r : rhs._summands) {
        auto monom = unique(Monom<Number>::monomMul( l.monom, r.monom));
        auto coeff = l.coeff * r.coeff;
        auto res = prods.emplace(make_pair(std::move(monom), coeff));
        if (!res.second) {
          auto& iter = res.first;
          ASS(iter != prods.end());
          iter->second = iter->second + coeff;
        }
      }
    }

    ComplexPolynom<Number> out;
    out._summands.reserve(prods.size());
    for (auto iter = prods.begin(); iter != prods.end(); iter++) {
      auto coeff = iter->second;
      if (coeff != Number::zeroC) {
        out._summands.pushMv(PolyPair(coeff, iter->first)); 
      }
    }
    //TODO use stack instead of vector
    std::sort(out._summands.begin(), out._summands.end(), 
        []( const PolyPair& lhs, const PolyPair& rhs) { return std::less<UniqueShared<Monom<Number>>>{}(lhs.monom, rhs.monom); });
    out.integrity();
    DEBUG("out: ", out);
    return unique(std::move(out));
  }

  static std::pair<Polynom, Polynom> cancel_(Coeff oldl, Coeff oldr) {
    auto zero = Number::zeroC;
    if (oldl >= zero && oldr >= zero) {
      // cancelation simplifies:
      //    10 ~~  8 ==> 2 ~~ 0 
      if (oldl > oldr) {
        return make_pair(Polynom(oldl - oldr), Polynom(zero));
      } else {
        return make_pair(Polynom(zero), Polynom(oldr - oldl));
      }
    } else if (oldl < zero && oldr < zero) {
      // cancelation simplifies:
      //   -10 ~~ -8 ==> 0 ~~ 2 
      if (oldl < oldr) {
        return make_pair(Polynom(zero), Polynom(oldr - oldl));
      } else {
        return make_pair(Polynom(oldl - oldr), Polynom(zero));
      }
    } else {
      // cancelation does not simplify.
      //   -10 ~~  8 ==> 0 ~~ 18  
      //    10 ~~ -8 ==> 18 ~~ 0  
      return make_pair(Polynom(oldl),Polynom(oldr));
    }
  }

  static std::pair<Polynom, Polynom> cancel_(Coeff oldl, UniqueShared<ComplexPolynom<Number>>& oldr_) {
    auto& oldr = *oldr_;

    auto fstCoeff = oldr._summands[0];
    if (!fstCoeff.monom->isOne()) {
      // oldr does not contain a constant term
      return make_pair(Polynom(oldl), Polynom(oldr_));
    } 

    auto numr = fstCoeff.coeff;
    // auto zero = Number::zeroC;
    // auto sameSign = (oldl <= zero) == (numr <= zero);

    //   consider: 
    //   -10 + x ~~  8 ==> -18 + x ~~ 0
    //            OR   ==>       x ~~ 18
    //            both cases do not simplify wrt KBO
    //
    // TODO resolve this strictly non-simplifying behaviour
    //      same applies to cancel_(ComplexPolynom&, ComplexPolynom& oldl)

    auto beginR = oldr._summands.begin() + 1;
    auto sizeR = oldr._summands.size() - 1;

    return make_pair(Polynom(oldl - numr), Polynom(unique(ComplexPolynom<Number>(
              ComplexPolynom<Number>::CoeffVec::fromIterator(
                getArrayishObjectIterator(beginR, sizeR))))));
  }

  static std::pair<Polynom, Polynom> cancel_(UniqueShared<ComplexPolynom<Number>>& oldl, Coeff oldr) {
    auto flipped = cancel_(oldr, oldl);
    return make_pair(std::move(get<1>(flipped)), std::move(get<0>(flipped)));
  }

  static std::pair<Polynom, Polynom> cancel_(UniqueShared<ComplexPolynom<Number>>& oldl_, UniqueShared<ComplexPolynom<Number>>& oldr_) {
    auto& oldl = *oldl_;
    auto& oldr = *oldr_;
    using CoeffVec = typename ComplexPolynom<Number>::CoeffVec;
    auto zero = Number::zeroC;
    auto itl = oldl._summands.begin();
    auto itr = oldr._summands.begin();
    auto endl = oldl._summands.end();
    auto endr = oldr._summands.end();
    auto push = [](CoeffVec& vec, const Monom<Number>& m, Coeff c) 
    { vec.pushMv(PolyPair(c, unique(Monom<Number>(m)))); };

    CoeffVec newl;
    CoeffVec newr;
    while(itl != endl && itr !=  endr) {
      auto cl = itl->coeff;
      auto cr = itr->coeff;
      const UniqueShared<Monom<Number>>& ml = itl->monom;
      const UniqueShared<Monom<Number>>& mr = itr->monom;
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
    return make_pair(
        Polynom(unique(ComplexPolynom<Number>(std::move(newl)))),
        Polynom(unique(ComplexPolynom<Number>(std::move(newr))))
      ); 
  }

public:

  static std::pair<Polynom, Polynom> cancel(Polynom& lhs, Polynom& rhs) {
    CALL("Polynom::cancel(Polynom&, Polynom&)")
    // only dispatiching is going on here
    if (lhs.isNumber()) {
      if (rhs.isNumber()) {
        return cancel_(lhs.unwrapNumber(), rhs.unwrapNumber());
      } else {
        return cancel_(lhs.unwrapNumber(), rhs.unwrapComplex());
      }
    } else {
      ASS(lhs.isComplex())
      if (rhs.isNumber()) {
        return cancel_(lhs.unwrapComplex(), rhs.unwrapNumber());
      } else {
        return cancel_(lhs.unwrapComplex(), rhs.unwrapComplex());
      }
    }
  }

  TermList toTerm() const;


  TermList toTerm(TermList* results) const
  {
    return _inner.template match<TermList>(

          [&](UniqueShared<ComplexPolynom<Number>> self) 
          { return self->toTerm(results); },

          [&](Coeff self ) 
          { return TermList(theory->representConstant(self)); }
        );
  }

public:

  template<class Config>
  inline static Polynom polyMul(Polynom& lhs, Polynom& rhs) ;
  

  inline static Polynom polyAdd(const Polynom& lhs, const Polynom& rhs) 
  {
    CALL("Polynom::polyAdd(const Polynom& lhs, const Polynom& rhs)")
    DBG("lala 1");
    return lhs._inner.template match<Polynom>(
          [&](UniqueShared<ComplexPolynom<Number>> const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<Number>> const& rhs) { return polyAdd(lhs, rhs); }
                , [&](Coeff           const& rhs) { return Polynom(polyAdd(rhs, lhs)); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<Number>> const& rhs) { return Polynom(polyAdd(lhs, rhs)); }
                , [&](Coeff           const& rhs) { return Polynom(lhs + rhs); }
                );
        });
  }

public:
  Polynom(UniqueShared<Monom<Number>> t) : Polynom(Coeff(1), t) {}
  Polynom(PolyNf const& t) : Polynom(Coeff(1), t) {}
  Polynom(Coeff coeff, PolyNf t);
  Polynom(Coeff coeff, UniqueShared<Monom<Number> > t);
  explicit Polynom(Coeff constant)          : _inner(Inner(constant)) {}
  explicit Polynom(UniqueShared<ComplexPolynom<Number>> inner)   : _inner(Inner::template variant<0>(inner)) {} 

  friend bool operator<(const Polynom& lhs, const Polynom& rhs)
  { return std::less<Inner>{}(lhs._inner, rhs._inner); }

  unsigned nSummands() const
  { return _inner.template match<unsigned>(

        [&](UniqueShared<ComplexPolynom<Number>> p) 
        { return p->nSummands(); },

        [&](Coeff self) 
        { return 0; }
        ); }

  unsigned nFactors(unsigned summand) const
  { return _inner.template match<unsigned>(

        [&](UniqueShared<ComplexPolynom<Number>> p) 
        { return p->nFactors(summand); },

        [&](Coeff self) -> unsigned
        { ASSERTION_VIOLATION }
        ); }


  PolyNf const& termAt(unsigned summand, unsigned factor) const
  { return _inner.template match<PolyNf const&>(

        [&](UniqueShared<ComplexPolynom<Number>> p)  -> PolyNf const&
        { return p->monomAt(summand)->termAt(factor); },

        [&](Coeff self) -> PolyNf const&
        { ASSERTION_VIOLATION }
        ); }

}; // class Polynom

POLYMORPHIC_FUNCTION(TermList, toTerm   , const& t, TermList* results; ) { return t.toTerm(results); }
POLYMORPHIC_FUNCTION(unsigned, nSummands, const& t,) { return t.nSummands(); }
POLYMORPHIC_FUNCTION(unsigned, nFactors , const& t, unsigned i;) { return t.nFactors(i); }
POLYMORPHIC_FUNCTION(PolyNf const&, termAt   , const& t, unsigned summand; unsigned factor;) { return t.termAt(summand, factor); }

using AnyPolySuper = Coproduct< 
  Polynom<NumTraits<IntegerConstantType>>, 
  Polynom<NumTraits<RationalConstantType>>, 
  Polynom<NumTraits<RealConstantType>> > ;
struct AnyPoly : public AnyPolySuper
{
  
  template<class C>
  using poly = Polynom<NumTraits<C>>;

  explicit AnyPoly(poly<IntegerConstantType>&& x) : Coproduct(variant<0>(std::move(x))) 
  { CALL("AnyPoly(Int)") }

  explicit AnyPoly(poly<RationalConstantType>&& x ) : Coproduct(variant<1>(std::move(x))) 
  { CALL("AnyPoly(Rat)") }

  explicit AnyPoly(poly<RealConstantType>&& x ) : Coproduct(variant<2>(std::move(x))) 
  { CALL("AnyPoly(Real)") }

  struct PolymorphicArity {
    template<class T>
    unsigned operator()(T const&t ) const 
    { return t.arity(); }
  };

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
  PolyNf normalize(TermList t);

  friend bool operator==(PolyNf const& lhs, PolyNf const& rhs) 
  { return static_cast<Coproduct const&>(lhs) == static_cast<Coproduct const&>(rhs); }

  friend bool operator!=(PolyNf const& lhs, PolyNf const& rhs) 
  { return !(lhs == rhs); }

  friend struct std::hash<PolyNf>;
  friend std::ostream& operator<<(std::ostream& out, const PolyNf& self)
  { return out << static_cast<Coproduct const&>(self); }

  bool    isPoly() const { return is<2>(); }
  AnyPoly const& asPoly() const& { return unwrap<2>(); }
  AnyPoly     && asPoly()     && { return std::move(unwrap<2>()); }
  AnyPoly      & asPoly()      & { return unwrap<2>(); }

  TermList toTerm() const
  { 
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
    static Memo::Hashed<Eval> memo;
    return evaluateBottomUp(*this, Eval{}, memo);
    // return collapsePoly<TermList>(PolyToTerm<Ord>{}); 
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
};



template<class Number>
class Monom 
{
  using MonomTermOrdering = std::less<PolyNf>;
  using MonomPair = ::Kernel::MonomPair<Number>;
  Stack<MonomPair> _factors;
  friend struct std::hash<Monom>;

public:
  Monom() : _factors(decltype(_factors)()) { }
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

private:

  Monom(decltype(_factors) factors) : _factors(factors) { }

public:

  USE_ALLOCATOR(Monom)
  CLASS_NAME(Monom)

  bool isOne() const 
  { return _factors.begin() == _factors.end(); }

  friend std::ostream& operator<<(std::ostream& out, const Monom& self) {
    if (self._factors.size() == 0) {
      return out << "1";
    } else {
      auto iter  = self._factors.begin();
      out << iter->term << "^" << iter->power;
      iter++;
      for (; iter != self._factors.end(); iter++) {
        out << " * " << iter->term << "^" << iter->power;
      }
      return out;
    }
  }

  // friend bool operator>(const Monom& l, const Monom& r) { return r < l; }

  friend bool operator==(const Monom& l, const Monom& r) {
    return l._factors == r._factors;
  }

  public:

  Monom& operator=(Monom&&) = default;
  Monom(Monom&&) = default;

  static UniqueShared<Monom> monomMul(const Monom& lhs, const Monom& rhs) 
    ;

  explicit Monom(const Monom&) = default;
  explicit Monom(Monom&) = default;

  friend class Polynom<Number>;
  friend class ComplexPolynom<Number>;

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
inline UniqueShared<Monom<Number>> Monom<Number>::monomMul(const Monom<Number>& lhs, const Monom<Number>& rhs) 
{
  // ASSERTION_VIOLATION
  return unique(Monom(merge_sort_with(lhs._factors,rhs._factors,
        [](MonomPair const& l, MonomPair const& r)  -> MonomPair
        { 
          ASS_EQ(l.term, r.term); 
          // PolyNf t = l.term;
          // int power = l.power + r.power;
          MonomPair out = l;
          out.power += r.power;
          // return assertionViolation<MonomPair>();
          return out; //Kernel::MonomPair<Number> { .term = t, .power = power };
        },
        [](MonomPair const& l) { return l.power != 0; },
        [](MonomPair const& l, MonomPair const& r) { return l.term < r.term; }
        )));
}

template<class Number>
class ComplexPolynom 
{
  friend struct std::hash<ComplexPolynom>;
  template<class NumTraits> friend class Polynom;

  using Coeff = typename Number::ConstantType;
  using PMonomInner = Monom<Number>;
  using SharedMonom = UniqueShared<PMonomInner>;
public:
  USE_ALLOCATOR(ComplexPolynom)
  CLASS_NAME(ComplexPolynom)

private:
  using PolyPair = Kernel::PolyPair<Number>;
  using CoeffVec = Stack<PolyPair>;
  CoeffVec _summands;

public:

  ComplexPolynom(Coeff coeff, SharedMonom t) : _summands(decltype(_summands)()) 
  { _summands.pushMv(PolyPair(coeff, std::move(t))); }

  ComplexPolynom(SharedMonom&& t) : _summands(decltype(_summands)())  
  { _summands.pushMv(PolyPair(Coeff(1), std::move(t))); }

  ComplexPolynom(Coeff coeff, PolyNf t);

  ComplexPolynom(Coeff constant) : _summands(decltype(_summands)())  
  {
    CALL("ComplexPolynom::ComplexPolynom(Coeff)")
    if (constant != Number::zeroC)
      _summands.pushMv(PolyPair(constant, unique(Monom<Number>())));
  }

  ComplexPolynom(decltype(_summands) coeffs) : _summands(coeffs) { }

  ComplexPolynom() : _summands(decltype(_summands)()) { }

  ComplexPolynom(ComplexPolynom&& other) = default;
  explicit ComplexPolynom(const ComplexPolynom&) = default;

  ComplexPolynom& operator=(ComplexPolynom&& other) = default;


  friend bool operator==(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
    return lhs._summands == rhs._summands;
  }

  unsigned nSummands() const
  { return _summands.size(); }

  unsigned nFactors(unsigned summand) const
  { return _summands[summand].monom->nFactors(); }


  UniqueShared<Monom<Number>> monomAt(unsigned summand) const
  { return _summands[summand].monom; }

  void integrity() const {
#if VDEBUG
    if (_summands.size() > 0) {
      auto iter = this->_summands.begin();
      auto last = iter++;
      while (iter != _summands.end()) {
        ASS_REP(std::less<UniqueShared<Monom<Number>>>{}(last->monom, iter->monom), *this);
        iter->monom->integrity();
        last = iter++;
      }
    }
#endif
  }

  TermList toTerm(TermList* results)  const 
  {
    CALL("ComplexPolynom::toTerm()")

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

  friend std::ostream& operator<<(std::ostream& out, const ComplexPolynom& self) {
    auto iter = self._summands.begin();
    if ( iter == self._summands.end() ) {
      out << "0";
    } else {
      out << iter->monom << " * " << iter->coeff;
      iter++;
      for (; iter != self._summands.end(); iter++) {
        out << " + " << iter->monom << " * " << iter->coeff;
      }
    }
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
Kernel::Polynom<Number>::Polynom(Coeff coeff, PolyNf t) 
  : _inner(Inner(unique(ComplexPolynom<Number>(coeff, t))))
{  }


template<class Number>
Kernel::Polynom<Number>::Polynom(Coeff coeff, UniqueShared<Monom<Number>> t) 
  : _inner(Inner(unique(ComplexPolynom<Number>(coeff, t))))
{  }

template<class Number>
Kernel::ComplexPolynom<Number>::ComplexPolynom(Coeff coeff, PolyNf t) 
  : ComplexPolynom(coeff, unique(Monom<Number>(t))) 
{ }

template<class Number>
template<class Config>
Polynom<Number> Polynom<Number>::polyMul(Polynom& lhs, Polynom& rhs) 
{
  return lhs._inner.template match<Polynom>(
        [&](UniqueShared<ComplexPolynom<Number>> & lhs) { 
          return rhs._inner.template match<Polynom>(
                [&](UniqueShared<ComplexPolynom<Number>> & rhs) { 
                  if(Config::usePolyMul || (lhs->nSummands() == 1 && rhs->nSummands() == 1 )) {
                    return Polynom(polyMul(lhs, rhs)); 
                  } else {
                    auto wrapPoly = 
                      [](UniqueShared<ComplexPolynom<Number> >& t) -> PolyNf 
                      { return PolyNf(AnyPoly(Polynom(t))); };

                    return Polynom(unique(Monom<Number>(wrapPoly(lhs), wrapPoly(rhs))));
                  }
                }
              , [&](Coeff           & rhs) { return polyMul(rhs, lhs); }
              );
        }
      , [&](Coeff & lhs) { 
          return rhs._inner.template match<Polynom>(
                [&](UniqueShared<ComplexPolynom<Number>> & rhs) { return polyMul(lhs, rhs); }
              , [&](Coeff           & rhs) { return Polynom(lhs * rhs); }
              );
      });
}

template<class Number>
Polynom<Number> Polynom<Number>::polyAdd(const ComplexPolynom<Number>& lhs, const ComplexPolynom<Number>& rhs) 
{
  CALL("ComplexPolynom::polyAdd")
  lhs.integrity();
  rhs.integrity();
  ASS(!lhs._summands.isEmpty())
  ASS(!rhs._summands.isEmpty())
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
    return Polynom(unique(ComplexPolynom<Number>(std::move(newCoeffs))));
  }
}


template<class Number> 
TermList Polynom<Number>::toTerm()  const
{ return PolyNf(AnyPoly(Polynom(*this))).toTerm(); }


} // namespace Kernel


template<class NumTraits> struct std::hash<Kernel::Polynom<NumTraits>> 
{
  size_t operator()(Kernel::Polynom<NumTraits> const& self) const 
  { return std::hash<decltype(self._inner)>{}(self._inner); }
};



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
struct std::hash<Kernel::ComplexPolynom<NumTraits>> 
{
  size_t operator()(Kernel::ComplexPolynom<NumTraits> const& x) const noexcept 
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

#ifndef __POLYNOMIAL__H__
#define __POLYNOMIAL__H__

#include "Lib/STLAllocator.hpp"
#include "Kernel/NumTraits.hpp"
#include <vector>
#include "Lib/Coproduct.hpp"
#include "Lib/Optional.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Theory.hpp"
#include <map> // TODO replace by Map
#include "Lib/UniqueShared.hpp"
#include "Kernel/NumTraits.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

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

  template<class Ord> TermList toTerm()
  { return TermList::var(id()); }
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
using MonomTerm = PolyNf;

// template<class Number> using PolyPair = tuple<UniqueShared<Monom<Number>>, typename Number::ConstantType>;
/** 
 * Represents a summand in a polynom of the number type Number 
 * e.g. a term like 3 * (a*x) would be represented as 
 * PolyPair { 3, Monom { a, x }}
 */
template<class Number> 
struct PolyPair {
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

  friend struct std::hash<FuncTerm>;

  friend std::ostream& operator<<(std::ostream& out, const FuncTerm& self) ;

  template<class Ord> TermList toTerm();
};

/**
 * A polynomial of a specific interpreted Number sort. The type parameter is expected to be an instance of NumTraits<...>, 
 * defined in NumTraits.hpp.
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

  // TODO rename to isNumber
  bool isCoeff() const& { return _inner.template is<1>(); }
  // TODO rename to unwrapNumber
  Coeff unwrapCoeff() const& { return _inner.template unwrap<1>(); }

  friend ostream& operator<<(ostream& out, const Polynom& self) { 
    self._inner.template match<void>(
          [&](UniqueShared<ComplexPolynom<Number>> poly) { out << poly; }
        , [&](Coeff self          ) { out << self; }
        );
    return out;
  }


private:

  static Polynom<Number> polyAdd(const ComplexPolynom<Number>& lhs, const ComplexPolynom<Number>& rhs) ;
  

  inline static UniqueShared<ComplexPolynom<Number>> polyAdd(Coeff coeff, UniqueShared<ComplexPolynom<Number>> old_) {
    CALL("ComplexPolynom::polyAdd(Coeff coeff, const ComplexPolynom& old) ")
    const auto& oldPoly = *old_;

    ASS(!oldPoly._coeffs.empty())
    if (coeff == Coeff(0)) {
      return old_;
    } 

    ComplexPolynom<Number> newPoly;
    if (oldPoly._coeffs[0].monom->isOne()) {
      ASS(oldPoly._coeffs.begin() != oldPoly._coeffs.end())

      auto newVal = oldPoly._coeffs[0].coeff + coeff;
      if (newVal == Coeff(0)) {
        /* skipping zero constant value */
        newPoly._coeffs.reserve(oldPoly._coeffs.size() - 1);
        
        auto iter = oldPoly._coeffs.begin();
        iter++;
        for (; iter !=  oldPoly._coeffs.end(); iter++) {
          newPoly._coeffs.emplace_back(PolyPair(*iter));
        }
      } else {
        /* skipping zero constant value */
        newPoly._coeffs = oldPoly._coeffs;
        newPoly._coeffs[0].coeff = newVal;
      }
    } else {
      newPoly._coeffs.reserve(oldPoly._coeffs.size() + 1);
      newPoly._coeffs.push_back(PolyPair(coeff, unique(Monom<Number>())));
      for (auto& f : oldPoly._coeffs) {
        newPoly._coeffs.push_back(PolyPair(f));
      }
    }


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

      newPoly._coeffs.reserve(old._coeffs.size());
      for (auto& p : old._coeffs) {
        newPoly._coeffs.push_back(PolyPair(coeff * p.coeff, unique(Monom<Number>(p.monom))));
      }
      newPoly.integrity();

      return Polynom(unique(std::move(newPoly)));
    }
  }

  static UniqueShared<ComplexPolynom<Number>> polyMul(const ComplexPolynom<Number>& lhs, const ComplexPolynom<Number>& rhs) {

    CALL("ComplexPolynom::polyMul");
    DEBUG("lhs: ", lhs);
    DEBUG("rhs: ", rhs);
    lhs.integrity();
    rhs.integrity();

    //TODO use Map instead
    map<UniqueShared<Monom<Number>>, Coeff> prods;

    for (auto& l : lhs._coeffs) {
      for (auto& r : rhs._coeffs) {
        auto monom = unique(Monom<Number>::monom_mul( l.monom, r.monom));
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
    out._coeffs.reserve(prods.size());
    for (auto iter = prods.begin(); iter != prods.end(); iter++) {
      auto coeff = iter->second;
      if (coeff != Number::zeroC) {
        out._coeffs.emplace_back(PolyPair(coeff, iter->first)); 
      }
    }
    std::sort(out._coeffs.begin(), out._coeffs.end(), 
        []( const PolyPair& lhs, const PolyPair& rhs) { return lhs.monom < rhs.monom; });
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

    auto fstCoeff = oldr._coeffs[0];
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

    return make_pair(Polynom(oldl - numr), Polynom(unique(ComplexPolynom<Number>(typename ComplexPolynom<Number>::CoeffVec(++oldr._coeffs.begin(), oldr._coeffs.end())))));
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
    auto itl = oldl._coeffs.begin();
    auto itr = oldr._coeffs.begin();
    auto endl = oldl._coeffs.end();
    auto endr = oldr._coeffs.end();
    auto push = [](CoeffVec& vec, const Monom<Number>& m, Coeff c) 
    { vec.emplace_back(PolyPair(c, unique(Monom<Number>(m)))); };

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
        ASS(ml > mr)
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
    // only dispatiching is going on here
    if (lhs.isCoeff()) {
      if (rhs.isCoeff()) {
        return cancel_(lhs.unwrapCoeff(), rhs.unwrapCoeff());
      } else {
        return cancel_(lhs.unwrapCoeff(), rhs.unwrapComplex());
      }
    } else {
      ASS(lhs.isComplex())
      if (rhs.isCoeff()) {
        return cancel_(lhs.unwrapComplex(), rhs.unwrapCoeff());
      } else {
        return cancel_(lhs.unwrapComplex(), rhs.unwrapComplex());
      }
    }
  }

  template<class Config>
  TermList toTerm() { 
    return _inner.template match<TermList>(

          [](UniqueShared<ComplexPolynom<Number>> self) 
          { return self->template toTerm<Config>(); },

          [](Coeff self ) 
          { return TermList(theory->representConstant(self)); }
        );
  }

  template<class Config>
  static TermList toTerm(Polynom& self) { 
    return self._inner.template match<TermList>(
          [](UniqueShared<ComplexPolynom<Number>> self) { return self->template toTerm<Config>(); }
        , [](Coeff self          ) { return TermList(theory->representConstant(self)); }
        );
  }

public:

  template<class Config>
  inline static Polynom polyMul(Polynom& lhs, Polynom& rhs) ;
  

  inline static Polynom polyAdd(const Polynom& lhs, const Polynom& rhs) {
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
  Polynom(MonomTerm&& t) : Polynom(Coeff(1), t) {}
  Polynom(Coeff coeff, MonomTerm t);
  Polynom(Coeff coeff, UniqueShared<Monom<Number> > t);
  explicit Polynom(Coeff constant)          : _inner(Inner(constant)) {}
  explicit Polynom(UniqueShared<ComplexPolynom<Number>> inner)   : _inner(Inner::template variant<0>(inner)) {} 
  // explicit Polynom(ComplexPolynom<Number>& inner)   : _inner(Inner::template variant<0>(inner)) {} 
  // template<class UniqueComplexPolynomOrdering>
  // struct PolynomOrdering {
  //     CoproductOrdering<UniqueComplexPolynomOrdering, std::less<Variable>, std::less<AnyPoly> > self{};
  // }

  friend bool operator<(const Polynom& lhs, const Polynom& rhs)
  { 
    return std::less<Inner>{}(lhs._inner, rhs._inner);
    // using PolyT = UniqueShared<ComplexPolynom<Number>>;
    // return CoproductOrdering<typename PolyT::PtrComparison, std::less<Coeff>>{}(lhs._inner,rhs._inner);
  }
private:
}; // class Polynom


template<class T, class Ord>
struct MonoToTerm 
{
  TermList operator()(T& t) const
  { return t.template toTerm<Ord>(); }
};

template<class T, class Ord, class UniqueSharedOrd>
struct MonoToTerm<UniqueShared<T, UniqueSharedOrd>, Ord>
{
  TermList operator()(UniqueShared<T, UniqueSharedOrd>& t) const
  { return t->template toTerm<Ord>(); }
};

template<class Ord> struct PolyToTerm
{
  template<class T> 
  TermList operator()(T& t) const
  { return MonoToTerm<T,Ord>{}(t); }
};

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

  template<class Const, class Config>
  TermList toTerm() 
  {
    CALL("AnyPoly::toTerm")
    return poly<Const>::template toTerm<Config>(as<poly<Const>>());
  }

  template<class Config>
  TermList toTerm_() {
    CALL("AnyPoly::toTerm_")

    if (is<0>()) return toTerm<typename type<0>::value::Coeff, Config>();
    if (is<1>()) return toTerm<typename type<1>::value::Coeff, Config>();
    if (is<2>()) return toTerm<typename type<2>::value::Coeff, Config>();

    ASSERTION_VIOLATION
  }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& self) {
    if (self.is<0>()) return out << self.unwrap<0>();
    if (self.is<1>()) return out << self.unwrap<1>();
    if (self.is<2>()) return out << self.unwrap<2>();
    ASSERTION_VIOLATION
  }

  AnyPoly& operator=(AnyPoly&&) = default;
  AnyPoly(AnyPoly&&) = default;
  explicit AnyPoly(const AnyPoly&) = default;
  friend struct std::hash<AnyPoly>;

  template<class Ord> TermList toTerm()
  { return collapsePoly<TermList>(PolyToTerm<Ord>{}); }
};


template<class t> using vector  = std::vector<t, Lib::STLAllocator<t>>;
template<class K, class V, class Compare = std::less<K>> using map  = std::map<K, V, Compare, STLAllocator<std::pair<const K, V > > >;

/** Merges two map-like vectors into a new map-like vector. 
 * A vector is map-like if has key-value pairs as entry, is sorted by keys and each key is unique within the vector.
 *
 * If there is a key present in both lhs and rhs, the corresponding the two corresponding values will be combined 
 * with the closure @b add. After that the result of combining is then used as argument for @b filter() and will 
 * be discarded if filter returns false.
 */
template<class A, class Combine, class Filter, class Compare>
vector<A> merge_sort_with(const vector<A>& lhs, const vector<A>& rhs, Combine combine, Filter filter, Compare cmp) 
{
    CALL("merge_sort_with()")

    vector<A> out;
    /* is needed at least */
    out.reserve(max(lhs.size(), rhs.size()));
    auto l = lhs.begin();
    auto r = rhs.begin();
    auto insert = [&](const A& value) {
      ASS(filter(value));
      out.emplace_back(value);
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


// template<class T, class Cmp>
// TermList template<class Ord> PolyToTerm<Ord>::toTerm<UniqueShared<T, Cmp> (UniqueShared<T,Cmp>& t) 
// { return t->toTerm(); }

using PolyNfSuper = Lib::Coproduct<UniqueShared<FuncTerm>, Variable, AnyPoly>;

/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * TODO add more documentation
 */
class PolyNf : public PolyNfSuper
{
public:
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

  template<class Ord> TermList toTerm()
  { return collapsePoly<TermList>(PolyToTerm<Ord>{}); }
};

inline bool operator<(const PolyNf& lhs, const PolyNf& rhs)  // TODO get rid of that and use the vampire sorting method 
{ return std::less<PolyNfSuper>{}(lhs,rhs); }

template<class Number>
class Monom 
{
  // using MonomTermOrdering = PolyNfOrdering<UniqueShared<PolyNf>::PtrComparison>;
  using MonomTermOrdering = std::less<MonomTerm>;
  vector<tuple<MonomTerm, int>> _factors;
  Lib::Optional<TermList> _toTerm;
  friend struct std::hash<Monom>;

public:
  Monom() : _factors(decltype(_factors)()) { }
  Monom(MonomTerm t) : _factors { make_tuple(t, 1)}  { }
  Monom(MonomTerm t1, MonomTerm t2) 
    : _factors(t1 == t2 ? decltype(_factors) ({ make_tuple(t1, 2)}) : 
               MonomTermOrdering{}(t1, t2) ? decltype(_factors) ({ make_tuple(t1,1), make_tuple(t2,1)}) :
                          decltype(_factors) ({ make_tuple(t2,1), make_tuple(t1,1)}) 
                          )  { }
private:

  Monom(decltype(_factors) factors) : _factors(factors) { }

public:

  USE_ALLOCATOR(Monom)
  CLASS_NAME(Monom)
  using monom_pair = typename decltype(_factors)::value_type;

  static MonomTerm getTerm(const typename decltype(_factors)::value_type& pair) 
  { return std::get<0>(pair); }

  static int getCount(const typename decltype(_factors)::value_type& pair) 
  { return std::get<1>(pair); }

  bool isOne() const 
  { return _factors.begin() == _factors.end(); }

  friend std::ostream& operator<<(std::ostream& out, const Monom& self) {
    if (self._factors.size() == 0) {
      return out << "1";
    } else {
      auto iter  = self._factors.begin();
      out << getTerm(*iter) << "^" << getCount(*iter);
      iter++;
      for (; iter != self._factors.end(); iter++) {
        out << " * " << getTerm(*iter) << "^" << getCount(*iter);
      }
      return out;
    }
  }

  friend bool operator<(const Monom& l, const Monom& r) {
    if (l._factors.size() < r._factors.size()) {
      return true;
    } else if (l._factors.size() > r._factors.size()) {
      return false;
    } else {
      return  l._factors < r._factors;
    }
  }

  friend bool operator>(const Monom& l, const Monom& r) { return r < l; }

  friend bool operator==(const Monom& l, const Monom& r) {
    return l._factors == r._factors;
  }

  public:

  Monom& operator=(Monom&&) = default;
  Monom(Monom&&) = default;

  static UniqueShared<Monom> monom_mul(const Monom& lhs, const Monom& rhs) 
  {
    return unique(Monom(merge_sort_with(lhs._factors,rhs._factors,
          [](monom_pair const& l, monom_pair const& r) 
          { 
            ASS_EQ(getTerm(l), getTerm(r)); 
            return monom_pair(getTerm(l), getCount(l) + getCount(r)); 
          },
          [](monom_pair const& l) { return getCount(l) != 0; },
          [](monom_pair const& l, monom_pair const& r) { return getTerm(l) < getTerm(r); }
          )));
  }

  explicit Monom(const Monom&) = default;
  explicit Monom(Monom&) = default;

  friend class Polynom<Number>;
  friend class ComplexPolynom<Number>;

  template<class Config> TermList toTerm() {
    CALL("Monom::toTerm()")
      //
    // TODO replace caching by generic memoization
    return _toTerm.unwrapOrInit([&]() {

      if (_factors.size() == 0) {
        return Number::one();
      } else {

        vector<TermList> factors;
        auto sz = 0;
        for(auto& f : _factors) {
          sz += getCount(f);
        }
        factors.reserve(sz);

        for (auto f : _factors) {
          for (auto i = 0; i < getCount(f); i++) {
            factors.push_back(getTerm(f).template toTerm<Config>());
          }
        }

        sort(begin(factors), end(factors), typename Config::Ordering{});

        auto iter = factors.rbegin();

        auto out = *iter;
        iter++;
        for(; iter != factors.rend(); iter++)  {
          out = Number::mul(*iter, out); 
        }
        return out;
      }
    });
  }

  void integrity() const {
#if VDEBUG
    if (_factors.size() > 0) {
      auto iter = this->_factors.begin();
      auto last = iter++;
      while (iter != _factors.end()) {
        ASS_REP(getTerm(*last) < getTerm(*iter), *this);
        last = iter++;
      }
    }
#endif
  }


};

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
  using CoeffVec = vector<PolyPair>;
  // TODO _coeffs => _summands
  CoeffVec _coeffs;
  Lib::Optional<TermList> _toTerm;

public:

  ComplexPolynom(Coeff coeff, SharedMonom t) : _coeffs(decltype(_coeffs)()) 
  { _coeffs.emplace_back(PolyPair(coeff, std::move(t))); }

  ComplexPolynom(SharedMonom&& t) : _coeffs(decltype(_coeffs)())  
  { _coeffs.emplace_back(PolyPair(Coeff(1), std::move(t))); }

  ComplexPolynom(Coeff coeff, MonomTerm t);

  ComplexPolynom(Coeff constant) : _coeffs(decltype(_coeffs)())  
  {
    CALL("ComplexPolynom::ComplexPolynom(Coeff)")
    if (constant != Number::zeroC)
      _coeffs.emplace_back(PolyPair(constant, unique(Monom<Number>())));
  }

  ComplexPolynom(decltype(_coeffs) coeffs) : _coeffs(coeffs) { }

  ComplexPolynom() : _coeffs(decltype(_coeffs)()) { }

  ComplexPolynom(ComplexPolynom&& other) = default;
  explicit ComplexPolynom(const ComplexPolynom&) = default;
  unsigned nSummands() const& { return _coeffs.size(); }

  ComplexPolynom& operator=(ComplexPolynom&& other) = default;


  friend bool operator==(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
    return lhs._coeffs == rhs._coeffs;
  }

  void integrity() const {
#if VDEBUG
    if (_coeffs.size() > 0) {
      auto iter = this->_coeffs.begin();
      auto last = iter++;
      while (iter != _coeffs.end()) {
        ASS_REP(last->monom < iter->monom, *this);
        iter->monom->integrity();
        last = iter++;
      }
    }
#endif
  }

  template<class Config>
  TermList toTerm() {
    CALL("ComplexPolynom::toTerm()")
    auto& self = *this;
    return self._toTerm.unwrapOrInit([&]() {
      
      auto trm = [](PolyPair& x) -> TermList { 
        if (x.monom->isOne()) {  
          /* the pair is a plain Number */
          return TermList( theory->representConstant(x.coeff) );

        } else if (x.coeff== Number::constant(1)) {
          /* the pair is an uninterpreted term */
          return x.monom->template toTerm<Config>();

        } else if (x.coeff== Number::constant(-1)) {
          return TermList(Number::minus(x.monom->template toTerm<Config>()));

        } else {
          return TermList(Number::mul(TermList( theory->representConstant(x.coeff) ), x.monom->template toTerm<Config>())); 
        }
      };

      vector<TermList> coeffs(self._coeffs.size());
      transform(begin(self._coeffs),end(self._coeffs), begin(coeffs), trm);

      sort(begin(coeffs), end(coeffs), typename Config::Ordering{});

      auto iter = coeffs.rbegin(); 
      if (iter == coeffs.rend()) {
        return TermList(Number::zero());
      } else {
        auto out = *iter;
        iter++;
        for (; iter != coeffs.rend(); iter++) {
          out = Number::add(*iter, out);
        }
        return out;
      }
    });
  }

  friend std::ostream& operator<<(std::ostream& out, const ComplexPolynom& self) {
    auto iter = self._coeffs.begin();
    if ( iter == self._coeffs.end() ) {
      out << "0";
    } else {
      out << iter->monom << " * " << iter->coeff;
      iter++;
      for (; iter != self._coeffs.end(); iter++) {
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
Kernel::Polynom<Number>::Polynom(Coeff coeff, MonomTerm t) 
  : _inner(Inner(unique(ComplexPolynom<Number>(coeff, t))))
{  }


template<class Number>
Kernel::Polynom<Number>::Polynom(Coeff coeff, UniqueShared<Monom<Number>> t) 
  : _inner(Inner(unique(ComplexPolynom<Number>(coeff, t))))
{  }

template<class Number>
Kernel::ComplexPolynom<Number>::ComplexPolynom(Coeff coeff, MonomTerm t) 
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
  ASS(!lhs._coeffs.empty())
  ASS(!rhs._coeffs.empty())
  auto newCoeffs = merge_sort_with(lhs._coeffs, rhs._coeffs, 
      /* combine */
      [](PolyPair const& l, PolyPair const& r)
      { ASS_EQ(l.monom, r.monom); return PolyPair( l.coeff + r.coeff, l.monom ); },

      /* filter */
      [](PolyPair const& x)
      { return x.coeff != Number::zeroC; },

      /* compare */
      [](PolyPair const& l, PolyPair const& r){ return l.monom < r.monom; }
    );
  if (newCoeffs.empty())  {
    return Polynom(Coeff(0));
  } else {
    return Polynom(unique(ComplexPolynom<Number>(std::move(newCoeffs))));
  }
}




template<class Ord> TermList FuncTerm::toTerm()
{ 
  // TODO get rid of recursion
  Stack<TermList> args(_args.size());
  for (auto arg : _args) {
    args.push(arg.template toTerm<Ord>());
  }
  return TermList(Term::create(_fun.id(), args.size(), args.begin())); 
}

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
    for (auto c : x._coeffs) {
      out = HashUtils::combine(
              stlHash(c.monom),
              stlHash(c.coeff),
              out);
    }
    return out;
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
      out = HashUtils::combine(
            stlHash(std::get<0>(f)),
            stlHash(std::get<1>(f)),
            out);
    }
    return out;
  }
};

#undef DEBUG

#endif // __POLYNOMIAL__H__

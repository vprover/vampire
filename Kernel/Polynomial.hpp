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
template<class number> class ComplexPolynom;
template<class number> class        Polynom;
template<class number> class        Monom;
using MonomTerm = PolyNf;
template<class number> using poly_pair = tuple<UniqueShared<Monom<number>>, typename number::ConstantType>;
struct AnyPoly;


std::ostream& operator<<(std::ostream& out, const PolyNf& self);

bool operator==(PolyNf const& lhs, PolyNf const& rhs);

/**
 * Represents an ordenary complex term. In the PolyNF term tree.
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
 * A polynomial of a specific interpreted number sort. The type parameter is expected to be an instance of NumTraits<...>, 
 * defined in NumTraits.hpp.
 */
template<class number>
class Polynom 
{
public:
  using Coeff = typename number::ConstantType;
  using poly_pair = Kernel::poly_pair<number>;

private:
  friend struct std::hash<Polynom>;
  friend struct std::hash<ComplexPolynom<number>>;


  // optimization in order to make handle polynomials that are only a single number more efficiently
  using Inner = Coproduct<UniqueShared<ComplexPolynom<number> >, Coeff>;
  Inner _inner;

  bool                      isComplex() const& { return _inner.template is<0>(); }
  const UniqueShared<ComplexPolynom<number>>& unwrapComplex() const& { return _inner.template unwrap<0>(); }
        UniqueShared<ComplexPolynom<number>>& unwrapComplex()      & { return _inner.template unwrap<0>(); }

public:
  friend bool operator==(Polynom const& lhs, Polynom const& rhs) 
  { return lhs._inner == rhs._inner; }

  // TODO rename to isNumber
  bool isCoeff() const& { return _inner.template is<1>(); }
  // TODO rename to unwrapNumber
  Coeff unwrapCoeff() const& { return _inner.template unwrap<1>(); }

  friend ostream& operator<<(ostream& out, const Polynom& self) { 
    self._inner.template match<void>(
          [&](UniqueShared<ComplexPolynom<number>> poly) { out << poly; }
        , [&](Coeff self          ) { out << self; }
        );
    return out;
  }


private:

  static Polynom<number> poly_add(const ComplexPolynom<number>& lhs, const ComplexPolynom<number>& rhs) {
    CALL("ComplexPolynom::poly_add")
    ASS(!lhs._coeffs.empty())
    ASS(!rhs._coeffs.empty())
    auto newCoeffs = merge_sort_with(lhs._coeffs, rhs._coeffs, 
            [](Coeff l, Coeff r){ return l + r; },
            [](Coeff x){ return x != number::zeroC; }
          );
    if (newCoeffs.empty())  {
      return Polynom(Coeff(0));
    } else {
      return Polynom(unique(ComplexPolynom<number>(std::move(newCoeffs))));
    }
  }

  inline static UniqueShared<ComplexPolynom<number>> add(Coeff coeff, UniqueShared<ComplexPolynom<number>> old_) {
    CALL("ComplexPolynom::add(Coeff coeff, const ComplexPolynom& old) ")
    const auto& oldPoly = *old_;

    ASS(!oldPoly._coeffs.empty())
    if (coeff == Coeff(0)) {
      return old_;
    } 

    ComplexPolynom<number> newPoly;
    if (oldPoly.getMonom(oldPoly._coeffs[0])->isOne()) {
      ASS(oldPoly._coeffs.begin() != oldPoly._coeffs.end())

      auto newVal = oldPoly.getCoeff(oldPoly._coeffs[0]) + coeff;
      if (newVal == Coeff(0)) {
        /* skipping zero constant value */
        newPoly._coeffs.reserve(oldPoly._coeffs.size() - 1);
        
        auto iter = oldPoly._coeffs.begin();
        iter++;
        for (; iter !=  oldPoly._coeffs.end(); iter++) {
          newPoly._coeffs.emplace_back(poly_pair(*iter));
        }
      } else {
        /* skipping zero constant value */
        newPoly._coeffs = oldPoly._coeffs;
        oldPoly.getCoeffMut(newPoly._coeffs[0]) = newVal;
      }
    } else {
      newPoly._coeffs.reserve(oldPoly._coeffs.size() + 1);
      newPoly._coeffs.push_back(poly_pair(unique(Monom<number>()), coeff));
      for (auto& f : oldPoly._coeffs) {
        // newPoly.push_back(poly_pair(unique(Monom<number>(old.getMonom(p), old.getMonom()))))
        newPoly._coeffs.push_back(poly_pair(f));
      }
    }


    return unique(std::move(newPoly));
  }

  static Polynom<number> coeff_poly_mul(Coeff coeff, const UniqueShared<ComplexPolynom<number>>& old_) {
    CALL("ComplexPolynom::coeff_poly_mul(Coeff coeff, UniqueShared<ComplexPolynom> old) ")
    auto& old = *old_;

    if (coeff == Coeff(0)) {
      return Polynom(Coeff(0));

    } else if (coeff == Coeff(1)) {
      return Polynom(old_);

    } else {
      ComplexPolynom<number> newPoly;

      newPoly._coeffs.reserve(old._coeffs.size());
      for (auto& p : old._coeffs) {
        newPoly._coeffs.push_back(poly_pair(unique(Monom<number>(old.getMonom(p))), coeff * old.getCoeff(p)));
      }

      return Polynom(unique(std::move(newPoly)));
    }
  }

  static UniqueShared<ComplexPolynom<number>> poly_mul(const ComplexPolynom<number>& lhs, const ComplexPolynom<number>& rhs) {

    CALL("ComplexPolynom::poly_mul");
    DEBUG("lhs: ", lhs);
    DEBUG("rhs: ", rhs);
    lhs.integrity();
    rhs.integrity();

    //TODO use Map instead
    map<UniqueShared<Monom<number>>, Coeff> prods;

    for (auto& l : lhs._coeffs) {
      for (auto& r : rhs._coeffs) {
        auto monom = unique(Monom<number>::monom_mul( lhs.getMonom(l), rhs.getMonom(r)));
        auto coeff = lhs.getCoeff(l) * rhs.getCoeff(r);
        auto res = prods.emplace(make_pair(std::move(monom), coeff));
        if (!res.second) {
          auto& iter = res.first;
          ASS(iter != prods.end());
          iter->second = iter->second + coeff;
        }
      }
    }

    ComplexPolynom<number> out;
    out._coeffs.reserve(prods.size());
    for (auto iter = prods.begin(); iter != prods.end(); iter++) {
      auto coeff = iter->second;
      if (coeff != number::zeroC) {
        out._coeffs.emplace_back(poly_pair(iter->first, coeff)); 
      }
    }
    DEBUG("out: ", out);
    std::sort(out._coeffs.begin(), out._coeffs.end());
    out.integrity();
    return unique(std::move(out));
  }

  static std::pair<Polynom, Polynom> cancel_(Coeff oldl, Coeff oldr) {
    auto zero = number::zeroC;
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

  static std::pair<Polynom, Polynom> cancel_(Coeff oldl, UniqueShared<ComplexPolynom<number>>& oldr_) {
    auto& oldr = *oldr_;

    auto fstCoeff = oldr._coeffs[0];
    if (!oldr.getMonom(fstCoeff)->isOne()) {
      // oldr does not contain a constant term
      return make_pair(Polynom(oldl), Polynom(oldr_));
    } 

    auto numr = oldr.getCoeff(fstCoeff);
    // auto zero = number::zeroC;
    // auto sameSign = (oldl <= zero) == (numr <= zero);

    //   consider: 
    //   -10 + x ~~  8 ==> -18 + x ~~ 0
    //            OR   ==>       x ~~ 18
    //            both cases do not simplify wrt KBO
    //
    // TODO resolve this strictly non-simplifying behaviour
    //      same applies to cancel_(ComplexPolynom&, ComplexPolynom& oldl)

    return make_pair(Polynom(oldl - numr), Polynom(unique(ComplexPolynom<number>(typename ComplexPolynom<number>::CoeffVec(++oldr._coeffs.begin(), oldr._coeffs.end())))));
  }

  static std::pair<Polynom, Polynom> cancel_(UniqueShared<ComplexPolynom<number>>& oldl, Coeff oldr) {
    auto flipped = cancel_(oldr, oldl);
    return make_pair(std::move(get<1>(flipped)), std::move(get<0>(flipped)));
  }

  static std::pair<Polynom, Polynom> cancel_(UniqueShared<ComplexPolynom<number>>& oldl_, UniqueShared<ComplexPolynom<number>>& oldr_) {
    auto& oldl = *oldl_;
    auto& oldr = *oldr_;
    using CoeffVec = typename ComplexPolynom<number>::CoeffVec;
    auto zero = number::zeroC;
    auto itl = oldl._coeffs.begin();
    auto itr = oldr._coeffs.begin();
    auto endl = oldl._coeffs.end();
    auto endr = oldr._coeffs.end();
    auto push = [](CoeffVec& vec, const Monom<number>& m, Coeff c) {
      vec.emplace_back(make_pair(unique(Monom<number>(m)), c));
    };
    CoeffVec newl;
    CoeffVec newr;
    while(itl != endl && itr !=  endr) {
      auto cl = oldl.getCoeff(*itl);
      auto cr = oldr.getCoeff(*itr);
      const UniqueShared<Monom<number>>& ml = oldl.getMonom(*itl);
      const UniqueShared<Monom<number>>& mr = oldr.getMonom(*itr);
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
      push(newl, get<0>(*itl), get<1>(*itl));
    }
    for(; itr != endr; itr++) {
      push(newr, get<0>(*itr), get<1>(*itr));
    }
    return make_pair(
        Polynom(unique(ComplexPolynom<number>(std::move(newl)))),
        Polynom(unique(ComplexPolynom<number>(std::move(newr))))
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

          [](UniqueShared<ComplexPolynom<number>> self) 
          { return self->template toTerm<Config>(); },

          [](Coeff self ) 
          { return TermList(theory->representConstant(self)); }
        );
  }

  template<class Config>
  static TermList toTerm(Polynom& self) { 
    return self._inner.template match<TermList>(
          [](UniqueShared<ComplexPolynom<number>> self) { return self->template toTerm<Config>(); }
        , [](Coeff self          ) { return TermList(theory->representConstant(self)); }
        );
  }

public:

  template<class Config>
  inline static Polynom poly_mul(Polynom& lhs, Polynom& rhs) ;
  

  inline static Polynom poly_add(const Polynom& lhs, const Polynom& rhs) {
    return lhs._inner.template match<Polynom>(
          [&](UniqueShared<ComplexPolynom<number>> const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<number>> const& rhs) { return poly_add(lhs, rhs); }
                , [&](Coeff           const& rhs) { return Polynom(add(rhs, lhs)); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<number>> const& rhs) { return Polynom(add(lhs, rhs)); }
                , [&](Coeff           const& rhs) { return Polynom(lhs + rhs); }
                );
        });
  }

public:
  Polynom(UniqueShared<Monom<number>> t) : Polynom(Coeff(1), t) {}
  Polynom(MonomTerm&& t) : Polynom(Coeff(1), t) {}
  Polynom(Coeff coeff, MonomTerm t);
  Polynom(Coeff coeff, UniqueShared<Monom<number> > t);
  explicit Polynom(Coeff constant)          : _inner(Inner(constant)) {}
  explicit Polynom(UniqueShared<ComplexPolynom<number>> inner)   : _inner(Inner::template variant<0>(inner)) {} 
  // explicit Polynom(ComplexPolynom<number>& inner)   : _inner(Inner::template variant<0>(inner)) {} 
  // template<class UniqueComplexPolynomOrdering>
  // struct PolynomOrdering {
  //     CoproductOrdering<UniqueComplexPolynomOrdering, std::less<Variable>, std::less<AnyPoly> > self{};
  // }

  friend bool operator<(const Polynom& lhs, const Polynom& rhs)
  { 
    return std::less<Inner>{}(lhs._inner, rhs._inner);
    // using PolyT = UniqueShared<ComplexPolynom<number>>;
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
template<class A, class B, class Add, class Filter>
vector<tuple<A, B>> merge_sort_with(const vector<tuple<A, B>>& lhs, const vector<tuple<A, B>>& rhs, Add add, Filter filter) {
    CALL("merge_sort_with()")

    vector<tuple<A,B>> out;
    /* is needed at least */
    out.reserve(max(lhs.size(), rhs.size()));
    auto l = lhs.begin();
    auto r = rhs.begin();
    auto insert = [&](const A& key, B value) {
      ASS(filter(value));
      out.emplace_back(make_tuple(A(key), value));
    };
    auto fst = [](const tuple<A,B>& x) { return get<0>(x); };
    auto snd = [](const tuple<A,B>& x) { return get<1>(x); };
    while (l != lhs.end() && r != rhs.end() ) {
      if (fst(*l) == fst(*r)) {
        //add up
        auto sum = add(snd(*l), snd(*r));
        if (filter(sum))
          insert(fst(*l), sum);
        l++;
        r++;
      } else if (fst(*l) < fst(*r)) {
        // insert l
        insert(fst(*l), snd(*l));
        l++;
      } else {
        // insert r
        insert(fst(*r), snd(*r));
        r++;
      }
    }
    while (l != lhs.end()) {
      insert(fst(*l), snd(*l));
      l++;
    }
    while (r != rhs.end()) {
      insert(fst(*r), snd(*r));
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

template<class number>
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
           [](int l, int r) { return l + r; },
           [](int l) { return l != 0; })));
  }

  explicit Monom(const Monom&) = default;
  explicit Monom(Monom&) = default;

  friend class Polynom<number>;
  friend class ComplexPolynom<number>;

  template<class Config> TermList toTerm() {
    CALL("Monom::toTerm()")
      //
    // TODO replace caching by generic memoization
    return _toTerm.unwrapOrInit([&]() {

      if (_factors.size() == 0) {
        return number::one();
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
          out = number::mul(*iter, out); 
        }
        return out;
      }
    });
  }

};

template<class number>
class ComplexPolynom 
{
  friend struct std::hash<ComplexPolynom>;
  template<class NumTraits> friend class Polynom;

  using Coeff = typename number::ConstantType;
  using PMonomInner = Monom<number>;
  using SharedMonom = UniqueShared<PMonomInner>;
public:
  USE_ALLOCATOR(ComplexPolynom)
  CLASS_NAME(ComplexPolynom)

private:
  using poly_pair = Kernel::poly_pair<number>;
  using CoeffVec = vector<poly_pair>;
  CoeffVec _coeffs;
  Lib::Optional<TermList> _toTerm;

public:

  // ComplexPolynom(Coeff coeff, PMonom t) : _coeffs(decltype(_coeffs)()) 
  // { _coeffs.emplace_back(poly_pair(std::move(t), coeff)); }

  ComplexPolynom(Coeff coeff, SharedMonom t) : _coeffs(decltype(_coeffs)()) 
  { _coeffs.emplace_back(poly_pair(std::move(t), coeff)); }

  ComplexPolynom(SharedMonom&& t) : _coeffs(decltype(_coeffs)())  
  { _coeffs.emplace_back(poly_pair(std::move(t), Coeff(1))); }

  ComplexPolynom(Coeff coeff, MonomTerm t);

  ComplexPolynom(Coeff constant) : _coeffs(decltype(_coeffs)())  
  {
    CALL("ComplexPolynom::ComplexPolynom(Coeff)")
    if (constant != number::zeroC)
      _coeffs.emplace_back(poly_pair(unique(Monom<number>()), constant));
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

  static SharedMonom& getMonom(poly_pair& pair) {
    return std::get<0>(pair);
  }

  static const SharedMonom& getMonom(const poly_pair& pair) {
    return std::get<0>(pair);
  }

  static const Coeff& getCoeff(const poly_pair& pair) {
    return std::get<1>(pair);
  }

  static Coeff& getCoeffMut(poly_pair& pair) {
    return std::get<1>(pair);
  }

  void integrity() const {
#if VDEBUG
    if (_coeffs.size() > 0) {
      auto iter = this->_coeffs.begin();
      auto last = iter++;
      while (iter != _coeffs.end()) {
        ASS_REP(getMonom(*last) < getMonom(*iter), *this);
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
      // self.integrity();
      
      auto trm = [](poly_pair& x) -> TermList { 
        using Self = ComplexPolynom;

        if (Self::getMonom(x)->isOne()) {  
          /* the pair is a plain number */
          return TermList( theory->representConstant(Self::getCoeff(x)) );

        } else if (Self::getCoeff(x)== number::constant(1)) {
          /* the pair is an uninterpreted term */
          return Self::getMonom(x)->template toTerm<Config>();

        } else if (Self::getCoeff(x)== number::constant(-1)) {
          return TermList(number::minus(Self::getMonom(x)->template toTerm<Config>()));

        } else {
          return TermList(number::mul(TermList( theory->representConstant(Self::getCoeff(x)) ), Self::getMonom(x)->template toTerm<Config>())); 
        }
      };

      vector<TermList> coeffs(self._coeffs.size());
      transform(begin(self._coeffs),end(self._coeffs), begin(coeffs), trm);

      sort(begin(coeffs), end(coeffs), typename Config::Ordering{});

      auto iter = coeffs.rbegin(); 
      if (iter == coeffs.rend()) {
        return TermList(number::zero());
      } else {
        auto out = *iter;
        iter++;
        for (; iter != coeffs.rend(); iter++) {
          out = number::add(*iter, out);
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
      out << self.getMonom(*iter)<< " * " << self.getCoeff(*iter);
      iter++;
      for (; iter != self._coeffs.end(); iter++) {
        out << " + " << self.getMonom(*iter)<< " * " << self.getCoeff(*iter);
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


template<class number>
Kernel::Polynom<number>::Polynom(Coeff coeff, MonomTerm t) 
  : _inner(Inner(unique(ComplexPolynom<number>(coeff, t))))
{  }


template<class number>
Kernel::Polynom<number>::Polynom(Coeff coeff, UniqueShared<Monom<number>> t) 
  : _inner(Inner(unique(ComplexPolynom<number>(coeff, t))))
{  }

template<class number>
Kernel::ComplexPolynom<number>::ComplexPolynom(Coeff coeff, MonomTerm t) 
  : ComplexPolynom(coeff, unique(Monom<number>(t))) 
{ }

template<class number>
template<class Config>
Polynom<number> Polynom<number>::poly_mul(Polynom& lhs, Polynom& rhs) 
{
    return lhs._inner.template match<Polynom>(
          [&](UniqueShared<ComplexPolynom<number>> & lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<number>> & rhs) { 
                    if(Config::usePolyMul || (lhs->nSummands() == 1 && rhs->nSummands() == 1 )) {
                      return Polynom(poly_mul(lhs, rhs)); 
                    } else {
                      auto wrapPoly = 
                        [](UniqueShared<ComplexPolynom<number> >& t) -> PolyNf 
                        { return PolyNf(AnyPoly(Polynom(t))); };

                      return Polynom(unique(Monom<number>(wrapPoly(lhs), wrapPoly(rhs))));
                      // return Polynom(ComplexPolynom<number>(unique(Monom<number>(PolyNf(AnyPoly(Polynom<number>(lhs))), PolyNf(AnyPoly(Polynom<number>(rhs)))))));
                      // auto wrap = [](Polynom p) -> PolyNf {
                      //   return PolyNf(unique(AnyPoly(p)));
                      // };
                      // auto l = unique(ComplexPolynom<number>::template toTerm<Config>(*lhs));
                      // auto r = unique(ComplexPolynom<number>::template toTerm<Config>(*rhs));
                      // return Polynom(unique(ComplexPolynom<number>(unique(Monom<number>(l,r)))));
                      // return Polynom(unique(ComplexPolynom<number>(unique(Monom<number>(l,r)))));
                    }
                  }
                , [&](Coeff           & rhs) { return coeff_poly_mul(rhs, lhs); }
                );
          }
        , [&](Coeff & lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](UniqueShared<ComplexPolynom<number>> & rhs) { return coeff_poly_mul(lhs, rhs); }
                , [&](Coeff           & rhs) { return Polynom(lhs * rhs); }
                );
        });
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
              stlHash(ComplexPolynom<NumTraits>::getMonom(c)),
              stlHash(ComplexPolynom<NumTraits>::getCoeff(c)),
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

#ifndef __POLYNOMIAL__H__
#define __POLYNOMIAL__H__

#include "Lib/STLAllocator.hpp"
#include "Kernel/NumTraits.hpp"
#include <vector>
#include "Lib/Either.hpp"
#include "Lib/Optional.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Theory.hpp"
#include <map> // TODO replace by Map

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Kernel {

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
      } else if (fst(*l)< fst(*r)) {
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


template<class number>
class Monom { 
public:
  using Coeff = typename number::ConstantType;
  class MonomInner;
  struct Hasher;
  Monom& operator=(const Monom&) = default;
  Monom(Monom&&) = default;

private:
  MonomInner* _inner;
  static Map<MonomInner, MonomInner*, Hasher> monoms;

public:

  bool isOne() const {return _inner->isOne();}

  template<class Config>
  TermList toTerm() {return _inner->template toTerm<Config>();}

  friend bool operator<(const Monom& lhs, const Monom& rhs) { return lhs._inner < rhs._inner; }

  friend bool operator==(const Monom& lhs, const Monom& rhs) {return lhs._inner == rhs._inner;}
  size_t hash() const { return std::hash<size_t>{}((size_t) _inner); }

  friend ostream& operator<<(ostream& out, const Monom& m) {return out << *m._inner;}

  Monom(const Monom& other) : _inner(other._inner) {}
  Monom& operator=(Monom&& other) = default;  
  Monom(MonomInner* inner) : _inner(inner) {}
  Monom() : _inner(MonomInner::create(MonomInner())) {}

  Monom(TermList t) : _inner(MonomInner::create(MonomInner(t))) {}
  Monom(TermList factor1, TermList factor2) : _inner(MonomInner::create(MonomInner(factor1, factor2))) { }


  static Monom monom_mul(const Monom& lhs, const Monom& rhs) {
    return Monom(MonomInner::monom_mul(*lhs._inner, *rhs._inner));
  }

  // Monom& operator=(Monom&&) = default;
  class MonomInner {
    vector<tuple<TermList, int>> _factors;
    Lib::Optional<TermList> _toTerm;
    friend class Monom;

    // empty monom == 1
    static MonomInner* create(MonomInner&& self) {
      CALL("MonomInner::create(MonomInner&&)")
      return monoms.getOrInit(MonomInner(self),
          [=](MonomInner** toInit) {*toInit = new MonomInner(std::move(self));});
    }

  public:
    MonomInner() : _factors(decltype(_factors)()) { }
    private:

    MonomInner(decltype(_factors) factors) : _factors(factors) { }

    MonomInner(TermList t) : _factors { make_tuple(t, 1)}  { }
    MonomInner(TermList t1, TermList t2) 
      : _factors(t1 == t2 ? decltype(_factors) ({ make_tuple(t1, 2)}) : 
                 t1 <  t2 ? decltype(_factors) ({ make_tuple(t1,1), make_tuple(t2,1)}) :
                            decltype(_factors) ({ make_tuple(t2,1), make_tuple(t1,1)}) 
                            )  { }

    public:

      USE_ALLOCATOR(MonomInner)
      CLASS_NAME(MonomInner)
      using monom_pair = typename decltype(_factors)::value_type;

    static TermList getTerm(const typename decltype(_factors)::value_type& pair) {
      return std::get<0>(pair);
    }

    static int getCount(const typename decltype(_factors)::value_type& pair) {
      return std::get<1>(pair);
    }

    bool isOne() const  {
      return _factors.begin() == _factors.end();
    }

    static TermList pairToTerm(const monom_pair& pair) {
      auto cnt = getCount(pair);
      ASS_REP(cnt > 0, cnt)

      auto trm = getTerm(pair);
      auto out = trm;
      for (auto i = 1; i < cnt; i++) {
        out = number::mul(trm, out);
      }
      return out;
    }

    template<class Config>
    TermList toTerm() {
      CALL("MonomInner::toTerm()")
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
              factors.push_back(getTerm(f));
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

    friend std::ostream& operator<<(std::ostream& out, const MonomInner& self) {
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

    friend bool operator<(const MonomInner& l, const MonomInner& r) {
      if (l._factors.size() < r._factors.size()) {
        return true;
      } else if (l._factors.size() > r._factors.size()) {
        return false;
      } else {
        return  l._factors < r._factors;
      }
    }

    friend bool operator==(const MonomInner& l, const MonomInner& r) {
      return l._factors == r._factors;
    }

    public:

    MonomInner& operator=(MonomInner&&) = default;
    MonomInner(MonomInner&&) = default;

    static MonomInner* monom_mul(const MonomInner& lhs, const MonomInner& rhs) {
      return MonomInner::create(MonomInner(merge_sort_with(lhs._factors,rhs._factors,
             [](int l, int r) { return l + r; },
             [](int l) { return l != 0; })));
    }

    explicit MonomInner(const MonomInner&) = default;
    explicit MonomInner(MonomInner&) = default;
  };
  struct Hasher {

    static unsigned hash(Monom::MonomInner const& x) noexcept {
      unsigned out = 0;
      for (auto f : x._factors) {
        out ^= TermListHash::hash(std::get<0>(f));
        out ^= std::hash<int>{}(std::get<1>(f));
        out <<= 1;
      }
      return out;
    }

    static bool equals(Monom::MonomInner const& lhs, Monom::MonomInner const& rhs) noexcept {
      return lhs == rhs;
    }
  };
};
/**
 * A polynomial of a specific interpreted number sort. The type parameter is expected to be an instance of NumTraits<...>, 
 * defined in NumTraits.hpp.
 */
template<class number>
class Polynom {
public:
  using Coeff = typename number::ConstantType;
  using Monom = Monom<number>;

private:
  class ComplexPolynom;

  struct Hasher;

  using Inner = Coproduct<ComplexPolynom*, Coeff>;
  Inner _inner;
  static Map<ComplexPolynom, ComplexPolynom*, Hasher> polynoms;

public:

  friend ostream& operator<<(ostream& out, const Polynom& self) { 
    self._inner.template match<void>(
          [&](ComplexPolynom* poly) { out << *poly; }
        , [&](Coeff self          ) { out << self; }
        );
    return out;
  }
  template<class Config>
  static TermList toTerm(Polynom& self) { 
    return self._inner.template match<TermList>(
          [](ComplexPolynom* self) { return ComplexPolynom::template toTerm<Config>(*self); }
        , [](Coeff self          ) { return TermList(theory->representConstant(self)); }
        );
  }
public:

  template<class Config>
  inline static Polynom poly_mul(const Polynom& lhs, const Polynom& rhs) {
    return lhs._inner.template match<Polynom>(
          [&](ComplexPolynom* const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { 
                    if(Config::usePolyMul) {
                      return Polynom(ComplexPolynom::poly_mul(*lhs, *rhs)); 
                    } else {
                      auto l = ComplexPolynom::template toTerm<Config>(*lhs);
                      auto r = ComplexPolynom::template toTerm<Config>(*rhs);
                      return Polynom(ComplexPolynom::create(ComplexPolynom(Monom(l,r))));
                    }
                  }
                , [&](Coeff           const& rhs) { return ComplexPolynom::coeff_poly_mul(rhs, lhs); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return ComplexPolynom::coeff_poly_mul(lhs, rhs); }
                , [&](Coeff           const& rhs) { return Polynom(lhs * rhs); }
                );
        });
  }

  inline static Polynom poly_add(const Polynom& lhs, const Polynom& rhs) {
    return lhs._inner.template match<Polynom>(
          [&](ComplexPolynom* const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return ComplexPolynom::poly_add(*lhs, *rhs); }
                , [&](Coeff           const& rhs) { return Polynom(ComplexPolynom::add(rhs, lhs)); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return Polynom(ComplexPolynom::add(lhs, rhs)); }
                , [&](Coeff           const& rhs) { return Polynom(lhs + rhs); }
                );
        });
  }

  Polynom(Coeff coeff, TermList t) : _inner(Inner::template variant<0>(ComplexPolynom::create(ComplexPolynom(coeff, t)))) {}
  explicit Polynom(Coeff constant)          : _inner(Inner::template variant<1>(constant)) {}
  explicit Polynom(ComplexPolynom* inner)   : _inner(Inner::template variant<0>(inner)) {} 

private:

  class ComplexPolynom {
  public:
    USE_ALLOCATOR(ComplexPolynom)
    CLASS_NAME(ComplexPolynom)

  private:
    vector<tuple<Monom, Coeff>> _coeffs;
    Lib::Optional<TermList> _toTerm;
    using poly_pair = typename decltype(_coeffs)::value_type;

  public:

    ComplexPolynom(Coeff coeff, Monom&& t) : _coeffs(decltype(_coeffs)())  { 
      _coeffs.emplace_back(poly_pair(std::move(t), coeff));
    }

    ComplexPolynom(Monom&& t) : _coeffs(decltype(_coeffs)())  { 
      _coeffs.emplace_back(poly_pair(std::move(t), Coeff(1)));
    }

    ComplexPolynom(Coeff coeff, TermList t) : ComplexPolynom(coeff, Monom(t))  { 
      // _coeffs.emplace_back(poly_pair(Monom(t), coeff));
    }

    ComplexPolynom(Coeff constant) : _coeffs(decltype(_coeffs)())  { 
      CALL("ComplexPolynom::ComplexPolynom(Coeff)")
      if (constant != number::zeroC)
        _coeffs.emplace_back(poly_pair(Monom(), constant));
    }

    ComplexPolynom(decltype(_coeffs) coeffs) : _coeffs(coeffs) { }

    ComplexPolynom() : _coeffs(decltype(_coeffs)()) {
    }

    ComplexPolynom(ComplexPolynom&& other) = default;
    explicit ComplexPolynom(const ComplexPolynom&) = default;

    ComplexPolynom& operator=(ComplexPolynom&& other) = default;


    static ComplexPolynom* create(ComplexPolynom&& self) {
      return polynoms.getOrInit(ComplexPolynom(self), 
          [=](ComplexPolynom** toInit) { *toInit = new ComplexPolynom(std::move(self)); });
    }

    friend bool operator==(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
      return lhs._coeffs == rhs._coeffs;
    }

    static Monom& getMonom(poly_pair& pair) {
      return std::get<0>(pair);
    }

    static const Monom& getMonom(const poly_pair& pair) {
      return std::get<0>(pair);
    }

    static const Coeff& getCoeff(const poly_pair& pair) {
      return std::get<1>(pair);
    }

    static Coeff& getCoeffMut(poly_pair& pair) {
      return std::get<1>(pair);
    }

    static Polynom poly_add(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
      CALL("ComplexPolynom::poly_add")
      ASS(!lhs._coeffs.empty())
      ASS(!rhs._coeffs.empty())
      auto newCoeffs = merge_sort_with(lhs._coeffs, rhs._coeffs, 
              [](Coeff l, Coeff r){ return l + r; },
              [](Coeff x){ return x != number::zeroC; }
            );
      // if (newCoeffs.empty())  {
      //   return Polynom(Coeff(0));
      // } else {
        return Polynom(ComplexPolynom::create(ComplexPolynom(std::move(newCoeffs))));
      // }
    }

    inline static ComplexPolynom* add(Coeff coeff, ComplexPolynom* old_) {
      CALL("ComplexPolynom::add(Coeff coeff, const ComplexPolynom& old) ")
      const auto& oldPoly = *old_;

      ASS(!oldPoly._coeffs.empty())
      if (coeff == Coeff(0)) {
        return old_;
      } 

      ComplexPolynom newPoly;
      if (getMonom(oldPoly._coeffs[0]).isOne()) {
        ASS(oldPoly._coeffs.begin() != oldPoly._coeffs.end())

        auto newVal = getCoeff(oldPoly._coeffs[0]) + coeff;
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
          getCoeffMut(newPoly._coeffs[0]) = newVal;
        }
      } else {
        newPoly._coeffs.reserve(oldPoly._coeffs.size() + 1);
        newPoly._coeffs.push_back(poly_pair(Monom(), coeff));
        for (auto& f : oldPoly._coeffs) {
          // newPoly.push_back(poly_pair(Monom(getMonom(p), getMonom())))
          newPoly._coeffs.push_back(poly_pair(f));
        }
      }

      // DBG("in : ", oldPoly, "\t+\t", coeff)
      // DBG("out: ", newPoly)

      return ComplexPolynom::create(std::move(newPoly));
    }

    static Polynom coeff_poly_mul(Coeff coeff, ComplexPolynom* old_) {
      CALL("ComplexPolynom::coeff_poly_mul(Coeff coeff, ComplexPolynom* old) ")
      const auto& old = *old_;

      if (coeff == Coeff(0)) {
        return Polynom(Coeff(0));

      } else if (coeff == Coeff(1)) {
        return Polynom(old_);

      } else {
        ComplexPolynom newPoly;

        newPoly._coeffs.reserve(old._coeffs.size());
        for (auto& p : old._coeffs) {
          newPoly._coeffs.push_back(poly_pair(Monom(getMonom(p)), coeff * getCoeff(p)));
        }

        return Polynom(ComplexPolynom::create(std::move(newPoly)));
      }
    }

    static ComplexPolynom* poly_mul(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {

      CALL("ComplexPolynom::poly_mul");
      DEBUG("lhs: ", lhs);
      DEBUG("rhs: ", rhs);

      map<Monom, Coeff> prods;

      for (auto& l : lhs._coeffs) {
        for (auto& r : rhs._coeffs) {
          Monom monom = Monom::monom_mul( getMonom(l), getMonom(r));
          auto coeff = getCoeff(l) * getCoeff(r);
          auto res = prods.emplace(make_pair(move(monom), coeff));
          if (!res.second) {
            auto& iter = res.first;
            ASS(iter != prods.end());
            iter->second = iter->second + coeff;
          }
        }
      }
      ComplexPolynom out;
      out._coeffs.reserve(prods.size());
      for (auto iter = prods.begin(); iter != prods.end(); iter++) {
        auto coeff = iter->second;
        if (coeff != number::zeroC) {
          out._coeffs.emplace_back(poly_pair(iter->first, coeff)); 
        }
      }
      DEBUG("out: ", out);
      out.integrity();
      return ComplexPolynom::create(std::move(out));
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
    static TermList toTerm(ComplexPolynom& self) {
      CALL("ComplexPolynom::toTerm() const")
      return self._toTerm.unwrapOrInit([&]() {
        // self.integrity();
        
        auto trm = [](poly_pair& x) -> TermList { 

          if (getMonom(x).isOne()) {  
            /* the pair is a plain number */
            return TermList( theory->representConstant(getCoeff(x)) );

          } else if (getCoeff(x)== number::constant(1)) {
            /* the pair is an uninterpreted term */
            return getMonom(x).template toTerm<Config>();

          } else if (getCoeff(x)== number::constant(-1)) {
            return TermList(number::minus(getMonom(x).template toTerm<Config>()));

          } else {
            return TermList(number::mul(TermList( theory->representConstant(getCoeff(x)) ), getMonom(x).template toTerm<Config>())); 
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
        out << getMonom(*iter)<< " * " << getCoeff(*iter);
        iter++;
        for (; iter != self._coeffs.end(); iter++) {
          out << " + " << getMonom(*iter)<< " * " << getCoeff(*iter);
        }
      }
      return out;
    }

    friend struct Hasher;
  };
  struct Hasher {
    static unsigned hash(Polynom::ComplexPolynom const& x) noexcept {
      unsigned out = 0;
      for (auto c : x._coeffs) {
        out ^= ComplexPolynom::getMonom(c).hash();
        out ^= ComplexPolynom::getCoeff(c).hash();
        out <<= 1;
      }
      return out;
    }
    static bool equals(Polynom::ComplexPolynom const& lhs, Polynom::ComplexPolynom const& rhs) {
      return lhs == rhs;
    }
  };
};


struct AnyPoly {
  
  template<class C>
  using poly = Polynom<NumTraits<C>>;
  using self_t = Coproduct< poly<IntegerConstantType> , poly<RationalConstantType> , poly<RealConstantType> >;
  self_t self; 

  explicit AnyPoly(poly<IntegerConstantType>&& x) : self(self_t::variant<0>(std::move(x))) {
    CALL("AnyPoly(Int)")
  }
  explicit AnyPoly(poly<RationalConstantType>&& x ) : self(self_t::variant<1>(std::move(x))) {
    CALL("AnyPoly(Rat)")
  }
  explicit AnyPoly(poly<RealConstantType>&& x ) : self(self_t::variant<2>(std::move(x))) {
    CALL("AnyPoly(Real)")
  }

  template<class Const> const poly<Const>& ref() const;

  template<> const poly<IntegerConstantType>& ref<IntegerConstantType>() const 
  { return self.unwrap<0>();  }
  template<> const poly<RationalConstantType>& ref<RationalConstantType>() const 
  { return self.unwrap<1>();  }
  template<> const poly<RealConstantType>& ref<RealConstantType>() const 
  { return self.unwrap<2>();  }

  template<class Const> poly<Const>& ref_mut();

  template<> poly<IntegerConstantType>& ref_mut<IntegerConstantType>() 
  { return self.unwrap<0>();  }
  template<> poly<RationalConstantType>& ref_mut<RationalConstantType>()
  { return self.unwrap<1>();  }
  template<> poly<RealConstantType>& ref_mut<RealConstantType>() 
  { return self.unwrap<2>();  }

  template<class Const>
  void set(TermList t, Const c) {
    CALL("AnyPoly::set")
    return ref_mut<Const>().set(t,c);
  }

  template<class Const>
  Const get(TermList t) {
    CALL("AnyPoly::get")
    return ref_mut<Const>().get(t);
  }

  template<class Const, class Config>
  TermList toTerm() {
    CALL("AnyPoly::toTerm")
    return poly<Const>::template toTerm<Config>(ref_mut<Const>());
  }

  template<class Config>
  TermList toTerm_() {
    CALL("AnyPoly::toTerm_")
      //TODO replace with match

    if (self.is<0>()) {
      using ty = typename self_t::type<0>::value::Coeff;
      return toTerm<ty, Config>();

    } else if (self.is<1>()) {
      using ty = typename self_t::type<1>::value::Coeff;
      return toTerm<ty, Config>();

    } else {
      ASS(self.is<2>())
      using ty = typename self_t::type<2>::value::Coeff;
      return toTerm<ty, Config>();
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& x) {
    auto& self = x.self;
    if (self.is<0>()) {
      out << self.unwrap<0>();
    } else if (self.is<1>()) {
      out << self.unwrap<1>();
    } else {
      out << self.unwrap<2>();
    }
    return out;
  }
  AnyPoly& operator=(AnyPoly&&) = default;
  AnyPoly(AnyPoly&&) = default;
  explicit AnyPoly(const AnyPoly&) = default;
private:
};

} // namespace Kernel

#undef DEBUG

#endif // __POLYNOMIAL__H__

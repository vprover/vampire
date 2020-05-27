#include "PolynomialNormalizer.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include <stack>

#define DEBUG(...) // DBG(__VA_ARGS__)

#define TODO throw "TODO";

using namespace Lib;

namespace Kernel {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// TERM SORTING (ONLY IN DEBUG MODE)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#if VDEBUG
bool expensive_sort_terms(TermList lhs, TermList rhs);

struct expensive_term_comparison {
  bool operator()(TermList lhs, TermList rhs) const {
    return expensive_sort_terms(lhs, rhs);
  }
};

int _expensive_sort_terms(const Term& lhs, const TermList& rhs);
int _expensive_sort_terms(TermList lhs, TermList rhs);

int _expensive_sort_terms(const Term& lhs, const Term& rhs) {

  int l_fun = lhs.functor();
  int r_fun = rhs.functor();

  int l_thry = theory->isInterpretedFunction(l_fun);
  int r_thry = theory->isInterpretedFunction(r_fun);
  int cmp_thry = l_thry - r_thry;

  if (cmp_thry != 0) return cmp_thry;
  if (l_thry) {
    ASS(r_thry)

    int l_inter = theory->interpretFunction(l_fun);
    int r_inter = theory->interpretFunction(r_fun);
    int cmp_inter = l_inter - r_inter;

    if (cmp_inter != 0) return cmp_inter;

  } else {
    ASS(!l_thry && !r_thry)
 
    const vstring& lname = env.signature->getFunction(l_fun)->name();
    const vstring& rname = env.signature->getFunction(r_fun)->name();
    if (l_fun == r_fun) {

    } else if (lname < rname) {
      return -1;
    } else {
      return 1;
    }
    // if (cmp_fun != 0) return cmp_fun;
 }

  ASS(lhs.arity() == rhs.arity())
  for (int i = 0; i < lhs.arity(); i++) {
    auto cmp = _expensive_sort_terms(lhs[i], rhs[i]);
    if (cmp != 0) {
      return cmp;
    }
  }
  return 0;
}

bool expensive_sort_terms(TermList lhs, TermList rhs) {
  auto out = _expensive_sort_terms(lhs, rhs) < 0;
  // DBG("comparing: ", lhs, " < ", rhs, " ==> ", out);
  return out;
}

int _expensive_sort_terms(TermList lhs, TermList rhs) {
  auto l_trm = lhs.isTerm();
  auto r_trm = rhs.isTerm();
  auto cmp_trm = l_trm - r_trm;
  if (cmp_trm != 0) return cmp_trm;

  if (l_trm) {
    ASS(r_trm);
    return _expensive_sort_terms(*lhs.term(), *rhs.term());
  } else {
    ASS(lhs.isVar() && rhs.isVar());
    return int(lhs.var()) - int(rhs.var());
  }

}

#endif // VDEBUG

struct compare_terms {
  bool operator()(TermList lhs, TermList rhs) const {
#if VDEBUG
    auto out = expensive_sort_terms(lhs,rhs);
#else
    auto out = lhs < rhs;
#endif // VDEBUG
    return out;
  }
};


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Data structures
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class K, class V, class Compare = std::less<K>> using map  = std::map<K, V, Compare, STLAllocator<std::pair<const K, V > > >;

template<
    class Key,
    class Hash = std::hash<Key>,
    class KeyEqual = std::equal_to<Key>
> using unordered_set = std::unordered_set<Key, Hash, KeyEqual, STLAllocator<Key>>;

template<
    class Key,
    class V,
    class Hash = std::hash<Key>,
    class KeyEqual = std::equal_to<Key>
> using unordered_map = std::unordered_map<Key, V, Hash, KeyEqual, STLAllocator<std::pair<const Key, V>>>;

template<class t> using vector  = std::vector<t, STLAllocator<t>>;
template<class t> using stack  = std::stack<t, STLAllocator<t>>;

    struct WrappedTermList {
      USE_ALLOCATOR(WrappedTermList)
      CLASS_NAME(WrappedTermList)
      TermList inner;
      explicit WrappedTermList(TermList t) : inner(t) { }

      friend bool operator<(WrappedTermList lhs, WrappedTermList rhs) {
        return compare_terms{}(lhs.inner,rhs.inner);
      }

      friend bool operator==(WrappedTermList lhs, WrappedTermList rhs) {
        return lhs.inner == rhs.inner;
      }
      size_t hash() const {
        return TermListHash::hash(inner);
      }
    };



template<class number>
class Monom { 
public:
  using Coeff = typename number::ConstantType;
  class MonomInner;
  struct hasher;
private:
  MonomInner const& _inner;
  static unordered_map<MonomInner, MonomInner*, hasher> monoms;

public:

  bool isOne() const {return _inner.isOne();}

  TermList toTerm() const {return _inner.toTerm();}

  friend bool operator<(const Monom& lhs, const Monom& rhs) { return lhs._inner < rhs._inner; }

  friend bool operator==(const Monom& lhs, const Monom& rhs) {return &lhs._inner == &rhs._inner;}
  size_t hash() const { return std::hash<size_t>{}((size_t)&_inner); }

  friend ostream& operator<<(ostream& out, const Monom& m) {return out << m._inner;}

  Monom(const MonomInner& inner) : _inner(inner) {}

  Monom(TermList t) : _inner(MonomInner::create(MonomInner(t))) {}

  Monom() : _inner(MonomInner::create(MonomInner())) {}

  static Monom monom_mul(const Monom& lhs, const Monom& rhs) {
    return Monom(MonomInner::monom_mul(lhs._inner, rhs._inner));
  }

  class MonomInner {
    vector<tuple<WrappedTermList, int>> _factors;
    friend class Monom;

    // empty monom == 1
    static const MonomInner& create(const MonomInner& self) {
      CALL("MonomInner::create(MonomInner&&)")
      auto pos = monoms.find(self);
      if (pos == monoms.end()) {
        auto alloc = new MonomInner(self);
        auto res = monoms.emplace(make_pair(std::move(self), alloc));
        ASS(res.second);
        pos = res.first;
      } else {
      }
      return *pos->second;
    }
    MonomInner() : _factors(decltype(_factors)()) {
    }

    MonomInner(TermList t) : _factors(decltype(_factors)()) {
      _factors.emplace_back(make_tuple(t, 1));
    }

    public:

      USE_ALLOCATOR(MonomInner)
      CLASS_NAME(MonomInner)
      using monom_pair = typename decltype(_factors)::value_type;

    static TermList getTerm(const typename decltype(_factors)::value_type& pair) {
      return std::get<0>(pair).inner;
    }

    static int getCount(const typename decltype(_factors)::value_type& pair) {
      return std::get<1>(pair);
    }

    bool isOne() const  {
      return _factors.begin() == _factors.end();
    }

    TermList toTerm() const {
      //TODO memo
      CALL("MonomInner::toTerm()")
        auto iter = _factors.rbegin();
      if (iter == _factors.rend()) {
        return number::one();
      } else {

        auto mul_n_times = [](TermList wrap, TermList t, int cnt) {
          TermList out = wrap;
          for (int i = 0; i < cnt; i++) {
            out = number::mul(t, out);
          }
          return out;
        };

        ASS(getCount(*iter) != 0);
        auto out = mul_n_times(getTerm(*iter), getTerm(*iter), getCount(*iter) - 1);
        iter++;
        for(; iter != _factors.rend(); iter++)  {
          out = mul_n_times(out, getTerm(*iter), getCount(*iter));
        }
        return out;
      }
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

    static const MonomInner& monom_mul(const MonomInner& lhs, const MonomInner& rhs) {
      MonomInner out;
      auto l = lhs._factors.begin();
      auto r = rhs._factors.begin();
      auto insert = [&](TermList term, int value) {
        if (value != 0)
          out._factors.emplace_back(make_pair(term, value));
      };
      while (l != lhs._factors.end() && r != rhs._factors.end() ) {
        if (getTerm(*l) == getTerm(*r) ) {
          //add up
          insert(getTerm(*l) , getCount(*l) + getCount(*r));
          l++;
          r++;
        } else if (compare_terms{}(getTerm(*l), getTerm(*r)) ) {
          // insert l
          insert(getTerm(*l) , getCount(*l));
          l++;
        } else {
          // insert r
          insert(getTerm(*r) , getCount(*r));
          r++;
        }
      }
      while (l != lhs._factors.end()) {
        insert(getTerm(*l) , getCount(*l));
        l++;
      }
      while (r != rhs._factors.end()) {
        insert(getTerm(*r) , getCount(*r));
        r++;
      }
      ASS(l == lhs._factors.end() && r == rhs._factors.end());
      return MonomInner::create(std::move(out));
    }

    explicit MonomInner(const MonomInner&) = default;
    private:
  };
  struct hasher {
    size_t operator()(Monom::MonomInner const& x) const noexcept {
      size_t out = 0;
      for (auto f : x._factors) {
        out ^= std::get<0>(f).hash();
        out ^= std::hash<int>{}(std::get<1>(f));
        out <<= 1;
      }
      return out;
    }
  };
};


/**
 * A polynomial of a specific interpreted number sort. The type parameter is expected to be an instance of num_traits<...>, 
 * defined in num_traits.hpp.
 */
template<class number>
class Polynom {
  class PolynomInner;

  struct hasher;
  PolynomInner const& _inner;
  static unordered_map<PolynomInner, PolynomInner*, hasher> polynoms;
public:
  using Coeff = typename number::ConstantType;
  using Monom = Monom<number>;

  friend ostream& operator<<(ostream& out, const Polynom& self) { return out << self._inner; }
  static TermList toTerm(const Polynom& self) { return PolynomInner::toTerm(self._inner); }
  static Polynom poly_mul(const Polynom& lhs, const Polynom& rhs) {
    return Polynom(PolynomInner::poly_mul(lhs._inner, rhs._inner));
  }
  static Polynom poly_add(const Polynom& lhs, const Polynom& rhs) {
    return Polynom(PolynomInner::poly_add(lhs._inner, rhs._inner));
  }

  Polynom(Coeff coeff, TermList t) : _inner(PolynomInner::create(PolynomInner(coeff, t))) {}
  Polynom(Coeff constant) : _inner(PolynomInner::create(constant)) {}
  Polynom(const PolynomInner& inner) : _inner(inner){} 

private:

  class PolynomInner {
  public:
    USE_ALLOCATOR(PolynomInner)
    CLASS_NAME(PolynomInner)

  private:
    // static unordered_map<PolynomInner<number>, PolynomInner<number> const *const > polys;
    vector<tuple<Monom, Coeff>> _coeffs;
    using poly_pair = typename decltype(_coeffs)::value_type;

  public:
    static const PolynomInner& create(PolynomInner&& self_) {
      auto self = std::move(self_);
      const PolynomInner& x = self;
      CALL("PolynomInner::create(PolynomInner&&)")
      auto pos = polynoms.find(x);
      if (pos == polynoms.end()) {
        auto alloc = new PolynomInner(std::move(self));
        auto res = polynoms.emplace(make_pair(PolynomInner(*alloc), alloc));
        ASS(res.second);
        pos = res.first;
      }
      return *pos->second;
    }

    friend bool operator==(const PolynomInner& lhs, const PolynomInner& rhs) {
      return lhs._coeffs == rhs._coeffs;
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

    static const PolynomInner& poly_add(const PolynomInner& lhs, const PolynomInner& rhs) {
      CALL("PolynomInner::poly_add")

      PolynomInner out;
      // TODO memoization
      // TODO unify with Monom::operator+
      auto l = lhs._coeffs.begin();
      auto r = rhs._coeffs.begin();
      auto insert = [&](const Monom& monom, Coeff value) {
        if (value != number::zeroC)
          out._coeffs.emplace_back(make_pair(Monom(monom), value));
      };
      while (l != lhs._coeffs.end() && r != rhs._coeffs.end() ) {
        if (getMonom(*l) == getMonom(*r)) {
          //add up
          insert(getMonom(*l), getCoeff(*l) + getCoeff(*r));
          l++;
          r++;
        } else if (getMonom(*l)< getMonom(*r)) {
          // insert l
          insert(getMonom(*l), getCoeff(*l));
          l++;
        } else {
          // insert r
          insert(getMonom(*r), getCoeff(*r));
          r++;
        }
      }
      while (l != lhs._coeffs.end()) {
        insert(getMonom(*l), getCoeff(*l));
        l++;
      }
      while (r != rhs._coeffs.end()) {
        insert(getMonom(*r), getCoeff(*r));
        r++;
      }
      ASS(l == lhs._coeffs.end() && r == rhs._coeffs.end());
      out.integrity();
      return PolynomInner::create(std::move(out));
    }

    static const PolynomInner& poly_mul(const PolynomInner& lhs, const PolynomInner& rhs) {

      CALL("PolynomInner::poly_mul")
      DEBUG("lhs: ", lhs)
      DEBUG("rhs: ", rhs)

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
      PolynomInner out;
      out._coeffs.reserve(prods.size());
      for (auto iter = prods.begin(); iter != prods.end(); iter++) {
        auto coeff = iter->second;
        if (coeff != number::zeroC) {
          out._coeffs.emplace_back(poly_pair(Monom(iter->first), coeff)); // TODO try implicit copy
        }
      }
      DEBUG("out: ", out)
      out.integrity();
      return PolynomInner::create(std::move(out));
    }

    PolynomInner(Coeff coeff, TermList t) : _coeffs(decltype(_coeffs)())  { 
      CALL("PolynomInner::PolynomInner(Coeff, TermList)")
      _coeffs.emplace_back(poly_pair(std::move(Monom(t)), coeff));
    }

    PolynomInner(Coeff constant) : _coeffs(decltype(_coeffs)())  { 
      CALL("PolynomInner::PolynomInner(Coeff)")
      if (constant != number::zeroC)
        _coeffs.emplace_back(poly_pair(Monom(), constant));
    }

    PolynomInner() : _coeffs(decltype(_coeffs)()) {
      CALL("PolynomInner::PolynomInner()")
    }

    PolynomInner(PolynomInner&& other) = default;
    explicit PolynomInner(const PolynomInner&) = default;

    PolynomInner& operator=(PolynomInner&& other) = default;

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

    static TermList toTerm(const PolynomInner& self) {
      CALL("PolynomInner::toTerm() const")
      self.integrity();
      auto trm = [](const poly_pair& x) -> TermList { 

        if (getMonom(x).isOne()) {  
          /* the pair is a plain number */
          return TermList( theory->representConstant(getCoeff(x)) );

        } else if (getCoeff(x)== number::constant(1)) {
          /* the pair is an uninterpreted term */
          return getMonom(x).toTerm();

        } else if (getCoeff(x)== number::constant(-1)) {
          return TermList(number::minus(getMonom(x).toTerm()));

        } else {
          return TermList(number::mul(TermList( theory->representConstant(getCoeff(x)) ), getMonom(x).toTerm())); 
        }
      };

      auto iter = self._coeffs.rbegin(); 
      if (iter == self._coeffs.rend()) {
        return TermList(number::zero());
      } else {
        auto out = trm(*iter);
        iter++;
        for (; iter != self._coeffs.rend(); iter++) {
          out = number::add(trm(*iter), out);
        }
        return out;
      }
    }

    friend std::ostream& operator<<(std::ostream& out, const PolynomInner& self) {
      auto iter = self._coeffs.begin();
      if ( iter == self._coeffs.end() ) {
        out << "0" << endl;
      } else {
        out << getMonom(*iter)<< " * " << getCoeff(*iter);
        iter++;
        for (; iter != self._coeffs.end(); iter++) {
          out << " + " << getMonom(*iter)<< " * " << getCoeff(*iter);
        }
      }
      return out;
    }

    friend struct hasher;
  };
  struct hasher {
    size_t operator()(Polynom::PolynomInner const& x) const noexcept {
      size_t out = 0;
      for (auto c : x._coeffs) {
        out ^= PolynomInner::getMonom(c).hash();
        out ^= PolynomInner::getCoeff(c).hash();
        out <<= 1;
      }
      return out;
    }
  };
};

struct AnyPoly {
  
  template<class C>
  using poly = Polynom<num_traits<C>>;
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

  // template<class Const>
  // void multiply(Const c) {
  //   CALL("AnyPoly::multiply")
  //   return ref_mut<Const>().multiply(c);
  // }

  template<class Const>
  Const get(TermList t) {
    CALL("AnyPoly::get")
    return ref_mut<Const>().get(t);
  }

  template<class Const>
  TermList toTerm() const {
    CALL("AnyPoly::toTerm")
    return poly<Const>::toTerm(ref<Const>());
  }

  TermList toTerm_() const {
    CALL("AnyPoly::toTerm_")

    if (self.is<0>()) {
    // if (self.isLeft()) {
      // using ty = typename self_t::left_t::Coeff;
      using ty = typename self_t::type<0>::value::Coeff;
      return toTerm<ty>();

    } else if (self.is<1>()) {
    // } else if (self.unwrapRight().isLeft()) {
      // using ty = typename self_t::right_t::left_t::Coeff;
      using ty = typename self_t::type<1>::value::Coeff;
      return toTerm<ty>();

    } else {
      ASS(self.is<2>())
      // using ty = typename self_t::right_t::right_t::Coeff;
      using ty = typename self_t::type<2>::value::Coeff;
      return toTerm<ty>();
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& x) {
    auto& self = x.self;
    if (self.is<0>()) {
    // if (self.isLeft()) {
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

namespace Kernel {



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number> inline LitEvalResult interpret_equality(Literal* lit, bool polarity, TermList lhs, TermList rhs) {
  using Const = typename number::ConstantType;
  Const l;
  Const r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::right(polarity == (l == r));
  } else {
    return LitEvalResult::left(Literal::createEquality(lit->polarity(), lhs, rhs, number::sort));
  }
}

template<> LitEvalResult PolynomialNormalizer::evaluateLit<Interpretation::EQUAL>(Literal* lit) const {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::right(lit->polarity());
  auto sort =  SortHelper::getEqualityArgumentSort(lit);
  switch (sort) {
    case Sorts::SRT_INTEGER:  return interpret_equality<num_traits<IntegerConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_RATIONAL: return interpret_equality<num_traits<RationalConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_REAL:     return interpret_equality<num_traits<RealConstantType>>(lit, lit->polarity(), lhs, rhs);
                             //TODO lift to term algebras
    default:
      return LitEvalResult::right(Literal::createEquality(lit->polarity(), lhs, rhs, sort));
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> LitEvalResult PolynomialNormalizer::evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) const {
  ASS(lit->arity() == 2);
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::right(lit->polarity() != strict);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::right(lit->polarity() == evalIneq(l, r));
  } else {
    return LitEvalResult::left(lit);
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op) \
  template<> LitEvalResult PolynomialNormalizer::evaluateLit<num_traits<Const>::name ## I>(Literal* lit) const \
  { return evaluateInequality<Const>(lit, STRICT, [](Const l, Const r) {return l op r;}); } \

#define IMPL_INEQUALTIES(Const) \
   /*                inequality| is strict? | operator */ \
  __IMPL_INEQ(Const, less      ,   true     ,  <        ) \
  __IMPL_INEQ(Const, leq       ,   false    ,  <=       ) \
  __IMPL_INEQ(Const, greater   ,   true     ,  >        ) \
  __IMPL_INEQ(Const, geq       ,   false    ,  >=       ) \


IMPL_INEQUALTIES(RationalConstantType)
IMPL_INEQUALTIES(RealConstantType) 
IMPL_INEQUALTIES(IntegerConstantType)

#undef  IMPL_NUM_EVALS
#undef  __IMPL_INEQ

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// INT_DIVIDES
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<> LitEvalResult PolynomialNormalizer::evaluateLit<Interpretation::INT_DIVIDES>(Literal* lit) const {
  return tryEvalConstant2<IntegerConstantType>(lit, [](IntegerConstantType l, IntegerConstantType r) { 
      return  (r % l) == 0;
  });
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// UNARY_MINUS 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
TermEvalResult evaluateUnaryMinus(TermEvalResult& inner) {
  auto out = inner.map(
      [](const TermList& t) { 
        return TermEvalResult::rightMv(AnyPoly(
            Polynom<number>( number::constant(-1), t)
            ));
      },
      [](const AnyPoly& p) {
        // p.multiply(number::constant(-1)); 
        auto minusOne = Polynom<number>(number::constant(-1));
        auto out = Polynom<number>::poly_mul(minusOne, p.ref<typename number::ConstantType>());//TODO speed this up
        return TermEvalResult::rightMv(AnyPoly(std::move(out)));
      });
  return out;
}

#define IMPL_UNARY_MINUS(Const) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<num_traits<Const>::minusI>(Term* orig, TermEvalResult* evaluatedArgs) const  \
  { \
    CALL("PolynomialNormalizer::evaluateFun<num_traits<" #Const ">::minusI>(Term* trm, TermEvalResult* evaluatedArgs)") \
    auto out = evaluateUnaryMinus<num_traits<Const>>(evaluatedArgs[0]);  \
    return out; \
  } \

  IMPL_UNARY_MINUS(RealConstantType    )
  IMPL_UNARY_MINUS(RationalConstantType)
  IMPL_UNARY_MINUS(IntegerConstantType )

#undef IMPL_UNARY_MINUS


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MULTIPLY
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number> 
TermEvalResult PolynomialNormalizer::evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs) const 
{
  using Const = typename number::ConstantType;
  using poly = Polynom<number>;
  if (_usePolyMul) {
    auto l = lhs.collapse<poly>(
        [](TermList&& t) { 
          return poly(number::constant(1), t);
        },
        [](AnyPoly&& p) {
          return std::move(p.ref_mut<Const>());
        });

    auto r = rhs.collapse<poly>(
        [](TermList&& t) { 
          return poly(number::constant(1), t);
        },
        [](AnyPoly&& p) {
          return std::move(p.ref_mut<Const>());
        });

    return TermEvalResult::rightMv(AnyPoly(poly::poly_mul(l, r)));
  } else {

    auto toTerm = [](TermEvalResult&& res) {
      return res.collapse<TermList>(
        [](TermList&& t) { 
          return t;
        },
        [](AnyPoly&& p) {
          return p.toTerm_();
        });
    };

    auto l = toTerm(std::move(lhs));
    auto r = toTerm(std::move(rhs));

    if ( WrappedTermList(r) < WrappedTermList(l) ) {
      std::swap(l,r);
    }

    return TermEvalResult::leftMv(TermList(number::mul(l, r)));
  }
}


#define IMPL_MULTIPLY(Const) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<num_traits<Const>::mulI>(Term* orig, TermEvalResult* evaluatedArgs) const  \
  { \
    CALL("PolynomialNormalizer::evaluateFun<num_traits<" #Const ">::mulI>(Term* trm, TermEvalResult* evaluatedArgs)") \
    return evaluateMul<num_traits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
  } \

  IMPL_MULTIPLY(RealConstantType    )
  IMPL_MULTIPLY(RationalConstantType)
  IMPL_MULTIPLY(IntegerConstantType )

#undef IMPL_MULTIPLY


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ADD 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
Polynom<number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs) {
  CALL("Polynom<number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs)")
  using Const = typename number::ConstantType;
  using poly = Polynom<number>;

  poly l = lhs.collapse<poly>(
      [](TermList&& t) { 
        return poly(number::constant(1), t);
      },
      [](AnyPoly&& p) {
        return std::move(p.ref_mut<Const>());
      });

  poly r = rhs.collapse<poly>(
      [](TermList&& t) { 
        return poly(number::constant(1), t);
      },
      [](AnyPoly&& p) {
        return std::move(p.ref_mut<Const>());
      });
  
  return poly::poly_add(l, r);
}


#define IMPL_ADD(Const) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<num_traits<Const>::addI>(Term* orig, TermEvalResult* evaluatedArgs) const  \
  { \
    CALL("PolynomialNormalizer::evaluateFun<num_traits<" #Const ">::addI>(Term* trm, TermEvalResult* evaluatedArgs)") \
    auto poly = evaluateAdd<num_traits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
    auto out = TermEvalResult::rightMv(AnyPoly(std::move(poly))); \
    return out; \
  } \

  IMPL_ADD(RealConstantType    )
  IMPL_ADD(RationalConstantType)
  IMPL_ADD(IntegerConstantType )

#undef IMPL_ADD


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Number Constants 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
TermEvalResult evaluateConst(typename number::ConstantType c) {
  return TermEvalResult::rightMv(AnyPoly(Polynom<number>(c)));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Functions that are only handled for constants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define IMPL_EVAL_UNARY(Const, INTER, expr) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<Interpretation::INTER>(Term* orig, TermEvalResult* evaluatedArgs) const   \
  {  return tryEvalConstant1<Const>(orig, evaluatedArgs, [] (Const x) { return expr; }); } 

#define IMPL_EVAL_BINARY(Const, INTER, expr) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<Interpretation::INTER>(Term* orig, TermEvalResult* evaluatedArgs) const   \
  {  return tryEvalConstant2<Const>(orig, evaluatedArgs, [] (Const l, Const r) { return expr; }); } 


/////////////////// Integer only functions

IMPL_EVAL_UNARY(IntegerConstantType, INT_ABS      , x >= 0 ? x : -x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_SUCCESSOR, x + 1          )

/////////////////// INT_QUOTIENT_E and friends

#define IMPL_QUOTIENT_REMAINDER(Const, NUM, SUFFIX) \
  IMPL_EVAL_BINARY(Const, NUM ##  _QUOTIENT_ ## SUFFIX,  l.quotient ## SUFFIX(r)) \
  IMPL_EVAL_BINARY(Const, NUM ## _REMAINDER_ ## SUFFIX,  l - (l.quotient ## SUFFIX (r)*r)) \

#define IMPL_QUOTIENT_REMAINDERS(Const, NUM) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, E) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, T) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, F) \
  IMPL_EVAL_BINARY(Const, NUM ## _MINUS, l - r) \

  IMPL_QUOTIENT_REMAINDERS(RealConstantType    , REAL)
  IMPL_QUOTIENT_REMAINDERS(RationalConstantType, RAT )
  IMPL_QUOTIENT_REMAINDERS(IntegerConstantType , INT )

#undef IMPL_QUOTIENT_REMAINDER
#undef IMPL_QUOTIENT_REMAINDERS

/////////////////// INT_FLOOR and friends

// have no effect for ints
IMPL_EVAL_UNARY(IntegerConstantType, INT_FLOOR   , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_CEILING , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_TRUNCATE, x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_ROUND   , x)

// same impl for fractionals
#define IMPL_FRAC_FLOOR_FRIENDS(Const, NUM) \
  IMPL_EVAL_UNARY(Const, NUM ## _FLOOR, x.floor()) \
  IMPL_EVAL_UNARY(Const, NUM ## _CEILING, x.ceiling()) \
  IMPL_EVAL_UNARY(Const, NUM ## _TRUNCATE, x.truncate()) \

  IMPL_FRAC_FLOOR_FRIENDS(RealConstantType    , REAL)
  IMPL_FRAC_FLOOR_FRIENDS(RationalConstantType, RAT)

#undef IMPL_EVAL_FRAC_FLOOR_FRIENDS
 
/////////////////// RAT_TO_INT and friends

#define IMPL_NUM_CVT(Const, NUM) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_INT, IntegerConstantType::floor(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_RAT, RationalConstantType(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_REAL, RealConstantType(x)) \

  IMPL_NUM_CVT(RealConstantType    , REAL)
  IMPL_NUM_CVT(RationalConstantType, RAT )
  IMPL_NUM_CVT(IntegerConstantType , INT )

#undef IMPL_NUM_CVT

/////////////////// QUOTIENT 
//
#define IMPL_QUOTIENT(Const, NUM) \
    IMPL_EVAL_BINARY(Const, NUM ## _QUOTIENT, l / r) \

  IMPL_QUOTIENT(RealConstantType    , REAL)
  IMPL_QUOTIENT(RationalConstantType, RAT )

#undef IMPL_QUOTIENT
 

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround>
LitEvalResult PolynomialNormalizer::tryEvalConstant1(Literal* lit, EvalGround fun) const {
  auto lhs = *lit->nthArgument(0);
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return LitEvalResult::right(fun(l));
  } else {
    return LitEvalResult::left(lit);
  }
}


template<class ConstantType, class EvalGround>
LitEvalResult PolynomialNormalizer::tryEvalConstant2(Literal* lit, EvalGround fun) const {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::right(fun(l,r));
  } else {
    return LitEvalResult::left(lit);
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult PolynomialNormalizer::tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const {

  TermList lhs = evaluatedArgs[0].unwrapLeft();
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return TermEvalResult::left(TermList(theory->representConstant(fun(l))));
  } else {
    return TermEvalResult::left(TermList(orig));
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult PolynomialNormalizer::tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const {

  TermList lhs = evaluatedArgs[0].unwrapLeft();
  TermList rhs = evaluatedArgs[1].unwrapLeft();

  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) 
      && theory->tryInterpretConstant(rhs, r)) {
    return TermEvalResult::left(TermList(theory->representConstant(fun(l,r))));
  } else {
    return TermEvalResult::left(TermList(orig));
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

LitEvalResult PolynomialNormalizer::evaluate(Literal* lit) const {
  Stack<TermList> terms(lit->arity());
  for (int i = 0; i < lit->arity(); i++) {
    terms.push(evaluate(*lit->nthArgument(i)));
  }
  return evaluateStep(Literal::create(lit, terms.begin()));
}

LitEvalResult PolynomialNormalizer::evaluateStep(Literal* lit) const {
  CALL("PolynomialNormalizer::evaluateStep(Literal* term)")
  DEBUG("evaluating: ", lit->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return evaluateLit<Interpretation::INTER>(lit); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return LitEvalResult::left(lit);
#define HANDLE_NUM_CASES(NUM) \
      IGNORE_CASE(NUM ## _IS_INT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_RAT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_REAL) /* TODO */ \
      HANDLE_CASE(NUM ## _GREATER) \
      HANDLE_CASE(NUM ## _GREATER_EQUAL) \
      HANDLE_CASE(NUM ## _LESS) \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  //TODO create function theory->tryInterpret(Predicate|Function)
  auto sym = env.signature->getPredicate(lit->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)

      default:
        DBG("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return LitEvalResult::left(lit);
    }
  } else {
    return LitEvalResult::left( lit );
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main Term
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


TermList PolynomialNormalizer::evaluate(TermList term) const {
  if (term.isTerm()) {
    return evaluate(term.term()); 
  } else {
    ASS_REP(term.isVar(), term);
    /* single variables can't be simplified */
    return term;
  }
}

// TermEvalResult PolynomialNormalizer::evaluateStep(TermList term) const {
//   if (term.isTerm()) {
//     return evaluateStep(term.term()); 
//   } else {
//     ASS_REP(term.isVar(), term);
//     /* single variables can't be simplified */
//     return term;
//   }
// }

TermList PolynomialNormalizer::evaluate(Term* term) const {
  CALL("PolynomialNormalizer::evaluate(Term* term)")
  DEBUG("evaluating ", term->toString())
  static DHMap<Term*, TermEvalResult> memo;

  static Stack<TermList*> recursion(8);

  static Stack<Term*> terms(8);
  static vector<TermEvalResult> args;

  args.clear();
  recursion.reset();
  terms.reset();

  recursion.push(term->args());
  terms.push(term);

  TermList* cur;
  while (!recursion.isEmpty()) {

    cur = recursion.pop();

    if (!cur->isEmpty()) {

      recursion.push(cur->next());

      if(cur->isVar()) {
        // variables are not evaluated
        args.emplace_back(TermEvalResult::left(*cur));

      } else {
        ASS(cur->isTerm());

        Term* t = cur->term();
        TermEvalResult* cached = memo.findPtr(t);
        if (cached != nullptr) {
          args.emplace_back(TermEvalResult(*cached));
        } else {
          terms.push(t);
          recursion.push(t->args());
        }
      }


    } else /* cur->isEmpty() */ { 

      ASS(!terms.isEmpty()) 

      Term* orig=terms.pop();

      auto cached = memo.findPtr(orig);
      TermEvalResult res;
      if (cached) {
        res = TermEvalResult(*cached);
        // args.emplace_back(TermEvalResult(*cached));

      } else {
        TermEvalResult* argLst = 0;
        if (orig->arity() != 0) {
          argLst=&args[args.size() - orig->arity()];
        }

        res = evaluateStep(orig, argLst);
        ALWAYS(memo.emplace(orig, TermEvalResult(res)))
        DEBUG("evaluated: ", orig->toString(), " -> ", res);
      }
      args.resize(args.size() - orig->arity());
      args.emplace_back(std::move(res));
    }

  }
  ASS_REP(recursion.isEmpty(), recursion)
    

  ASS(args.size() == 1);
  TermEvalResult out = TermEvalResult::left( TermList() );
  std::move(std::make_move_iterator(args.begin()),
            std::make_move_iterator(args.end()),
            &out);
  auto out_ = out.collapse<TermList>(
      [](TermList&& l) { return l; },
      [](AnyPoly&& p) -> TermList{ return p.toTerm_(); }
      ); 
  return out_;
}


inline TermList createTerm(unsigned fun, const Signature::Symbol& sym, TermEvalResult* evaluatedArgs) {
  Stack<TermList> args(sym.arity());
  // args.reserve;

  auto& op = *sym.fnType();
  auto arity = op.arity();
  for (int i = 0; i < arity; i++) {
    args.push(evaluatedArgs[0].toLeft(
      [&](const AnyPoly& p) { 
        return p.toTerm_();
      }));
  }
  return TermList(Term::create(fun, arity, args.begin()));
}

TermEvalResult PolynomialNormalizer::evaluateStep(Term* orig, TermEvalResult* args) const {
  CALL("PolynomialNormalizer::evaluateStep(Term* orig, TermEvalResult* args)")

#define HANDLE_CASE(INTER) case Interpretation::INTER: return evaluateFun<Interpretation::INTER>(orig, args); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return TermEvalResult::left(createTerm(functor, *sym, args));


#define HANDLE_CONSTANT_CASE(Num) \
  { \
    Num ## ConstantType c; \
    if (theory->tryInterpretConstant(orig, c)) { \
      return evaluateConst<num_traits<Num ## ConstantType>>(c); \
    } \
  } \

#define HANDLE_NUM_CASES(NUM) \
    HANDLE_CASE(NUM ## _UNARY_MINUS) \
    HANDLE_CASE(NUM ## _PLUS) \
    HANDLE_CASE(NUM ## _MINUS) \
    HANDLE_CASE(NUM ## _MULTIPLY) \
    HANDLE_CASE(NUM ## _QUOTIENT_E) \
    HANDLE_CASE(NUM ## _QUOTIENT_T) \
    HANDLE_CASE(NUM ## _QUOTIENT_F) \
    HANDLE_CASE(NUM ## _REMAINDER_E) \
    HANDLE_CASE(NUM ## _REMAINDER_T) \
    HANDLE_CASE(NUM ## _REMAINDER_F) \
    HANDLE_CASE(NUM ## _FLOOR) \
    HANDLE_CASE(NUM ## _CEILING) \
    HANDLE_CASE(NUM ## _TRUNCATE) \
    HANDLE_CASE(NUM ## _TO_INT) \
    HANDLE_CASE(NUM ## _TO_RAT) \
    HANDLE_CASE(NUM ## _TO_REAL) \

  auto functor = orig->functor();
  auto sym = env.signature->getFunction(functor);

  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch (inter) {

      /* common number functions*/
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer functions */
      HANDLE_CASE(INT_SUCCESSOR)
      HANDLE_CASE(INT_ABS)

      /* rational functions */
      HANDLE_CASE(RAT_QUOTIENT)
      IGNORE_CASE(RAT_ROUND)  //TODO

      /* real functions */
      HANDLE_CASE(REAL_QUOTIENT)
      IGNORE_CASE(REAL_ROUND)  //TODO

      /* ignored */
      IGNORE_CASE(ARRAY_SELECT)
      IGNORE_CASE(ARRAY_BOOL_SELECT)
      IGNORE_CASE(ARRAY_STORE)

      default:
        if (theory->isInterpretedNumber(orig)) {
          HANDLE_CONSTANT_CASE(Integer)
          HANDLE_CONSTANT_CASE(Rational)
          HANDLE_CONSTANT_CASE(Real)
        }
        ASS_REP(false, "unexpected interpreted function: " + orig->toString())
        // return TermList(Term::create(orig, args));
        return TermEvalResult::left(createTerm(functor, *sym, args));

    }

  } else {
      return TermEvalResult::left(createTerm(functor, *sym, args));
  }
}

// TODO
// - include division (?)
// - include binary minus
// - integrate in simplification rule (evaluation simpl)
// - integrate in rebalancing elimination
//     test this case:
//     - eq(mul(2, a), add(x, x)) =====>  eq(a, x)

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

#define INSTANTIATE_STATIC(value) \
  template<> decltype(value) value = decltype(value)();

#define INSTANTIATE_STATICS(Integer) \
  INSTANTIATE_STATIC(Kernel::Monom  <Kernel::num_traits<Kernel::Integer ## ConstantType>>::monoms  ) \
  INSTANTIATE_STATIC(Kernel::Polynom<Kernel::num_traits<Kernel::Integer ## ConstantType>>::polynoms)

INSTANTIATE_STATICS(Integer)
INSTANTIATE_STATICS(Rational)
INSTANTIATE_STATICS(Real)

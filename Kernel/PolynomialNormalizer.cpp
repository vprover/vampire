#include "PolynomialNormalizer.hpp"
#include "Debug/Tracer.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

using namespace Lib;
using namespace Lib::StdWrappers;

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
 
    int cmp_fun = l_fun - r_fun;
    if (cmp_fun != 0) return cmp_fun;
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
  return _expensive_sort_terms(lhs, rhs) > 0;
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


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Data structures
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/**
 * A polynomial of a specific interpreted number sort. The type parameter is expected to be an instance of num_traits<...>, 
 * defined in num_traits.hpp.
 */
template<class number>
struct Polynom {

  struct Monom {

    StdWrappers::map<TermList, int
#if VDEBUG
      , expensive_term_comparison
#endif
       > _factors;
    using monom_pair = typename decltype(_factors)::value_type;

    bool isOne() const {
      return _factors.begin() == _factors.end();
    }

    TermList toTerm() const {
      CALL("Monom::toTerm()")
      auto iter = _factors.begin();
      if (iter == _factors.end()) {
        return number::one();
      } else {

        auto mul_n_times = [](TermList wrap, TermList t, int cnt) {
          TermList out = wrap;
          for (int i = 0; i < cnt; i++) {
            out = number::mul(t, out);
          }
          return out;
        };

        ASS(iter->second != 0);
        auto out = mul_n_times(iter->first, iter->first, iter->second - 1);
        // DBG("out: ", out)
        iter++;
        for(; iter != _factors.end(); iter++)  {
          out = mul_n_times(out, iter->first, iter->second);
        // DBG("out: ", out)
        }
        return out;
      }
    }

    // empty monom == 1
    Monom() : _factors(decltype(_factors)()) {
    }
    Monom(TermList t) : _factors(decltype(_factors)()) {
      _factors.insert(monom_pair(t, 1));
    }

    friend std::ostream& operator<<(std::ostream& out, const Monom& self) {
      if (self._factors.size() == 0) {
        return out << "1";
      } else {
        auto iter  = self._factors.begin();
        out << iter->first << "^" << iter->second;
        iter++;
        for (; iter != self._factors.end(); iter++) {
          out << " * " << iter->first << "^" << iter->second;
        }
        return out;
      }
    }

    Monom clone() const {
      return Monom(*this);
    }

    friend bool operator<(const Monom& l, const Monom& r) {
      return l._factors < r._factors;
    }

    friend bool operator==(const Monom& l, const Monom& r) {
      return l._factors == r._factors;
    }

    Monom& operator=(Monom&&) = default;
    Monom(Monom&&) = default;

    friend Monom operator*(const Monom& lhs, const Monom& rhs) {
      Monom out;
      // TODO memoization
      auto pos = out._factors.begin();
      auto l = lhs._factors.begin();
      auto r = rhs._factors.begin();
      auto insert = [&](TermList term, int value) {
        if (value != 0)
          pos = out._factors.insert(pos, make_pair(term, value));
      };
      while (l != lhs._factors.end() && r != rhs._factors.end() ) {
        // DBG("l: ", l->first)
        // DBG("r: ", r->first)
        if (l->first == r->first) {
          //add up
          insert(l->first, l->second + r->second);
          l++;
          r++;
        } else if (l->first < r->first) {
          // insert l
          insert(l->first, l->second);
          l++;
        } else {
          // insert r
          insert(r->first, r->second);
          r++;
        }
      }
      while (l != lhs._factors.end()) {
        insert(l->first, l->second);
        l++;
      }
      while (r != rhs._factors.end()) {
        insert(r->first, r->second);
        r++;
      }
      ASS(l == lhs._factors.end() && r == rhs._factors.end());
      return out;
    }

    private:
    Monom(const Monom&) = default;
  };


  using Coeff = typename number::ConstantType;
  StdWrappers::map<Monom, Coeff> _coeffs;
  using poly_pair = typename decltype(_coeffs)::value_type;

  void multiply(Coeff c) {
    CALL("Polynom::multiply")
    for (auto& pair : _coeffs) {
      pair.second = c * pair.second;
    }
  }

  friend Polynom operator+(const Polynom& lhs, const Polynom& rhs) {
    CALL("Polynom::operator+")
    // DBG("Polynom::operator+")

    Polynom out;
    // TODO memoization
    // TODO unify with Monom::operator+
    auto pos = out._coeffs.begin();
    auto l = lhs._coeffs.begin();
    auto r = rhs._coeffs.begin();
    auto insert = [&](const Monom& monom, Coeff value) {
      if (value != number::zeroC)
      pos = out._coeffs.insert(pos, make_pair(monom.clone(), value));
    };
    while (l != lhs._coeffs.end() && r != rhs._coeffs.end() ) {
      // DBG("l: ", l->first)
      // DBG("r: ", r->first)
      if (l->first == r->first) {
        //add up
        insert(l->first, l->second + r->second);
        l++;
        r++;
      } else if (l->first < r->first) {
        // insert l
        insert(l->first, l->second);
        l++;
      } else {
        // insert r
        insert(r->first, r->second);
        r++;
      }
    }
    while (l != lhs._coeffs.end()) {
      insert(l->first, l->second);
      l++;
    }
    while (r != rhs._coeffs.end()) {
      insert(r->first, r->second);
      r++;
    }
    ASS(l == lhs._coeffs.end() && r == rhs._coeffs.end());
    return out;
  }

  friend Polynom operator*(const Polynom& lhs, const Polynom& rhs) {
    CALL("Polynom::operator*")
    // DBG("Polynom::operator*")
    //TODO memoization
    Polynom out;
    for (auto& l : lhs._coeffs) {
      for (auto& r : rhs._coeffs) {
        out._coeffs.insert(make_pair(std::move(l.first * r.first), l.second * r.second));
      }
    }
    return out;
  }

  Coeff get(TermList t) {
    CALL("Polynom::get")
    auto iter = _coeffs.find(t);
    if (iter == _coeffs.end()) {
      return Coeff(0);
    } else {
      return iter->second;
    }
  }

  Polynom(Coeff coeff, TermList t) : _coeffs(decltype(_coeffs)())  { 
    // _coeffs.insert(std::move(poly_pair(std::move(Monom(t)), coeff)));
    _coeffs.emplace(std::piecewise_construct,
        std::forward_as_tuple(Monom(t)),
        std::forward_as_tuple(coeff));
    // DBG("Polynom(Coeff, TermList) -> ", *this)
  }

  Polynom(Coeff constant) : _coeffs(decltype(_coeffs)())  { 
    if (constant != number::zeroC)
      _coeffs.insert(make_pair(Monom(), constant));
  }

  Polynom() : _coeffs(decltype(_coeffs)()) {}
  Polynom(Polynom&& other) = default;

  Polynom& operator=(Polynom&& other) {
    CALL("Polynom::operator=(Polynom&&)")
    _coeffs = std::move(other._coeffs);
    return *this;
  }

  static TermList toTerm(const Polynom& self) {
    CALL("Polynom::toTerm() const")
    auto trm = [](const poly_pair& x) -> TermList { 

      if (x.first.isOne()) {  
        /* the pair is a plain number */
        return TermList( theory->representConstant(x.second) );

      } else if (x.second == number::constant(1)) {
        /* the pair is an uninterpreted term */
        return x.first.toTerm();

      } else if (x.second == number::constant(-1)) {
        return TermList(number::minus(x.first.toTerm()));

      } else {
        return TermList(number::mul(TermList( theory->representConstant(x.second) ), x.first.toTerm())); 
      }

    };

    auto iter = self._coeffs.begin(); 
    if (iter == self._coeffs.end()) {
      return TermList(number::zero());
    } else {
      auto out = trm(*iter);
      // DBG("out: ", out)
      iter++;
      for (; iter != self._coeffs.end(); iter++) {
        // auto x = *iter;
        out = number::add(out, trm(*iter));
      // DBG("out: ", out)
      }
      return out;
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const Polynom& self) {
    auto iter = self._coeffs.begin();
    if ( iter == self._coeffs.end() ) {
      out << "0" << endl;
    } else {
      out << iter->first << " * " << iter->second;
      iter++;
      for (; iter != self._coeffs.end(); iter++) {
        out << " + " << iter->first << " * " << iter->second;
      }
    }
    return out;
  }
};

struct AnyPoly {
  
  template<class C>
  using poly = Polynom<num_traits<C>>;
  using self_t = Either< poly<IntegerConstantType> , Either< poly<RationalConstantType> , poly<RealConstantType> >>;
  self_t self; 

    explicit AnyPoly(poly<IntegerConstantType>&& x) : self(self_t::leftMv(std::move(x))) {
      CALL("AnyPoly(Int)")
    }
    explicit AnyPoly(poly<RationalConstantType>&& x ) : self(
        self_t::rightMv(self_t::right_t::leftMv(std::move(x)))
        ) {

      CALL("AnyPoly(Rat)")
    }
    explicit AnyPoly(poly<RealConstantType>&& x ) : self(
        self_t::rightMv(self_t::right_t::rightMv(std::move(x)))
        ) {
      CALL("AnyPoly(Real)")
    }

  template<class Const> const poly<Const>& ref() const;

  template<> const poly<IntegerConstantType>& ref<IntegerConstantType>() const 
  { return self.unwrapLeft();  }

  template<> const poly<RationalConstantType>& ref<RationalConstantType>() const 
  { return self.unwrapRight().unwrapLeft();  }

  template<> const poly<RealConstantType>& ref<RealConstantType>() const 
  { return self.unwrapRight().unwrapRight();  }


  template<class Const> poly<Const>& ref_mut();

  template<> poly<IntegerConstantType>& ref_mut<IntegerConstantType>() 
  { return self.unwrapLeft();  }

  template<> poly<RationalConstantType>& ref_mut<RationalConstantType>() 
  { return self.unwrapRight().unwrapLeft();  }

  template<> poly<RealConstantType>& ref_mut<RealConstantType>() 
  { return self.unwrapRight().unwrapRight();  }

  template<class Const>
  void set(TermList t, Const c) {
    CALL("AnyPoly::set")
    return ref_mut<Const>().set(t,c);
  }

  template<class Const>
  void multiply(Const c) {
    CALL("AnyPoly::multiply")
    return ref_mut<Const>().multiply(c);
  }

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

    if (self.isLeft()) {
      using ty = typename self_t::left_t::Coeff;
      return toTerm<ty>();

    } else if (self.unwrapRight().isLeft()) {
      using ty = typename self_t::right_t::left_t::Coeff;
      return toTerm<ty>();

    } else {
      using ty = typename self_t::right_t::right_t::Coeff;
      return toTerm<ty>();
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& x) {
    auto& self = x.self;
    if (self.isLeft()) {
      out << self.unwrapLeft();
    } else if (self.unwrapRight().isLeft()) {
      out << self.unwrapRight().unwrapLeft();
    } else {
      out << self.unwrapRight().unwrapRight();
    }
    return out;
  }
  AnyPoly& operator=(AnyPoly&&) = default;
  AnyPoly(AnyPoly&&) = default;
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
      [](TermList&& t) { 
        return TermEvalResult::rightMv(AnyPoly(
            Polynom<number>(
                number::constant(-1), t
              )));
      },
      [](AnyPoly&& p) {
        p.multiply(number::constant(-1));
        return TermEvalResult::rightMv(std::move(p));
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
Polynom<number> evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs) {
  using Const = typename number::ConstantType;
  using poly = Polynom<number>;

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

  return l * r;
}


#define IMPL_MULTIPLY(Const) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<num_traits<Const>::mulI>(Term* orig, TermEvalResult* evaluatedArgs) const  \
  { \
    CALL("PolynomialNormalizer::evaluateFun<num_traits<" #Const ">::mulI>(Term* trm, TermEvalResult* evaluatedArgs)") \
    return TermEvalResult::rightMv(AnyPoly(evaluateMul<num_traits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])))); \
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
  using Const = typename number::ConstantType;
  using poly = Polynom<number>;

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

  return l + r;
}


#define IMPL_ADD(Const) \
  template<> TermEvalResult PolynomialNormalizer::evaluateFun<num_traits<Const>::addI>(Term* orig, TermEvalResult* evaluatedArgs) const  \
  { \
    CALL("PolynomialNormalizer::evaluateFun<num_traits<" #Const ">::addI>(Term* trm, TermEvalResult* evaluatedArgs)") \
    return TermEvalResult::rightMv(AnyPoly(evaluateAdd<num_traits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])))); \
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
  Stack<TermList> terms;
  //TODO reserve arity
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

  static Stack<TermList*> position(8);

  static Stack<Term*> terms(8);
  static vector<TermEvalResult> args;

  args.clear();
  position.reset();
  terms.reset();

  position.push(term->args());
  terms.push(term);

  TermList* cur;
  while (!position.isEmpty()) {

    cur = position.pop();

    if (!cur->isEmpty()) {

      position.push(cur->next());

      if(cur->isVar()) {
        // variables are not evaluated
        args.emplace_back(TermEvalResult::left(*cur));

      } else {
        ASS(cur->isTerm());
        Term* t = cur->term();
        terms.push(t);
        position.push(t->args());
      }



    } else /* cur->isEmpty() */ { 

      ASS(!terms.isEmpty()) 

      Term* orig=terms.pop();

      TermEvalResult* argLst = 0;
      if (orig->arity() != 0) {
        //here we assume, that stack is an array with
        //second topmost element as &top()-1, third at
        //&top()-2, etc...
        argLst=&args[args.size() - 1] - (orig->arity()-1);
      }

      // auto t = Term::create(orig,argLst);
      auto res = evaluateStep(orig, argLst);
      args.resize(args.size() - orig->arity());
      DEBUG("evaluated: ", orig->toString(), " -> ", res);
      args.emplace_back(std::move(res));
    }

  }
  ASS_REP(position.isEmpty(), position)
    

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
  Stack<TermList> args;
  //TODO reserve

  auto& op = *sym.fnType();
  auto arity = op.arity();
  for (int i = 0; i < arity; i++) {
    args.push(evaluatedArgs[0].toLeft(
      [&](const AnyPoly& p) { 
      //TODO dispatch on sort of symbol
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


//TODO
// - include division (?)
// - include binary minus

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

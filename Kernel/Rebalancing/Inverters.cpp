#include "Inverters.hpp"
#include "Debug/Tracer.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {
#define DEBUG(...) //DBG(__VA_ARGS__)

#define CASE_INVERT(sort, fun, expr)                                           \
  case NumTraits<sort>::fun##I: {                                             \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-local-typedef\"") \
    using number = NumTraits<sort>;                                           \
    _Pragma("GCC diagnostic pop") \
    expr;                                                               \
  }

#define CASE_INVERT_INT(fun, expr) CASE_INVERT(IntegerConstantType, fun, expr)

#define CASE_INVERT_FRAC(fun, expr)                                            \
  CASE_INVERT(RealConstantType, fun, expr) \
  CASE_INVERT(RationalConstantType, fun, expr)

bool canInvertMulInt(const InversionContext &ctxt);
TermList doInvertMulInt(const InversionContext &ctxt);
template <class number> bool nonZero(const TermList &t);

#define CASE_PREDICATE \
  case Theory::Interpretation::EQUAL: \
  \
  case Theory::Interpretation::INT_IS_INT: \
  case Theory::Interpretation::INT_IS_RAT: \
  case Theory::Interpretation::INT_IS_REAL: \
  case Theory::Interpretation::INT_GREATER: \
  case Theory::Interpretation::INT_GREATER_EQUAL: \
  case Theory::Interpretation::INT_LESS: \
  case Theory::Interpretation::INT_LESS_EQUAL: \
  case Theory::Interpretation::INT_DIVIDES: \
  \
  case Theory::Interpretation::RAT_IS_INT: \
  case Theory::Interpretation::RAT_IS_RAT: \
  case Theory::Interpretation::RAT_IS_REAL: \
  case Theory::Interpretation::RAT_GREATER: \
  case Theory::Interpretation::RAT_GREATER_EQUAL: \
  case Theory::Interpretation::RAT_LESS: \
  case Theory::Interpretation::RAT_LESS_EQUAL: \
  \
  case Theory::Interpretation::REAL_IS_INT: \
  case Theory::Interpretation::REAL_IS_RAT: \
  case Theory::Interpretation::REAL_IS_REAL: \
  case Theory::Interpretation::REAL_GREATER: \
  case Theory::Interpretation::REAL_GREATER_EQUAL: \
  case Theory::Interpretation::REAL_LESS: \
  case Theory::Interpretation::REAL_LESS_EQUAL \



bool NumberTheoryInverter::canInvertTop(const InversionContext &ctxt) {
  CALL("NumberTheoryInverter::canInvertTop")
  auto &t = ctxt.topTerm();
  auto fun = t.functor();
  auto sym = env.signature->getFunction(fun);

  DEBUG("canInvert ", ctxt.topTerm().toString(), "@", ctxt.topIdx())
  if (theory->isInterpretedFunction(fun)) {
    auto inter = theory->interpretFunction(fun);
    switch (inter) {
      CASE_INVERT_FRAC(add  , return true)
      CASE_INVERT_INT (add  , return true)
      CASE_INVERT_FRAC(minus, return true)
      CASE_INVERT_INT (minus, return true)
      CASE_INVERT_FRAC(mul  , return nonZero<number>(t[1 - ctxt.topIdx()]))
      CASE_INVERT_INT (mul  , return canInvertMulInt(ctxt))
    case Theory::Interpretation::ARRAY_STORE:
      /* store(t, i, x) = s ==> x = select(s, i) */
      return ctxt.topIdx() == 2;
    default:;
    // CASE_PREDICATE:
    //   {ASSERTION_VIOLATION}
    }
    // DBG("WARNING: unknown interpreted function: ", t.toString())
    return false;
  } else if (sym->termAlgebraCons()) { 
    return true;
  } else { /* cannot invert uninterpreted functions */
    DEBUG("no")
    return false;
  }
}



#define CASE_DO_INVERT(sort, fun, expr)                                        \
  case NumTraits<sort>::fun##I: {                                             \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-local-typedef\"") \
    using number = NumTraits<sort>;                                           \
    return expr;                                                               \
    _Pragma("GCC diagnostic pop") \
  }

#define CASE_DO_INVERT_FRAC(fun, expr)                                         \
  CASE_DO_INVERT(RealConstantType, fun, expr)                                  \
  CASE_DO_INVERT(RationalConstantType, fun, expr)

#define CASE_DO_INVERT_ALL(fun, expr)                                          \
  CASE_DO_INVERT_INT(fun, expr)                                                \
  CASE_DO_INVERT_FRAC(fun, expr)

#define CASE_DO_INVERT_INT(fun, expr)                                          \
  CASE_DO_INVERT(IntegerConstantType, fun, expr)

TermList NumberTheoryInverter::invertTop(const InversionContext &ctxt) {
  CALL("NumberTheoryInverter::invertTop")
  ASS(canInvertTop(ctxt))
  // DBG("inverting: ", ctxt.topTerm().toString())
  auto &t = ctxt.topTerm();
  auto index = ctxt.topIdx();
  auto toWrap = ctxt.toWrap();
  auto fun = t.functor();
  DEBUG("inverting ", ctxt.topTerm().toString())
  if(theory->isInterpretedFunction(fun)) {
    switch (theory->interpretFunction(fun)) {

      CASE_DO_INVERT_ALL(add, number::add(toWrap, number::minus(t[1 - index])))
      CASE_DO_INVERT_ALL(minus, number::minus(toWrap))

      CASE_DO_INVERT_FRAC(
          mul, number::mul(toWrap, number::div(number::one(), t[1 - index])))
      CASE_DO_INVERT_INT(mul, doInvertMulInt(ctxt))

      case Theory::Interpretation::ARRAY_STORE: 
      {
        ASS(ctxt.topIdx() == 2)
        /*              store(t, i, x) = s ==> x = select(s, i) */
        /* auto toWrap:                  ^                      */
        /* auto& t:     ^^^^^^^^^^^^^^                          */
        auto& store = *env.signature->getFunction(t.functor())->fnType();
        auto select = env.signature->getInterpretingSymbol(
            Theory::Interpretation::ARRAY_SELECT, 
            OperatorType::getFunctionType({ store.arg(0), store.arg(1) }, store.arg(2)));
        return TermList(Term::create2(select, toWrap, *t.nthArgument(1)));
      }
    default:
      ASSERTION_VIOLATION;
    }
  } else {
    // must be a term algebra sort
    auto sym = env.signature->getFunction(fun);
    ASS_REP(sym->termAlgebraCons(), sym);
    auto ctor = env.signature->getTermAlgebraConstructor(fun);
    auto dtor = ctor->destructorFunctor(index);
    return TermList(Term::create1(dtor, toWrap));
  }
};

bool tryInvertMulInt(const InversionContext &ctxt, TermList &out) {
  CALL("tryInvertMulInt(..)")
  using number = NumTraits<IntegerConstantType>;

  auto a_ = ctxt.topTerm()[1 - ctxt.topIdx()];
  IntegerConstantType a;
  if ( theory->tryInterpretConstant(a_, a)) {
    if (a == IntegerConstantType(1)) {
      out = ctxt.toWrap();
      return true;

    } else if (a == IntegerConstantType(-1)) {
      out = number::mul(a_, ctxt.toWrap());
      return true;

    } else {
      return false;
    }
  } else {
    return false;
  }
}

TermList doInvertMulInt(const InversionContext &ctxt) {
  CALL("doInvertMulInt(...)")
  TermList out;
  ALWAYS(tryInvertMulInt(ctxt, out)) 
  return out;
}

bool canInvertMulInt(const InversionContext &ctxt) {
  CALL("canInvertMulInt(const InversionContext&)")
  TermList _inv;
  return tryInvertMulInt(ctxt, _inv);
}

template <class number> bool nonZero(const TermList &t) {
  typename number::ConstantType c;
  return theory->tryInterpretConstant(t, c) && number::zeroC != c;
}


} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel

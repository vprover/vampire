
template<class CommutativeMonoid>
PolyNf evaluateCommutativeMonoid(Term* orig, PolyNf* evaluatedArgs) ;

template<class ConstantType, class EvalIneq> 
LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) ;

template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun);

template<class ConstantType, class EvalGround>
PolyNf tryEvalConstant1(Term* orig, PolyNf* evaluatedArgs, EvalGround fun);

template<class Number> 
PolyNf evaluateMul(PolyNf&& lhs, PolyNf&& rhs);

template<class ConstantType, class EvalGround>
PolyNf tryEvalConstant2(Term* orig, PolyNf* evaluatedArgs, EvalGround fun);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//TODO unify tryEvalConstant1 and tryEvalConstant2 

template<class ConstantType, class EvalGround>
PolyNf tryEvalConstant1(Term* orig, PolyNf* evaluatedArgs, EvalGround fun) {
  auto func = FuncId(orig->functor());
  ASS_EQ(func.arity(), 1)

  using Number = NumTraits<ConstantType>;
  using NumberOut = NumTraits<typename result_of<EvalGround(ConstantType)>::type>;

  auto& x = evaluatedArgs[0];
  if (x.isPoly()) {
    auto poly = x.template as<AnyPoly>().template as<Polynom<Number>>();
    if (poly.isCoeff()) {
      return AnyPoly(Polynom<NumberOut>(fun(poly.unwrapCoeff())));
    }
  }

  return unique(FuncTerm(func, Stack<PolyNf>{  evaluatedArgs[0] }));
}


template<class ConstantType, class EvalGround>
PolyNf tryEvalConstant2(Term* orig, PolyNf* evaluatedArgs, EvalGround fun) {
  auto func = FuncId(orig->functor());
  ASS_EQ(func.arity(), 2)

  using Number = NumTraits<ConstantType>;
  using NumberOut = NumTraits<typename result_of<EvalGround(ConstantType, ConstantType)>::type>;

  if (evaluatedArgs[0].isPoly() && evaluatedArgs[1].isPoly()) {
    auto lhs = evaluatedArgs[0].template as<AnyPoly>().template as<Polynom<Number>>();
    auto rhs = evaluatedArgs[1].template as<AnyPoly>().template as<Polynom<Number>>();
    if (lhs.isCoeff() && rhs.isCoeff()) {
      return AnyPoly(Polynom<NumberOut>(fun(lhs.unwrapCoeff(), rhs.unwrapCoeff())));
    }
  }

  return unique(FuncTerm(func, Stack<PolyNf>{  evaluatedArgs[0], evaluatedArgs[1] }));
}



#define IMPL_EVALUATE_FUN(interpretation, ...)                                             \
  template<>                                                                               \
  struct FunctionEvaluator<interpretation> {                                               \
    template<class Config>                                                                 \
    static PolyNf evaluate(Term* orig, PolyNf* evaluatedArgs)              \
    {                                                                                      \
      CALL("FunctionEvaluator<" #interpretation ">::evaluate(Term*,PolyNf*)");     \
      __VA_ARGS__                                                                          \
    }                                                                                      \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// UNARY_MINUS 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number, class Config>
PolyNf evaluateUnaryMinus(PolyNf& inner) {
  auto out = inner.match<PolyNf>(
      [](UniqueShared<FuncTerm>& t) { return AnyPoly(Polynom<Number>(Number::constant(-1), t)); }, 
      [](              Variable& t) { return AnyPoly(Polynom<Number>(Number::constant(-1), t)); }, 
      [](AnyPoly& p) {
        auto minusOne = Polynom<Number>(Number::constant(-1));
        auto out = Polynom<Number>::template polyMul<Config>(
              minusOne
            , p.as<Polynom<Number>>());

        return AnyPoly(std::move(out));
      });
  return out;
}


#define IMPL_UNARY_MINUS(Const)                                                            \
  IMPL_EVALUATE_FUN(NumTraits<Const>::minusI, {                                            \
    return evaluateUnaryMinus<NumTraits<Const>, Config>(evaluatedArgs[0]);                 \
  })

  IMPL_UNARY_MINUS(RealConstantType    )
  IMPL_UNARY_MINUS(RationalConstantType)
  IMPL_UNARY_MINUS(IntegerConstantType )

#undef IMPL_UNARY_MINUS


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MULTIPLY
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
Polynom<number> toPoly(PolyNf x) {
  using Poly = Polynom<number>;
  return x.match<Poly>(
      [](UniqueShared<FuncTerm> const& t) { return Poly(PolyNf(t)); }, 
      [](Variable               const& t) { return Poly(PolyNf(t)); }, 
      [](AnyPoly                const& p) { return p.as<Poly>();    }
    );
};

template<class Number, class Config> PolyNf evaluateMul(PolyNf&& lhs, PolyNf&& rhs) 
{
  auto l = toPoly<Number>(lhs);
  auto r = toPoly<Number>(rhs);
  return AnyPoly(Polynom<Number>::template polyMul<Config>(l, r));
}


#define IMPL_MULTIPLY(Const)                                                               \
  IMPL_EVALUATE_FUN(NumTraits<Const>::mulI, {                                              \
    return evaluateMul<NumTraits<Const>, Config>(std::move(evaluatedArgs[0])               \
        , std::move(evaluatedArgs[1]));                                                    \
  })                                                                                       \

  IMPL_MULTIPLY(RealConstantType    )
  IMPL_MULTIPLY(RationalConstantType)
  IMPL_MULTIPLY(IntegerConstantType )

#undef IMPL_MULTIPLY


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ADD 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number>
Polynom<Number> evaluateAdd(PolyNf&& lhs, PolyNf&& rhs) {
  CALL("Polynom<Number> evaluateAdd(PolyNf&& lhs, PolyNf&& rhs)")
  using Poly = Polynom<Number>;

  return Poly::polyAdd(
      toPoly<Number>(lhs), 
      toPoly<Number>(rhs));
}


#define IMPL_ADD(Const)                                                                    \
  IMPL_EVALUATE_FUN(NumTraits<Const>::addI, {                                              \
    return AnyPoly( \
        evaluateAdd<NumTraits<Const>>( \
          std::move(evaluatedArgs[0]),  \
          std::move(evaluatedArgs[1]))); \
  })                                                                                       \

  IMPL_ADD(RealConstantType    )
  IMPL_ADD(RationalConstantType)
  IMPL_ADD(IntegerConstantType )

#undef IMPL_ADD

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Functions that are only handled for constants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define IMPL_EVAL_UNARY(Const, INTER, clsr)                                                \
  IMPL_EVALUATE_FUN(Interpretation::INTER, {                                               \
    return tryEvalConstant1<Const>(orig, evaluatedArgs, clsr);                             \
  } )

#define IMPL_EVAL_BINARY(Const, INTER, expr)                                               \
  IMPL_EVALUATE_FUN(Interpretation::INTER, {                                               \
    return tryEvalConstant2<Const>(orig, evaluatedArgs, [] (Const l, Const r) { return expr; }); \
  } )


/////////////////// Integer only functions

IMPL_EVAL_UNARY(IntegerConstantType, INT_ABS      , [] (IntegerConstantType x) -> IntegerConstantType { return x >= 0 ? x : -x; })
IMPL_EVAL_UNARY(IntegerConstantType, INT_SUCCESSOR, [] (IntegerConstantType x) -> IntegerConstantType { return x >= 0 ? x : -x; })

/////////////////// INT_QUOTIENT_E and friends

#define IMPL_QUOTIENT_REMAINDER(Const, NUM, SUFFIX)                                        \
  IMPL_EVAL_BINARY(Const, NUM ##  _QUOTIENT_ ## SUFFIX,  l.quotient ## SUFFIX(r))          \
  IMPL_EVAL_BINARY(Const, NUM ## _REMAINDER_ ## SUFFIX,  l - (l.quotient ## SUFFIX (r)*r)) \

#define IMPL_QUOTIENT_REMAINDERS(Const, NUM)                                               \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, E)                                                   \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, T)                                                   \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, F)                                                   \
  IMPL_EVAL_BINARY(Const, NUM ## _MINUS, l - r)                                            \

  IMPL_QUOTIENT_REMAINDERS(RealConstantType    , REAL)
  IMPL_QUOTIENT_REMAINDERS(RationalConstantType, RAT )
  IMPL_QUOTIENT_REMAINDERS(IntegerConstantType , INT )

#undef IMPL_QUOTIENT_REMAINDER
#undef IMPL_QUOTIENT_REMAINDERS

/////////////////// INT_FLOOR and friends

// have no effect for ints
IMPL_EVAL_UNARY(IntegerConstantType, INT_FLOOR   , [] (IntegerConstantType x) -> IntegerConstantType { return x; })
IMPL_EVAL_UNARY(IntegerConstantType, INT_CEILING , [] (IntegerConstantType x) -> IntegerConstantType { return x; })
IMPL_EVAL_UNARY(IntegerConstantType, INT_TRUNCATE, [] (IntegerConstantType x) -> IntegerConstantType { return x; })
IMPL_EVAL_UNARY(IntegerConstantType, INT_ROUND   , [] (IntegerConstantType x) -> IntegerConstantType { return x; })

// same impl for fractionals
#define IMPL_FRAC_FLOOR_FRIENDS(Const, NUM)                                                \
  IMPL_EVAL_UNARY(Const, NUM ## _FLOOR   , [](Const x) -> Const { return x.floor();   })   \
  IMPL_EVAL_UNARY(Const, NUM ## _CEILING , [](Const x) -> Const { return x.ceiling(); })   \
  IMPL_EVAL_UNARY(Const, NUM ## _TRUNCATE, [](Const x) -> Const { return x.truncate();})   \

  IMPL_FRAC_FLOOR_FRIENDS(RealConstantType    , REAL)
  IMPL_FRAC_FLOOR_FRIENDS(RationalConstantType, RAT)

#undef IMPL_EVAL_FRAC_FLOOR_FRIENDS
 
/////////////////// RAT_TO_INT and friends

#define IMPL_NUM_CVT(Const, NUM)                                                           \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_INT, [](Const x) -> IntegerConstantType  { return IntegerConstantType::floor(x); }) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_RAT, [](Const x) -> RationalConstantType { return RationalConstantType(x);       }) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_REAL,[](Const x) -> RealConstantType     { return RealConstantType(x);           }) \

  IMPL_NUM_CVT(RealConstantType    , REAL)
  IMPL_NUM_CVT(RationalConstantType, RAT )
  IMPL_NUM_CVT(IntegerConstantType , INT )

#undef IMPL_NUM_CVT

/////////////////// QUOTIENT 
//
#define IMPL_QUOTIENT(Const, NUM)                                                          \
    IMPL_EVAL_BINARY(Const, NUM ## _QUOTIENT, l / r)                                       \

  IMPL_QUOTIENT(RealConstantType    , REAL)
  IMPL_QUOTIENT(RationalConstantType, RAT )

#undef IMPL_QUOTIENT
 


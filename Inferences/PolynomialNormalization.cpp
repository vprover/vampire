#include "Inferences/PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
using namespace Lib;

namespace Inferences {

Clause* MaybeImmediateSimplification::simplify(Clause* cl) {
  CALL("MaybeImmediateSimplification::simplify(Clause*)")
  if (cl->isTheoryAxiom()) {
    DEBUG("skipping theory axiom")
    return cl;
  }
  auto gen = this->simplify(cl, false);
  return get<0>(gen);
}


SimplifyingGeneratingInference::ClauseGenerationResult MaybeImmediateSimplification::generateClauses(Clause* cl) {
  CALL("MaybeImmediateSimplification::generateClauses(Clause*)")
  auto gen = this->simplify(cl, true);
  auto simpl = get<0>(gen);
  auto redundant = get<1>(gen);

  if (simpl == cl) {
    return ClauseGenerationResult {
      .clauses = ClauseIterator::getEmpty(),
      .premiseRedundant = false,
    };

  } else {
    return ClauseGenerationResult {
      .clauses = simpl == nullptr 
        ? ClauseIterator::getEmpty()
        : pvi(getSingletonIterator(simpl)),
      .premiseRedundant = redundant && !cl->isTheoryAxiom(),
    };
  }
}

pair<Clause*, bool> MaybeImmediateLiteralSimplification::simplify(Clause* cl_, bool doOrderingCheck) {
  DEBUG("in:  ", *cl_)
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;
  bool allLessEq = true;
  bool oneLess = false;

  for (int i = 0; i < cl.size(); i++) {

    auto orig = cl[i];
    auto result = simplifyLiteral(orig);

    if (result.isNone() || (result.unwrap().isLiteral() && result.unwrap().unwrapLiteral() == orig) ) {
      out.push(orig);
    } else {
      auto simpl = result.unwrap();
      env.statistics->evaluationCnt++;

      if (simpl.isConstant()) {

        bool trivialValue = simpl.unwrapConstant();
        if (trivialValue) {
          /* clause is a tautology and can be deleted */
          return make_pair(nullptr, true);
        } else {
          /* do not add the literal to the output stack */
          changed = true;
        }

      } else {

        Literal* simplLit = simpl.unwrapLiteral();
        ASS_NEQ(simplLit, orig)
        changed = true;
        out.push(simplLit);

        if (doOrderingCheck) {
          ASS(_ordering)
          auto cmp = _ordering->compare(simplLit, orig);
          switch(cmp) {
            case Ordering::Result::LESS:
              oneLess = true;
              break;
            case Ordering::Result::LESS_EQ:
            case Ordering::Result::EQUAL:
              ASSERTION_VIOLATION
              break;
            case Ordering::Result::INCOMPARABLE:
            case Ordering::Result::GREATER:
            case Ordering::Result::GREATER_EQ:
              if (cmp == Ordering::Result::INCOMPARABLE) {
                env.statistics->evaluationIncomp++;
              } else {
                env.statistics->evaluationGreater++;
              }
              DEBUG("ordering violated: ", cmp)
              DEBUG("orig: ", *orig)
              DEBUG("simp: ", *simplLit)
              allLessEq = false;
              break;
          }
        }
      }
    }
  }


  if (!changed) {
    return make_pair(cl_, false);
  } else {
    auto result = Clause::fromStack(out, SimplifyingInference1(_rule, cl_));
    DEBUG("out: ", *result)
    return make_pair(result, allLessEq && oneLess);
  }
}

Optional<LitEvalResult> PolynomialNormalization::simplifyLiteral(Literal* lit) 
{ return _normalizer.evaluate(lit);
}

MaybeImmediateLiteralSimplification::MaybeImmediateLiteralSimplification(InferenceRule rule, Ordering& ordering): _ordering(&ordering), _rule(rule) {}

PolynomialNormalization::PolynomialNormalization(Ordering& ordering) : MaybeImmediateLiteralSimplification(InferenceRule::EVALUATION, ordering) {}

PolynomialNormalization::~PolynomialNormalization() {}

PushUnaryMinus::~PushUnaryMinus() {}


enum class UMinus {
  Int,
  Rat,
  Real,
  None,
};

ostream& operator<<(ostream& out, UMinus const& self) {
  switch(self) {
    case UMinus::Int: return out << "UMinus::Int";
    case UMinus::Rat: return out << "UMinus::Rat";
    case UMinus::Real: return out << "UMinus::Real";
    case UMinus::None: return out << "UMinus::None";
  }
}


TermList pushUMinus(UMinus outerMinus, TermList t) 
{
  CALL("pushUMinus(UMinus outerMinus, TermList t) ")
  auto wrapMinus = [&](TermList t) 
  {
    switch (outerMinus) {
      case UMinus::Int : return IntTraits::minus(t);
      case UMinus::Rat : return RatTraits::minus(t);
      case UMinus::Real: return RealTraits::minus(t);
      case UMinus::None: return t;
    }
  };

  if (t.isVar()) {
    return wrapMinus(t);
  } else {
    auto term = t.term();
    auto fun = term->functor();
    if (theory->isInterpretedFunction(fun)) {
      switch (theory->interpretFunction(fun)) {
#define CASE(Num)                                                                                             \
        case Num##Traits::minusI:                                                                             \
        {                                                                                                     \
          if(outerMinus == UMinus::None) {                                                                    \
            return pushUMinus(UMinus::Num, *term->nthArgument(0));                                            \
          } else {                                                                                            \
            ASS_EQ(outerMinus, UMinus::Num)                                                                   \
            return *term->nthArgument(0);                                                                     \
          }                                                                                                   \
        }                                                                                                     \
        case Num##Traits::addI:                                                                               \
        if (outerMinus != UMinus::None) {                                                                     \
          ASS_EQ(outerMinus, UMinus::Num);                                                                    \
          return Num##Traits::add(                                                                            \
              pushUMinus(UMinus::Num, *term->nthArgument(0)),                                                 \
              pushUMinus(UMinus::Num, *term->nthArgument(1)));                                                \
        } else { break; }
        CASE(Int)
        CASE(Rat)
        CASE(Real)
        default: {}
      }
    }
    Stack<TermList> args(term->arity());
    for (int i =0; i < term->arity(); i++) {
      args.push(pushUMinus(UMinus::None, *term->nthArgument(i)));
    }
    return wrapMinus(TermList(Term::create(term, args.begin())));
  }
}

Clause* PushUnaryMinus::simplify(Clause* cl_) 
{
  CALL("PushUnaryMinus::simplify(Clause*)")
  DEBUG("in:  ", *cl_)
  if (cl_->isTheoryAxiom()) 
    return cl_;
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (int i = 0; i < cl.size(); i++) {
    auto litIn = cl[i];
    Stack<TermList> litStack;
    for (int j = 0; j < litIn->arity(); j++) {
      auto tIn = *litIn->nthArgument(j);
      auto tOut = pushUMinus(UMinus::None, tIn);
      changed = changed || tIn != tOut;
      litStack.push(tOut);
    }
    auto litOut = Literal::create(litIn, litStack.begin());
    out.push(litOut);
  }

  if (!changed) {
    return cl_;
  } else {
    auto result = Clause::fromStack(out, SimplifyingInference1(InferenceRule::EVALUATION, cl_));
    DEBUG("out: ", *result)
    return result;
  }
}

Cancellation::~Cancellation() {}

template<class NumTraits>
Optional<Literal*> doCancellation(Literal* lit) {
  auto normL = PolyNf::normalize(TypedTermList((*lit)[0], SortHelper::getArgSort(lit, 0)));
  auto normR = PolyNf::normalize(TypedTermList((*lit)[1], SortHelper::getArgSort(lit, 1)));

  auto oldL = intoPoly<NumTraits>(normL);
  auto oldR = intoPoly<NumTraits>(normR);
  // auto oldL = normL.asPoly().template unwrap<UniqueShared<Polynom<NumTraits>>>();
  // auto oldR = normR.asPoly().template unwrap<UniqueShared<Polynom<NumTraits>>>();
  auto res = Polynom<NumTraits>::cancelAdd(*oldL, *oldR);
  auto newL = unique(std::move(res.lhs));
  auto newR = unique(std::move(res.rhs));
  if (newL != oldL || newR != oldR)  {
    TermList args[] = {
      res.lhs.toTerm(),
      res.rhs.toTerm(),
    };
    return Optional<Literal*>(Literal::create(lit, args));
  } else  {
    return Optional<Literal*>();
  }
}

Optional<Literal*> tryCancel(Interpretation inter, Literal* lit) {
  switch(inter) {
    case Interpretation::EQUAL:
      switch (SortHelper::getEqualityArgumentSort(lit)) {
        case  IntTraits::sort: return doCancellation< IntTraits>(lit);
        case  RatTraits::sort: return doCancellation< RatTraits>(lit);
        case RealTraits::sort: return doCancellation<RealTraits>(lit);
        default:;
      }
      break;
#define INEQ_CASES(NumTraits)                                                                                 \
    case NumTraits::leqI:                                                                                     \
    case NumTraits::geqI:                                                                                     \
    case NumTraits::greaterI:                                                                                 \
    case NumTraits::lessI:                                                                                    \
      return doCancellation<NumTraits>(lit); 

    INEQ_CASES( IntTraits)
    INEQ_CASES( RatTraits)
    INEQ_CASES(RealTraits)
#undef INEQ_CASES
    default:;
  }
  return Optional<Literal*>();
}

// TODO make cancellation its own inference rule
Cancellation::Cancellation(Ordering& ordering) : MaybeImmediateLiteralSimplification(InferenceRule::EVALUATION, ordering) 
{}

Optional<LitEvalResult> Cancellation::simplifyLiteral(Literal* litIn) 
{
  CALL("Cancellation::simplifyLiteral(Literal*)")

  auto pred = litIn->functor();
  if (!theory->isInterpretedPredicate(pred)) {
    return Optional<LitEvalResult>();
  } else {
    return tryCancel(theory->interpretPredicate(pred), litIn)
      .map([](Literal* lit) 
          { return LitEvalResult::literal(lit); });
  }
}

} // Inferences

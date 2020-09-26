#include "Inferences/PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {



Clause* PolynomialNormalization::simplify(Clause* cl_) {
  CALL("PolynomialNormalization::simplify(Clause*)")
  DEBUG("in:  ", *cl_)
  if (cl_->isTheoryAxiom()) 
    return cl_;
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (int i = 0; i < cl.size(); i++) {

    auto orig = cl[i];
    auto result = _normalizer.evaluate(orig);

    if (result.isNone()) {
        out.push(orig);
    } else {
      auto simpl = result.unwrap();
      env.statistics->polyNormalizerSimplCnt++;

      if (simpl.isConstant()) {

        bool trivialValue = simpl.unwrapConstant();
        if (trivialValue) {
          /* clause is a tautology and can be deleted */
          return NULL;
        } else {
          /* do not add the literal to the output stack */
          changed = true;
        }

        if (_ordering) {
          env.statistics->polyNormalizerSimplCorrect++;
        }
      } else {

        Literal* simplLit = simpl.unwrapLiteral();
        ASS_NEQ(simplLit, orig)
        changed = true;
        out.push(simplLit);

        if (_ordering) {
          if (_ordering->compare(simplLit, orig) == Ordering::Result::LESS) {
            env.statistics->polyNormalizerSimplCorrect++;
          } else {
            // DBGE(*orig    )
            // DBG(_ordering->compare(simplLit, orig))
            // DBGE(*simplLit)
            // ASSERTION_VIOLATION
          }
        }
      }
    }
  }


  if (!changed) {
    return cl_;
  } else {
    auto result = Clause::fromStack(out, SimplifyingInference1(InferenceRule::EVALUATION, cl_));
    DEBUG("out: ", *result)
    return result;
  }
}

PolynomialNormalization::PolynomialNormalization() : _ordering(nullptr) 
{  env.statistics->polyNormalizerSimplCorrect = -1; }

PolynomialNormalization::PolynomialNormalization(Ordering& ordering) : _ordering(&ordering) {}

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


} // Inferences

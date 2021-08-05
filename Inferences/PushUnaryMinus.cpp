/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/PushUnaryMinus.hpp"
#include "Kernel/Clause.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
namespace Inferences {

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
    default:
      return out << "UNKNOWN";
  }
  ASSERTION_VIOLATION
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
      default:
        ASSERTION_VIOLATION;
    }
    ASSERTION_VIOLATION
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
    for (unsigned i =0; i < term->arity(); i++) {
      args.push(pushUMinus(UMinus::None, *term->nthArgument(i)));
    }
    return wrapMinus(TermList(Term::create(term, args.begin())));
  }
}
PushUnaryMinus::~PushUnaryMinus() {}

Clause* PushUnaryMinus::simplify(Clause* cl_) 
{
  CALL("PushUnaryMinus::simplify(Clause*)")
  DEBUG("in:  ", *cl_)
  if (cl_->isTheoryAxiom()) 
    return cl_;

  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (unsigned i = 0; i < cl.size(); i++) {
    auto litIn = cl[i];
    Stack<TermList> litStack;
    for (unsigned j = 0; j < litIn->arity(); j++) {
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

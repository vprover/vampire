/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "PolynomialMultiplication.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Lib/Stack.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {

SimplifyingGeneratingLiteralSimplification::Result PolynomialMultiplication::simplifyLiteral(Literal* l)
{
  CALL("PolynomialMultiplication::simplifyLiteral(Literal* l)");
  
  Stack<TermList> simplArgs(l->arity());
  for (unsigned i = 0; i < l->arity(); i++) {
    auto term = normalizeTerm(TypedTermList(*l->nthArgument(i), SortHelper::getArgSort(l, i)));
    auto simpl = evaluateBottomUp(term, Evaluator{ *this });
    simplArgs.push(simpl.denormalize());
  }
  return Result::literal(Literal::create(l, simplArgs.begin()));
}

Kernel::PolyNf PolynomialMultiplication::evaluateStep(Kernel::PolyNf origTerm, Kernel::PolyNf* evaluatedArgs)
{
  CALL("PolynomialMultiplication::evaluateStep(Kernel::PolyNf, Kernel::PolyNf*)")
  if(origTerm.is<Variable>()) {
    return origTerm;
  } else if(origTerm.is<Perfect<FuncTerm>>()) {
    auto f = origTerm.unwrap<Perfect<FuncTerm>>();
    return perfect(FuncTerm(f->function(), evaluatedArgs));
  } else if(origTerm.is<AnyPoly>()) {
    auto poly = origTerm.unwrap<AnyPoly>();

    if(poly.isType<IntTraits>()) return resolvePolySummands<IntTraits>(poly, evaluatedArgs);
    else if(poly.isType<RatTraits>()) return resolvePolySummands<RatTraits>(poly, evaluatedArgs);
    else if(poly.isType<RealTraits>()) return resolvePolySummands<RealTraits>(poly, evaluatedArgs);
    else ASSERTION_VIOLATION
  } else {
    ASSERTION_VIOLATION
  }
}

template <class NumTraits>
Kernel::AnyPoly PolynomialMultiplication::resolvePolySummands(Kernel::AnyPoly& poly, Kernel::PolyNf* evaluatedArgs)
{
  CALL("PolynomialMultiplication::resolvePolySummands(Kernel::AnyPoly&, Kernel::PolyNf*)")
  using Polynom = Polynom<NumTraits>;

  Stack<PolyNf> summands;

  ASS(poly.isType<NumTraits>())
  for(unsigned i = 0, c = 0; i < poly.nSummands(); i++) {
    if(poly.nFactors(i) == 0) {
      // this is the case if a AnyPoly contains a constant number
      auto& m = poly.unwrap<Perfect<Polynom>>()->summandAt(i);
      summands.push(AnyPoly(perfect(Polynom(m))));
    } else {
      PolyNf resolved = evaluatedArgs[c++];
      for (unsigned j = 1; j < poly.nFactors(i); j++) {
        resolved = multiplyNormPoly<NumTraits>(resolved, evaluatedArgs[c++]);
      }
      summands.push(resolved);
    }
  }
  auto sum = Polynom(std::move(sumUpNormPoly<NumTraits>(summands)));
  return AnyPoly(perfect(sum));
}

template <class NumTraits>
Lib::Stack<Monom<NumTraits>> PolynomialMultiplication::sumUpNormPoly(Lib::Stack<PolyNf>& polys)
{
  CALL("PolynomialMultiplication::sumUpNormPoly(Lib::Stack<PolyNf> &)")
  using Monom = Kernel::Monom<NumTraits>;
  using Polynom = Kernel::Polynom<NumTraits>;
  using Numeral = typename NumTraits::ConstantType;

  Stack<Monom> monoms;

  for(auto& poly : polys) {
    if(poly.is<AnyPoly>()) {
      auto &anyP = poly.unwrap<AnyPoly>();
      ASS(anyP.isType<NumTraits>())
      for (auto m : anyP.unwrap<Perfect<Polynom>>()->iterSummands()) {
        monoms.push(m);
      }
    } else {
      monoms.push(Monom(Numeral(1), perfect(MonomFactors<NumTraits>(poly))));
    }
  }
  return monoms;
}

template <class NumTraits>
Kernel::AnyPoly PolynomialMultiplication::multiplyNormPoly(Kernel::PolyNf &lhs, Kernel::PolyNf &rhs)
{
  CALL("PolynomialMultiplication::multiplyNormPoly(Kernel::PolyNf &, Kernel::PolyNf &)")
  using MonomFactor = Kernel::MonomFactor<NumTraits>;
  using MonomFactors = Kernel::MonomFactors<NumTraits>;
  using Monom = Kernel::Monom<NumTraits>;
  using Polynom = Kernel::Polynom<NumTraits>;
  using Numeral = typename NumTraits::ConstantType;

  if(!lhs.is<AnyPoly>() && !rhs.is<AnyPoly>()) {
    Lib::Stack<MonomFactor> fStack;
    fStack.push(MonomFactor(lhs, 1));
    fStack.push(MonomFactor(rhs, 1));
    auto facs = perfect(MonomFactors(std::move(fStack)));
    return perfect(Polynom(Monom(Numeral(1), facs)));
  }

  auto l = &lhs;
  auto r = &rhs;

  if(r->is<AnyPoly>()) {
    /**
     * swapping lhs and rhs; after that, only two cases can occur:
     *  - l and r are both of type AnyPoly
     *  - l is an AnyPoly and r is a FuncTerm/Variable
     */
    auto b = r;
    r = l;
    l = b;
  }

  if(r->is<AnyPoly>()) {
    ASS(l->is<AnyPoly>())
    auto &lPoly = l->unwrap<AnyPoly>();
    auto &rPoly = r->unwrap<AnyPoly>();

    ASS(lPoly.is<Perfect<Polynom>>() && rPoly.is<Perfect<Polynom>>())

    Stack<Monom> summands;
    for(auto lSum: lPoly.unwrap<Perfect<Polynom>>()->iterSummands()) {
      for(auto rSum: rPoly.unwrap<Perfect<Polynom>>()->iterSummands()) {
        summands.push(multiplyNormMonom(lSum, rSum));
      }
    }
    return perfect(Polynom(std::move(summands)));
  } else {
    ASS(l->is<AnyPoly>() && (r->is<Perfect<FuncTerm>>() || r->is<Variable>()))
    auto& poly = l->unwrap<AnyPoly>();
    ASS(poly.is<Perfect<Polynom>>())
    Stack<Monom> summands;
    Monom m(Numeral(1), perfect(MonomFactors(*r)));
    for(auto sum : poly.unwrap<Perfect<Polynom>>()->iterSummands()) {
      summands.push(multiplyNormMonom(sum, m));
    }
    return perfect(Polynom(std::move(summands)));
  }
}


template<class NumTraits>
Kernel::Monom<NumTraits> PolynomialMultiplication::multiplyNormMonom(const Kernel::Monom<NumTraits> &lhs, const Kernel::Monom<NumTraits> &rhs)
{
  CALL("PolynomialMultiplication::multiplyNormMonom(const Kernel::Monom<NumTraits>&, const Kernel::Monom<NumTraits>&)")
  using MonomFactor = Kernel::MonomFactor<NumTraits>;
  using MonomFactors = Kernel::MonomFactors<NumTraits>;

  Lib::Stack<MonomFactor> facs;
  Lib::Stack<MonomFactor> facsResolved;

  for(auto f : lhs.factors->iter()) {
    facs.push(f);
  }
  for(auto f : rhs.factors->iter()) {
    facs.push(f);
  }

  std::sort(facs.begin(), facs.end());

  auto num = lhs.numeral * rhs.numeral;
  for(auto f : facs) {
    if(f.term.template tryNumeral<NumTraits>().isSome()) {
      num = num * f.term.template tryNumeral<NumTraits>().unwrap();
    } else if(!facsResolved.isEmpty()) {
      if(facsResolved.top().term == f.term) {
        facsResolved.top().power++;
      } else {
        facsResolved.push(f);
      }
    } else {
      facsResolved.push(f);
    }
  }
  return Monom<NumTraits>(num, perfect(MonomFactors(std::move(facsResolved))));
}


} // namespace Inferences 

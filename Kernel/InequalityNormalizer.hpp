/*
 * File InequalityNormalizer.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __INEQUALITY_NORMALIZER_HPP__
#define __INEQUALITY_NORMALIZER_HPP__

#include "Lib/Int.hpp"
#include "Forwards.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#define DEBUG(...) //DBG(__VA_ARGS__)


namespace Kernel {
  using Inferences::PolynomialEvaluation;
  
  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term >= 0 or term > 0 (for Reals and Rationals)
   * or   term >= 0             (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    Perfect<Polynom<NumTraits>> _term;
    bool _strict;

  public:
    InequalityLiteral(Perfect<Polynom<NumTraits>> term, bool strict) 
      : _term(term), _strict(strict) {}

    friend class InequalityNormalizer;

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return *_term; }

    /* 
     * returns whether this is a strict inequality (i.e. >), 
     * or a non-strict one (i.e. >=) 
     * */
    bool strict() const
    { return _strict; }

    friend std::ostream& operator<<(std::ostream& out, InequalityLiteral const& self) 
    { return out << self._term << (self._strict ? " > " : " >= ") << "0"; }

    Literal* denormalize() const
    {
      auto p = strict() ? NumTraits::greater : NumTraits::geq;
      return p(true, term().denormalize(), NumTraits::zero());
    }
  };

  class InequalityNormalizer {
    // Map<Literal*, Option<InequalityLiteral>> _normalized;
    PolynomialEvaluation _eval;

  public:
    InequalityNormalizer(PolynomialEvaluation eval) 
      : _eval(eval) {  }

    template<class NumTraits> Option<InequalityLiteral<NumTraits>> normalize(Literal* lit) const;
    template<class NumTraits> Literal* denormalize(InequalityLiteral<NumTraits> const& lit) const;
  };


}

////////////////////////////////////////////////////////////////////////////
// impl InequalityLiteral
/////////////////////////////
  
namespace Kernel {

  template<class NumTraits>
  Option<InequalityLiteral<NumTraits>> InequalityNormalizer::normalize(Literal* lit) const
  {
    CALL("InequalityLiteral<NumTraits>::fromLiteral(Literal*)")
    DEBUG("in: ", *lit, "(", NumTraits::name(), ")")
    auto impl = [&]() {

      constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

      using Opt = Option<InequalityLiteral<NumTraits>>;

      auto f = lit->functor();
      if (!theory->isInterpretedPredicate(f))
        return Opt();

      auto itp = theory->interpretPredicate(f);


      auto l = [lit]() -> TermList { return *lit->nthArgument(0); };
      auto r = [lit]() -> TermList { return *lit->nthArgument(1); };
      auto minus = [](TermList l, TermList r) { return NumTraits::add(l, NumTraits::minus(r)); };
      auto one = [](){ return NumTraits::one(); };

      bool strict;
      TermList t;
      switch(itp) {
        case NumTraits::leqI:
          /* l <= r ==> r >= l ==> r - l >= 0 */
          t = minus(r(), l());
          strict = false;
          break;

        case NumTraits::geqI:
          /* l >= r ==> l - r >= 0*/
          t = minus(l(), r());
          strict = false;
          break;

        case NumTraits::lessI:
          if (isInt)  {
            /* l < r ==> r > l ==> r - l > 0 ==> r - l - 1 >= 0 */
            t = minus(minus(r(), l()), one());
            strict = false;
          } else  {
            /* l < r ==> r > l ==> r - l > 0 */
            t = minus(r(), l());
            strict = true;
          }
          break;

        case NumTraits::greaterI:
          if (isInt) {
            /* l > r ==> l - r > 0 ==> l - r - 1 >= 0 */
            t = minus(minus(l(), r()), one());
            strict = false;
          } else {
            /* l > r ==> l - r > 0 */
            t = minus(l(), r());
            strict = true;
          }
          break;

        default: 
          return Opt();
      }

      ASS(!isInt || !strict)
      auto norm = Kernel::normalizeTerm(TypedTermList(t.term()));
      auto simpl = _eval.evaluate(norm).unwrapOr(norm);
      return Opt(InequalityLiteral<NumTraits>(simpl.wrapPoly<NumTraits>(), strict));
    };
    auto out = impl();
    DEBUG("out: ", out);
    return out;
  }

} // namespace Kernel

#undef DEBUG
#endif // __INEQUALITY_NORMALIZER_HPP__


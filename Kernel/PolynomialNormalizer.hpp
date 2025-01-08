/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__

#include "Lib/Int.hpp"
#include "Forwards.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Polynomial.hpp"
#include "Inferences/InferenceEngine.hpp"


namespace Kernel {

using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;

using NormalizationResult = Coproduct<PolyNf 
        , Polynom< IntTraits>
        , Polynom< RatTraits>
        , Polynom<RealTraits>
        , MonomFactors< IntTraits>
        , MonomFactors< RatTraits>
        , MonomFactors<RealTraits>
        >;

PolyNf normalizeTerm(TypedTermList t);
inline PolyNf normalizeTerm(TermList t, SortId sort)
{ return normalizeTerm(TypedTermList(t,sort)); }

inline PolyNf normalizeTerm(Term* t)
{ return normalizeTerm(TypedTermList(t)); }
} // namespace Kernel

/** a memoization realized as a hashmap */
template<class Arg, class Result>
struct MemoNonVars 
{
  Map<Arg, Result> _memo;

public:
  MemoNonVars() : _memo(decltype(_memo)()) {}

  static bool isVar(PolyNf const& p) { return p.is<Variable>(); }
  static bool isVar(TermList const& p) { return p.isVar(); }

  template<class Init> Result getOrInit(Arg const& orig, Init init)
  { 
    return isVar(orig) 
      ? init()
      : _memo.getOrInit(Arg(orig), init);
  }

  Option<Result> get(const Arg& orig)
  { return isVar(orig) ? Option<Result>() : _memo.tryGet(orig).toOwned(); }
};


#endif // __POLYNOMIAL_NORMALIZER_HPP__

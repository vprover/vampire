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

} // namespace Kernel

#endif // __POLYNOMIAL_NORMALIZER_HPP__

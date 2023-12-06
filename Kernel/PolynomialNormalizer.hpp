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
PolyNf normalizeTerm(TypedTermList t, bool& evaluated);
PolyNf simplNormalizeTerm(TypedTermList t, bool& evaluated);

// template<class T>
// PolyNf normalizeTerm(T t)
// { bool dummy; return normalizeTerm(t, dummy); }

template<class T>
PolyNf simplNormalizeTerm(T t)
{ bool dummy; return simplNormalizeTerm(t, dummy); }

// inline PolyNf normalizeTerm(Term* t, bool& evaluated)
// { return normalizeTerm(TypedTermList(t), evaluated); }
} // namespace Kernel

#endif // __POLYNOMIAL_NORMALIZER_HPP__

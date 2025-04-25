/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/TypeList.hpp"

#include "LiteralSelector.hpp"
#include "MaximalLiteralSelector.hpp"
#include "BestLiteralSelector.hpp"
#include "LookaheadLiteralSelector.hpp"
#include "SpassLiteralSelector.hpp"
#include "ELiteralSelector.hpp"
#include "RndLiteralSelector.hpp"

#include "LiteralComparators.hpp"


namespace TL = Lib::TypeList;

namespace LiteralSelectors {

  using namespace LiteralComparators;

  using Comparator2 = CompositeN
    < ColoredFirst
    , MaximalSize
    , LexComparator
    >;

  using Comparator3 = CompositeN
    < ColoredFirst
    , NoPositiveEquality
    , LeastTopLevelVariables
    , LeastDistinctVariables
    , LexComparator
    >;

  using Comparator4 = CompositeN
    < ColoredFirst
    , NoPositiveEquality
    , LeastTopLevelVariables
    , LeastVariables
    , MaximalSize
    , LexComparator
    >;

  using Comparator10 = CompositeN
    < ColoredFirst
    , NegativeEquality
    , MaximalSize
    , Negative
    , LexComparator
    >;

  template<unsigned i, class T> 
  struct OptionValue {
    using type = T;
    static constexpr unsigned number = i;
  };
// TODO reverse polarity for alasca selector

using OptionValues = TL::List<
    OptionValue<0, TotalLiteralSelector>
  , OptionValue<1, MaximalLiteralSelector>
  , OptionValue<2, CompleteBestLiteralSelector<Comparator2>>
  , OptionValue<3, CompleteBestLiteralSelector<Comparator3>>
  , OptionValue<4, CompleteBestLiteralSelector<Comparator4>>
  , OptionValue<10, CompleteBestLiteralSelector<Comparator10>>
  , OptionValue<11, GenericLookaheadLiteralSelector</* complete */ true>>

  , OptionValue<20, GenericSpassLiteralSelector<0>>
  , OptionValue<21, GenericSpassLiteralSelector<1>>
  , OptionValue<22, GenericSpassLiteralSelector<2>>

  , OptionValue<30, GenericELiteralSelector<0>>
  , OptionValue<31, GenericELiteralSelector<1>>
  , OptionValue<32, GenericELiteralSelector<2>>
  , OptionValue<33, GenericELiteralSelector<3>>
  , OptionValue<34, GenericELiteralSelector<4>>
  , OptionValue<35, GenericELiteralSelector<5>>

  , OptionValue<666, GenericRndLiteralSelector</* complte */ true>>

  , OptionValue<1002, BestLiteralSelector<Comparator2>>
  , OptionValue<1003, BestLiteralSelector<Comparator3>>
  , OptionValue<1004, BestLiteralSelector<Comparator4>>
  , OptionValue<1010, BestLiteralSelector<Comparator10>>
  , OptionValue<1011, GenericLookaheadLiteralSelector</* complete */ false>>
  , OptionValue<1666, GenericRndLiteralSelector</* complete */ false>>
  >;


// using SelectorList = TL::Map_type<OptionValues>;
struct __MkSelectorMode {
  template<class OptionValue>
  using apply = TL::Token<typename OptionValue::type>;
};
using SelectorMode = TL::ApplyT<Coproduct, TL::Map<__MkSelectorMode, OptionValues>>;

template<class T>
constexpr auto selectorMode() { return SelectorMode(TL::Token<T>{}); }

inline Option<SelectorMode> getSelectorType(unsigned absSelectorNumber) {
  return LiteralSelectors::OptionValues::find([&](auto token) -> Option<SelectorMode> {
      using OptionValue = TypeList::TokenType<decltype(token)>;
      using OptLiteralSelector = typename OptionValue::type;
      if (OptionValue::number == absSelectorNumber) {
        return some(SelectorMode(TL::Token<OptLiteralSelector>{}));
      } else {
        return {};
      }
  });
}

} // namespace LiteralSelectors


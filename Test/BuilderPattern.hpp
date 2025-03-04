/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__BUILDER_PATTERN_HPP__
#define __TEST__BUILDER_PATTERN_HPP__
namespace Test {

template<class Field>
struct DefaultValue {
  using Type = typename Field::Type;
  static Option<Type> value() { return Option<Type>(); }
};

template<class C>
struct BuilderInitializer
{ using Type = C; };

template<class A>
struct BuilderInitializer<Stack<A>>
{ using Type = std::initializer_list<A>; };


#define BUILDER_METHOD(Self, ty, field)                                                   \
private:                                                                                  \
  Option<ty> _##field;                                                                    \
                                                                                          \
  Option<ty> field() const                                                                \
  {                                                                                       \
    return _##field.isSome()                                                              \
         ? _##field                                                                       \
         : getDefault<__##field##_default>();                                             \
  }                                                                                       \
                                                                                          \
public:                                                                                   \
  Self field(typename BuilderInitializer<ty>::Type field)                                 \
  {                                                                                       \
    _##field = Option<ty>(std::move(field));                                              \
    return std::move(*this);                                                              \
  }                                                                                       \
  struct __ ## field ## _default { using Type = ty; };                                    \
                                                                                          \
                                                                                          \

template<class Field>
Option<typename Field::Type> getDefault()
{ return DefaultValue<Field>::value(); }

} // namespace Test

#endif // __TEST__BUILDER_PATTERN_HPP__

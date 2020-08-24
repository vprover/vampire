#ifndef __LIB_COPRODUCT__H__
#define __LIB_COPRODUCT__H__

#define MACRO_EXPANSION true

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Hash.hpp"
#include "Lib/TypeList.hpp"
#include <memory>
#include <functional>

namespace Lib {

#define POLYMORPHIC_FUNCTION(type, Name, polyArg, constArgs) \
  namespace Polymorphic { \
    struct Name  \
    { \
      constArgs \
      template<class T> \
      type operator()(T polyArg); \
    }; \
  } \
  template<class T> type Polymorphic::Name::operator()(T polyArg) 

#define FOR_REF_QUALIFIER(macro)                                                                                        \
  macro(const &, ) macro(&, ) macro(&&, std::move)

namespace TL = TypeList;

template <class... As> 
class Coproduct;


namespace CoproductImpl {


  template <class... As> union VariadicUnion;
  template <unsigned idx, class As> struct Unwrap;
  template <unsigned idx, unsigned size, class As> struct Apply;
  template <class As> struct Match;

  // TODO get rid of this
  template <> union VariadicUnion<> {
    CLASS_NAME(VariadicUnion)

    inline void unwrap(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }
    ~VariadicUnion() {}
#define ref_polymorphic(REF, MOVE)                                                                                      \
                                                                                                                        \
    template <class R, class F> inline R apply(unsigned idx, F f) REF  \
    { ASSERTION_VIOLATION_REP(idx) }  \
    \
    template <class R, class... F> \
    inline static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F... f) \
    { ASSERTION_VIOLATION_REP(idx) }  \
                                                                                                                        \
    template <class R> inline R match(unsigned idx) REF{ASSERTION_VIOLATION_REP(idx)} \

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic

    inline void destroy(unsigned idx) {ASSERTION_VIOLATION_REP(idx)}
    inline static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {ASSERTION_VIOLATION_REP(idx)}
  };

  template <class A, class... As> union VariadicUnion<A, As...> {
    CLASS_NAME(VariadicUnion)
    // USE_ALLOCATOR(VariadicUnion)
    using Ts = TL::List<A,As...>;

    A _head;
    VariadicUnion<As...> _tail;
    ~VariadicUnion() {}
    VariadicUnion<A, As...> clone(unsigned idx) {
      VariadicUnion out;
      if (idx == 0) {
        out._head = this->_head;
      } else {
        out._tail = _tail.clone(idx);
      }
      return out;
    }

#define ref_polymorphic(REF, MOVE)                                                                                      \
    template <class R, class F> inline R apply(unsigned idx, F f) REF {                                             \
      if (idx == 0) {                                                                                                   \
        return f(MOVE(_head));                                                                                          \
      } else {                                                                                                          \
        return MOVE(_tail).template apply<R>(idx - 1, f);                                                           \
      }                                                                                                                 \
    }                                                                                                                   \
                                                                                                                        \
    template <class R, class F, class... Fs>                                                                            \
    inline R match(unsigned idx, F f, Fs... fs) REF {                                                                   \
      if (idx == 0) {                                                                                                   \
        return f(MOVE(_head));                                                                                          \
      } else {                                                                                                          \
        return MOVE(_tail).template match<R>(idx - 1, fs...);                                                           \
      }                                                                                                                 \
    }                                                                                                                   \
    \
    template <class R, class F, class... Fs>  \
    inline static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F f, Fs... fs) \
    {  \
      if (idx == 0) {                                                                                                   \
        return f(MOVE(lhs._head), MOVE(rhs._head)); \
      } else {                                                                                                          \
        return VariadicUnion<As...>::template match2<R>(idx - 1, MOVE(lhs._tail), MOVE(rhs._tail), fs...);                                             \
      }                                                                                                                 \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic

    inline void destroy(unsigned idx) 
    { 
      if (idx == 0) {
        _head.~A(); 
      } else {
        _tail.destroy(idx - 1);
      }
    }

    inline static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {
      if (idx == 0) {
        return lhs._head == rhs._head;
      } else {
        return VariadicUnion<As...>::equal(idx - 1, lhs._tail, rhs._tail);
      }
    }

    template <unsigned idx, class Bs> friend struct InitStaticTag;
    VariadicUnion() {}

  };

  template <class A, class... As> struct Unwrap<0, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    A REF operator()(VariadicUnion<A, As...> REF self) const {                                                          \
      return MOVE(self._head);                                                                                          \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct Unwrap<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    TL::Get<idx - 1, TL::List<As...>> REF operator()(                                                                   \
        VariadicUnion<A, As...> REF self) const {                                                                       \
      return Unwrap<idx - 1, TL::List<As...>>{}(MOVE(self._tail));                                                      \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
  };


  template <unsigned idx, class As> struct InitStaticTag {};

  template <class A, class... As> struct InitStaticTag<0, TL::List<A, As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<0, TL::List<A, As...>> REF value) const                      \
    { ::new (&self._head) A(MOVE(value)); }                                                                             \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct InitStaticTag<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<idx, TL::List<A, As...>> REF value) const                    \
    { InitStaticTag<idx - 1, TL::List<As...>>{}(self._tail, MOVE(value)); }                                             \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class As> struct InitDynamicTag;

  template <unsigned size, class... As> struct InitDynamicTag<size, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const                     \
    {  ASSERTION_VIOLATION }                                                                                            \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class... As> struct InitDynamicTag<acc, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const                     \
    {                                                                                                                   \
      using Ts = TL::List<As...>;                                                                                       \
      auto unwrap = Unwrap<acc, Ts>{};                                                                                  \
      if (acc == idx) {                                                                                                 \
        ::new (&self) TL::Get<acc,Ts>(unwrap(MOVE(value)));                                                             \
        return;                                                                                                         \
      }                                                                                                                 \
      InitDynamicTag<acc + 1, size, TL::List<As...>>{}(self, idx, MOVE(value));                                         \
    }                                                                                                                   \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  struct PolymorphicHash {
    template<class T>
    size_t operator()(T const& t) const
    { return std::hash<T>{}(t); }
  };
}

template<class... Ords> struct CoproductOrdering;
template<template<class> class Ord> struct PolymorphicCoproductOrdering;

template <class A, class... As> 
class Coproduct<A, As...> 
{
  unsigned _tag;

  CoproductImpl::VariadicUnion<A, As...> _content;
  using Self = Coproduct<A, As...>;
  using Content = decltype(_content);

  /** unsafe default constructor. tag as well as content will be uninit */
  Coproduct() {}

public:
  CLASS_NAME(Coproduct)
  // USE_ALLOCATOR(Coproduct)

  using Ts = TL::List<A, As...>;
  static constexpr unsigned size = TL::Size<Ts>::val;

  unsigned tag() const { return _tag; }

  template <unsigned idx> struct type 
  {
    using value = TL::Get<idx, TL::List<A, As...>>;
  };

  template <unsigned idx> bool is() const {
    static_assert(idx < size, "out of bounds");
    return _tag == idx;
  }

  template <class B> bool is() const {
    return _tag == TL::IdxOf<B, Ts>::val;
  }

  template<class... Bs> using FstTy = TL::Get<0, TL::List<Bs...>>;
  // TODO: get rid of the type parameter Ret here.
#define REF_POLYMORPIHIC(REF, MOVE)                                                                                     \
                                                                                                                        \
  Coproduct(Coproduct REF other) : _tag(other._tag) {                                                                   \
    CALL("Coproduct(Coproduct " #REF " other)")                                                                         \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                           \
  }                                                                                                                     \
                                                                                                                        \
  template <unsigned idx>                                                                                               \
  static Coproduct variant(TL::Get<idx, Ts> REF value) {                                                                \
    Coproduct self;                                                                                                     \
    self._tag = idx;                                                                                                    \
    CoproductImpl::InitStaticTag<idx, Ts>{}(self._content, MOVE(value));                                                \
    return MOVE(self);                                                                                                  \
  }                                                                                                                     \
                                                                                                                        \
  template <class... F>                                                                                                 \
  inline ResultOf<FstTy<F...>, A REF> match(F... fs) REF {                                                              \
    using Ret = ResultOf<FstTy<F...>, A REF>;                                                                           \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template match<Ret>(_tag, fs...);                                                             \
  }                                                                                                                     \
  template <class F>                                                                                                    \
  inline ResultOf<F, A REF> apply(F f) REF {                                                                            \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template apply<ResultOf<F, A REF>>(_tag,f);                                               \
  }                                                                                                                     \
  template <class... F> inline Coproduct map(F... fs) REF {                                                             \
    return match(fs...);                                                                                                \
  }                                                                                                                     \
                                                                                                                        \
  Coproduct &operator=(Coproduct REF other) {                                                                           \
    CALL("Coproduct& operator=(Coproduct " #REF "other)")                                                               \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    _content.destroy(_tag); \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                           \
    _tag = other._tag;                                                                                                  \
    return *this;                                                                                                       \
  }                                                                                                                     \
                                                                                                                        \
  template<class B>                                                                                                     \
  explicit Coproduct(B REF b)                                                                                           \
    : Coproduct(variant<TL::IdxOf<B, Ts>::val>(MOVE(b)))                                                                \
  { }                                                                                                                   \
                                                                                                                        \
  template <class B> inline B REF unwrap() REF {                                                                        \
    return MOVE(unwrap<TL::IdxOf<B, Ts>::val>());                                                                       \
  }                                                                                                                     \
                                                                                                                        \
  template <unsigned idx>                                                                                               \
  inline TL::Get<idx, Ts> REF unwrap() REF {                                                                            \
    CALL("Coproduct::unwrap() " #REF );                                                                                 \
    static_assert(idx < size, "out of bounds");                                                                         \
    ASS_EQ(idx, _tag);                                                                                                  \
    return CoproductImpl::Unwrap<idx, Ts>{}(MOVE(_content));                                                            \
  }

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  // TODO: replace with zipping

  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs)
  {
    if (lhs._tag != rhs._tag) {
      return false;
    } else {
      auto tag = lhs._tag;
      return Content::equal(tag, lhs._content, rhs._content);
    }
  }

  template<class... Bs> friend bool operator!=(const Coproduct<Bs...> &lhs, const Coproduct<Bs...> &rhs)
  { return !(lhs == rhs); }

  ~Coproduct() { _content.destroy(_tag); }

private:
  struct __writeToStream {
    unsigned _tag;
    std::ostream &out;
    template <class B> std::ostream &operator()(const B &b) {
      return out << "Coproduct<" << _tag << ">(" << b << ")";
    }
  };

public:

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self) {
    return self.apply(__writeToStream{self._tag, out});
  }
  friend struct std::hash<Coproduct>;

  template<class... Ords> friend struct CoproductOrdering;
}; // class Coproduct<A, As...> 


namespace TL = TypeList;

template<class... Ords> struct CoproductOrdering 
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { 
    CALL("CoproductOrdering::operator()(Coproduct<As...> const&, Coproduct<As...> const&)")
    if (lhs._tag < rhs._tag) return true;
    if (lhs._tag > rhs._tag) return false;

    auto tag = lhs._tag;
    return CoproductImpl::VariadicUnion<As...>::template match2<bool>(tag, lhs._content, rhs._content, Ords{}...);
  }
};


template<template<class> class Ord> struct PolymorphicCoproductOrdering
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { return CoproductOrdering<Ord<As>...>{}(lhs,rhs); }
};


} // namespace Lib
template<class... Ts> struct std::hash<Lib::Coproduct<Ts...>>
{
  size_t operator()(Lib::Coproduct<Ts...> const& self) const 
  { 
    return Lib::HashUtils::combine(
        std::hash<unsigned>{}(self._tag), 
        self.apply(Lib::CoproductImpl::PolymorphicHash{})); 
  }
};

template<class... As>
struct std::less<Lib::Coproduct<As...> >
{
  bool operator()(const Lib::Coproduct<As...>& lhs, const Lib::Coproduct<As...>& rhs)
  { return Lib::PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};


#endif // __LIB_COPRODUCT__H__

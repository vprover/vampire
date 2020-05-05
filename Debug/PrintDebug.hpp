
#ifndef __PRINT_DEBUG_HPP__
#define __PRINT_DEBUG_HPP__

#include <iostream>

#if VDEBUG
#define DBG(...) Debug::dbg(#__VA_ARGS__, " = ", __VA_ARGS__);
#else 
#define DBG(...) 
#endif 
#include "Lib/vstd.h"

namespace Debug {

template <class A> struct print_debug {
  void operator()(std::ostream &out, const A &a) const { out << a; }
};

template <class A> struct print_debug<vvec<A>> {
  void operator()(std::ostream &out, const vvec<A> &a) const {
    out << "[";
    auto i = a.begin();
    if (i != a.end()) {
      out << *i;
      i++;
      for (; i != a.end(); i++) {
        out << ", " << *i;
      }
    }
    out << "]";
  }
};

template <class A> struct print_debug<refw<A>> {
  void operator()(std::ostream &out, const refw<A> &a) const {
    print_debug<A>{}(out, a.get());
  }
};

template <class A> struct print_debug<rc<A>> {
  void operator()(std::ostream &out, const rc<A> &a) const {
    print_debug<A>{}(out, *a.get());
  }
};

template <class... As> struct dbgr {
  static void debug(std::ostream &out, const As &... as);
};

template <> struct dbgr<> {
  static void debug(std::ostream &out) {}
};

template <class A, class... As> struct dbgr<A, As...> {
  static void debug(std::ostream &out, const A &a, const As &... as) {
    print_debug<A>{}(out, a);
    dbgr<As...>::debug(out, as...);
  }
};

template <class... As> void dbg(const As &... as) {
#if VDEBUG
  std::cout << "[ dbg  ]\t";
  dbgr<As...>::debug(std::cout, as...);
  std::cout << std::endl;
#endif 
}

}


#endif // __PRINT_DEBUG_HPP__

#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__ABSTRACT_LITERAL_CONTAINER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__ABSTRACT_LITERAL_CONTAINER__

#include "Lib/Allocator.hpp"
#include "Lib/vstd.h"

#include <functional>
#include <set>
#include <unordered_map>

template <class A> struct EquivalenceClass {
  // using equal = class Equal;
  using less = class Less;
  // template <class B> void dump(std::ostream &out, const B &t);
};

template <class A> class Equality;

template <class A> struct EquivalenceClass<Equality<A>> {
  // using equal = std::equal_to<A>;
  using less = std::less<A>;
  // template <class B> void dump(std::ostream &out, const B &t) { out << t; }
};

// template<class A>
// class TupEq;
//
// template<class A>
// struct EquivalenceClass<TupEq<A>> {
//     // using equal = std::equal_to<A>;
//     using value_type = A;
//     using less  = std::less<A>;
//     void dump(std::ostream& out, const A& t) {
//       out << t;
//     }
// };

template <class A> struct EquivalenceClass<Equality<rc<A>>> {
  // struct _hash {
  //     _hash() {}
  //
  //     ~_hash() {}
  //
  //     _hash(const _hash &other) {}
  //
  //     _hash(const _hash &&other) {}
  //
  //     size_t operator()(const rc<A> &self) const {
  //         return self.get()->hash_code();
  //     }
  // };
  //
  // using hash = _hash;
  using value_type = rc<A>;
  using less = struct {
    bool operator()(const rc<A> &lhs, const rc<A> &rhs) const {
      return *lhs.get() < *rhs.get();
    }
  };
  // template<class B>
  // void dump(std::ostream& out, const rc<B>& t) {
  //   EquivalenceClass<Equality<B>>::dump(out, *t.get());
  // }
  // using equal = struct {
  //     bool operator()(const rc<A> &lhs, const rc<A> &rhs) const {
  //         return *lhs.get() == *rhs.get();
  //     }
  // };
};

template <class A, class Equiv> class Container {
  CLASS_NAME(Container)
  USE_ALLOCATOR(Container)

  using _less = typename EquivalenceClass<Equiv>::less;
  using _set = set<A, std::less<A>, vamp_alloc<A>>;
  using m_set = map<A, size_t, _less, vamp_alloc<pair<const A, size_t>>>;
  // using m_set = map<A, _set, _less, vamp_alloc<pair<const A, _set>>>;

public:
  m_set _content;

  Container() : _content(m_set()) {}

  Container operator()() { return Container(); }

  void insert(A &l) {
    auto x = _content.find(l);
    if (x == _content.end()) {
      auto r = _content.insert(make_pair(l,0));
      // auto r = _content.insert(std::pair<A, _set>(l, _set()));
      // ASS_REP(r.second, *r.first->first);
      x = r.first;
    }
    x->second++;
  }

  decltype(_content.begin()) begin() { return _content.begin(); }

  decltype(_content.end()) end() { return _content.end(); }

  using ref = Container<refw<A>, Equiv>;

  void serialize(const char* container_name, ostream &out) const {
    for (auto &pair : _content) {
      auto size = pair.second; //.size();
      // auto &&elems = pair.second;
      // ASS_REP(size > 0, size);

      out << "[ equivalence class ]" 
          << "\t"
          << container_name
          << "\t" << size << "\t";
      // Equiv::dump(out, **min_element(elems.begin(), elems.end()));
      Equiv::dump(out, *pair.first.get());
      out << endl;
    }
  }
  void dump(ostream &out) const {
    using entry = typename decltype(_content)::value_type;
    using elem_t = typename decltype(_content)::value_type::first_type;
    auto c = vvec<const entry *>();
    for (auto &e : _content) {
      c.push_back(&e);
    }
    struct {
      bool operator()(const entry *l, const entry *r) {
        return l->second.size() > r->second.size();
      }
    } comp;
    sort(c.begin(), c.end(), comp);

#ifdef PRINT_TOP_N
    c.resize(min<size_t>(PRINT_TOP_N, c.size()));
#endif
    int i = 1;
    for (auto &pair : c) {
      auto size = pair->second.size();
      auto &&elems = pair->second;
      ASS_REP(size > 0, size);

      out << i << "."
          << "\t" << size << "\t";
      Equiv::dump(out, **min_element(elems.begin(), elems.end()));
      out << endl;
      i++;
    }
  }
};

#endif

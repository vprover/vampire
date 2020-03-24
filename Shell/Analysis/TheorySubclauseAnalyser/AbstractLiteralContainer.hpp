#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__ABSTRACT_LITERAL_CONTAINER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__ABSTRACT_LITERAL_CONTAINER__


#include "Lib/Allocator.hpp"
#include "Lib/vstd.h"

#include <functional>
#include <set>
#include <unordered_map>

template<class A>
struct EquivalenceClass {
    // using equal = class Equal;
    using less  = class Less;
};

template<class A>
class Equality;

template<class A>
struct EquivalenceClass<Equality<A>> {
    // using equal = std::equal_to<A>;
    using less  = std::less<A>;
};

template<class A>
class TupEq;

template<class A>
struct EquivalenceClass<TupEq<A>> {
    // using equal = std::equal_to<A>;
    using less  = std::less<A>;
};

template<class A>
struct EquivalenceClass<Equality<rc<A>>> {
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
    using less = struct {
      bool operator()(const rc<A>& lhs, const rc<A>& rhs) const {
        return *lhs.get() < *rhs.get();
      }
    };
    // using equal = struct {
    //     bool operator()(const rc<A> &lhs, const rc<A> &rhs) const {
    //         return *lhs.get() == *rhs.get();
    //     }
    // };
};



template<class A, class Equiv>
class Container {
    CLASS_NAME(Container)
    USE_ALLOCATOR(Container)

    using _less = typename EquivalenceClass<Equiv>::less;
    using _set = set<A, std::less<A>, vamp_alloc<A>>;
    using m_set = map<A, _set, _less, vamp_alloc<pair<const A,_set > > >;
public:
    m_set _content;

    Container() : _content(m_set()) {}

    Container operator()() { return Container(); }

    void insert(A& l) {
        auto x = _content.find(l);
        if (x == _content.end()) {
            auto r = _content.insert(std::pair<A,_set>(l,_set()));
            //ASS_REP(r.second, *r.first->first);
            x = r.first;
        }
        x->second.insert(l);
    }

    decltype(_content.begin()) begin() { return _content.begin(); }

    decltype(_content.end()) end() { return _content.end(); }

    using ref = Container<refw<A>, Equiv>;
};

#endif

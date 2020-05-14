
//
// Created by Johannes Schoisswohl on 23.03.20.
//

#ifndef VAMPIRE_VSTD_H
#define VAMPIRE_VSTD_H
#include <set>
#include <map>
#include <vector>
#include <memory>
#include <unordered_map>
#include "Lib/Allocator.hpp"

namespace Lib {
namespace StdWrappers {


/**
 * A std library conform wrapper for the allocator. This struct can be used with vectors, sets, maps, ect.
 */
template<class T>
class alloc {
public:
    typedef T value_type;

    static T *allocate(size_t n, const void *hint = 0) {
        return (T *) Lib::Allocator::current->allocateKnown(n * sizeof(T)
#if VDEBUG
                , typeid(T).name()
#endif
        );
    }

    static void deallocate(T *p, size_t n) {
        return Lib::Allocator::current->deallocateKnown((void *) p, n * sizeof(T)
#if VDEBUG
                , typeid(T).name() 
#endif
        );
    }

    template<class U>
    alloc(const alloc<U>& other) noexcept {}
    alloc() noexcept {}
    ~alloc() {}

    bool operator==(alloc &other) { return true; }
    bool operator!=(alloc &other) { return false; }
};


template<class t> using vvec  = std::vector<t, alloc<t>>;
template<class T> using refw = std::reference_wrapper<T>;
template<class T> class rc: public std::shared_ptr<T> {
public:
    rc(T* t) : std::shared_ptr<T>(t, [](T* t){delete t;}, alloc<T*>()) {}
    // rc(rc& other) : std::shared_ptr<T>(other) {}
    // rc(const rc& other) : std::shared_ptr<T>(other) {}
#define DELEGATE(OP) \
    friend bool operator OP(const rc& lhs, const rc& rhs) { \
      const T& l = *lhs; \
      const T& r = *rhs; \
      return l OP r; \
    } \

    DELEGATE(==)
    DELEGATE(<)
};

template<class T, class Compare = std::less<T>> using set = std::set<T, Compare, alloc<T>>;
template<class K, class V, class Hash = std::hash<K>, class Pred = std::equal_to<K>> using unordered_map  = std::unordered_map<K, V, Hash,Pred,  alloc<std::pair<const K,V>>>;
template<class K, class V, class Compare = std::less<K>> using map  = std::map<K, V, Compare, alloc<std::pair<const K, V > > >;

} // namespace StdWrappers 
} // namespace Lib

#endif //VAMPIRE_VSTD_H

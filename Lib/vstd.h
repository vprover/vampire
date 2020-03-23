//
// Created by Johannes Schoisswohl on 23.03.20.
//

#ifndef VAMPIRE_VSTD_H
#define VAMPIRE_VSTD_H
#include <set>
#include <map>
#include <vector>
#include <memory>

#include "Lib/Allocator.hpp"

/**
 * A std library conform wrapper for the allocator. This struct can be used with vectors, sets, maps, ect.
 */
template<class T>
class vamp_alloc {
public:
    typedef T value_type;

    static T *allocate(size_t n, const void *hint = 0) {
        return (T *) Allocator::current->allocateKnown(n * sizeof(T)
#ifdef VDEBUG
                , typeid(T).name()
#endif
        );
    }

    static void deallocate(T *p, size_t n) {
        return Allocator::current->deallocateKnown((void *) p, n * sizeof(T)
#ifdef VDEBUG
                , typeid(T).name()
#endif
        );
    }

    template<class U>
    vamp_alloc(const vamp_alloc<U>& other) noexcept {}

    vamp_alloc() noexcept {}

    ~vamp_alloc() {}

    bool operator==(vamp_alloc &other) { return true; }

    bool operator!=(vamp_alloc &other) { return *this != other; }
};


template<class t> using vvec  = std::vector<t, vamp_alloc<t>>;
template<class T> using refw = std::reference_wrapper<T>;
template<class T> class rc: public std::shared_ptr<T> {
public:
    rc(T* t) : std::shared_ptr<T>(t, [](T* t){delete t;}, vamp_alloc<T*>()) {}
};
template<class T, class Compare = std::less<T>> using tset = std::set<T, Compare, vamp_alloc<T>>;

#endif //VAMPIRE_VSTD_H

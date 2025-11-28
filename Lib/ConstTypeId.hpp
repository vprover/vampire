
#ifndef LIB_CONST_TYPE_ID_HPP
#define LIB_CONST_TYPE_ID_HPP

#include <cstddef>

// Adapted from https://gist.github.com/ktf/b51547b25f6467b2fb352d239b6080e2

namespace Lib {
  struct ConstTypeId
  {
    ConstTypeId() = default;

    template<size_t N>
    constexpr ConstTypeId(const char (&str)[N]) :
        str{&str[0]},
        length{N - 1}
    {}

    template<typename T>
    constexpr static ConstTypeId getTypeId()
    {
      return ConstTypeId(__PRETTY_FUNCTION__);
    }

    constexpr bool operator==(const ConstTypeId& other) const {
      return str == other.str;
    }

    constexpr bool operator!=(const ConstTypeId& other) const {
      return !operator==(other);
    }

    const char* str;
    size_t length;
  };
};

#endif
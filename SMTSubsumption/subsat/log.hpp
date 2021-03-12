#ifndef SUBSAT_LOG_HPP
#define SUBSAT_LOG_HPP

#include "./subsat_config.hpp"


#if SUBSAT_LOGGING_ENABLED


#include <cstdint>
#include <iostream>
#include <vector>
#include <typeinfo>
#include "./vector_map.hpp"

namespace numerical_chars {
inline std::ostream &operator<<(std::ostream &os, char c) {
    return std::is_signed<char>::value ? os << static_cast<int>(c)
                                       : os << static_cast<unsigned int>(c);
}

inline std::ostream &operator<<(std::ostream &os, signed char c) {
    return os << static_cast<int>(c);
}

inline std::ostream &operator<<(std::ostream &os, unsigned char c) {
    return os << static_cast<unsigned int>(c);
}
}

template <typename T, typename Allocator>
struct ShowVec {
  std::vector<T, Allocator> const& vec;
};

template<typename T, typename Allocator>
std::ostream& operator<<(std::ostream& os, ShowVec<T, Allocator> const& sv)
{
  using namespace numerical_chars;
  auto const& vec = sv.vec;

  if (vec.empty()) {
    return os << "[]";
  }

  os << "[ ";
  bool first = true;
  for (auto&& x : vec) {
    if (first) {
      first = false;
    } else {
      os << ", ";
    }
    os << x;
  }
  os << " ]";
  return os;
}

template<typename T, typename Allocator>
ShowVec<T, Allocator> SHOWVEC(std::vector<T, Allocator> const& vec)
{
    return ShowVec<T, Allocator>{vec};
}

template<typename Key, typename T, typename Allocator, typename Indexing>
ShowVec<T, Allocator> SHOWVEC(subsat::vector_map<Key, T, Allocator, Indexing> const& vecmap)
{
    return ShowVec<T, Allocator>{vecmap.underlying()};
}


/// Lower log level means more important
enum class LogLevel : int {
  Error = 0,
  Warn = 1,
  Info = 2,
  Debug = 3,
  Trace = 4,
};

/// Filter log messages
bool
subsat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

std::pair<std::ostream&, bool>
subsat_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

#define LOG(lvl, x)                                               \
  do {                                                            \
    if (subsat_should_log(lvl, __func__, __PRETTY_FUNCTION__)) {  \
      auto pair = subsat_log(lvl, __func__, __PRETTY_FUNCTION__); \
      std::ostream& os = pair.first;                              \
      bool should_reset = pair.second;                            \
      os << x;                                                    \
      if (should_reset) {                                         \
        os << "\x1B[0m"; /* reset color */                        \
      }                                                           \
      os << std::endl;                                            \
    }                                                             \
  } while (false)

#define LOG_WARN(x)  LOG(LogLevel::Warn, x)
#define LOG_INFO(x)  LOG(LogLevel::Info, x)
#define LOG_DEBUG(x) LOG(LogLevel::Debug, x)
#define LOG_TRACE(x) LOG(LogLevel::Trace, x)


#else  // SUBSAT_LOGGING_ENABLED


#define LOG(lvl, x)  \
  do {               \
    /* do nothing */ \
  } while (false)

#define LOG_WARN(x)  LOG(0, x)
#define LOG_INFO(x)  LOG(0, x)
#define LOG_DEBUG(x) LOG(0, x)
#define LOG_TRACE(x) LOG(0, x)


#endif  // SUBSAT_LOGGING_ENABLED


#endif  // SUBSAT_LOG_HPP

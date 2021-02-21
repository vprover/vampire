#ifndef LOG_HPP
#define LOG_HPP

#ifndef LOGGING_ENABLED
#   if !defined(NDEBUG) && defined(SUBSAT_STANDALONE)
#       define LOGGING_ENABLED 1
#   else
#       define LOGGING_ENABLED 0
#   endif
#endif


#if LOGGING_ENABLED


#include <iostream>

/// lower level means more important
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

#define LOG(lvl, x)                                              \
  do {                                                           \
    if (subsat_should_log(lvl, __func__, __PRETTY_FUNCTION__)) { \
      auto [os, should_reset] =                                  \
          subsat_log(lvl, __func__, __PRETTY_FUNCTION__);        \
      os << x;                                                   \
      if (should_reset) {                                        \
        os << "\x1B[0m"; /* reset color */                       \
      }                                                          \
      os << std::endl;                                           \
    }                                                            \
  } while (false)

#define LOG_WARN(x)  LOG(LogLevel::Warn, x)
#define LOG_INFO(x)  LOG(LogLevel::Info, x)
#define LOG_DEBUG(x) LOG(LogLevel::Debug, x)
#define LOG_TRACE(x) LOG(LogLevel::Trace, x)


#else  // LOGGING_ENABLED


#define LOG(lvl, x)  \
  do {               \
    /* do nothing */ \
  } while (false)

#define LOG_WARN(x)  LOG(0, x)
#define LOG_INFO(x)  LOG(0, x)
#define LOG_DEBUG(x) LOG(0, x)
#define LOG_TRACE(x) LOG(0, x)


#endif  // LOGGING_ENABLED


#endif  // LOG_HPP

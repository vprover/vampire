/**
 * Usage:
 *
 *    CDEBUG("message: " << 123);
 *
 * If DEBUG_STREAM_ENABLED is true, prints the message to std:cerr,
 * and automatically adds a newline character at the end.
 *
 * Otherwise, do nothing.
 *
 * By default, DEBUG_STREAM_ENABLED is only enabled in debug mode.
 */

#include <iostream>


// By default, enable output in debug mode
#ifndef DEBUG_STREAM_ENABLED
#   define DEBUG_STREAM_ENABLED VDEBUG
#endif

#ifdef CDEBUG
#   undef CDEBUG
#endif

#if DEBUG_STREAM_ENABLED
#define CDEBUG(x)                \
  do                             \
  {                              \
    std::cerr << x << std::endl; \
  } while (false)
#else
#define CDEBUG(x) \
  do              \
  { /* nothing */ \
  } while (false)
#endif


#ifndef LOGGING_ENABLED
#   define LOGGING_ENABLED (!defined(NDEBUG) && defined(SUBSAT_STANDALONE))
#endif


#if LOGGING_ENABLED


#ifndef LOG_DEFINED
#define LOG_DEFINED
namespace {
/// lower level means more important
enum class LogLevel : int {
  Warn = 1,
  Info = 2,
  Debug = 3,
  Trace = 4,
};

/// Filter log messages
bool should_log(LogLevel msg_level, std::string fn, std::string pretty_fn)
{
  // by default, log everything
  LogLevel max_log_level = LogLevel::Trace;

  bool const from_decision_queue =
      pretty_fn.find("DecisionQueue") != std::string::npos;

  if (from_decision_queue) {
    max_log_level = LogLevel::Info;
  }

  return msg_level <= max_log_level;
}

std::ostream& log(LogLevel msg_level, std::string fn, std::string pretty_fn)
{
  size_t width = 20;
  size_t padding = width - std::min(width, fn.size());
  return std::cerr << "[" << fn << "] " << std::string(padding, ' ');
}
}  // namespace
#endif  // LOG_DEFINED


#define LOG(lvl, x)                                              \
  do {                                                           \
    if (should_log(lvl, __func__, __PRETTY_FUNCTION__)) {        \
      log(lvl, __func__, __PRETTY_FUNCTION__) << x << std::endl; \
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


#undef DEBUG_STREAM_ENABLED

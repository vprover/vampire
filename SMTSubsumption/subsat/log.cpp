#include <unistd.h>
#include <optional>
#include <utility>

#include "./log.hpp"

#if LOGGING_ENABLED

/// Filter log messages
bool
subsat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn)
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

static char const*
level_name(LogLevel msg_level)
{
  switch (msg_level) {
    case LogLevel::Error: return "[ERROR]";
    case LogLevel::Warn:  return "[WARN] ";
    case LogLevel::Info:  return "[INFO] ";
    case LogLevel::Debug: return "[DEBUG]";
    case LogLevel::Trace: return "[TRACE]";
    default:              return "[???]  ";
  }
}

static std::optional<char const*>
level_color(LogLevel msg_level)
{
  switch (msg_level) {
    case LogLevel::Error:
      return "\x1B[31m"; // red
    case LogLevel::Warn:
      return "\x1B[33m"; // yellow
    case LogLevel::Info:
      return "\x1B[34m"; // blue
    default:
      return std::nullopt;
  }
}

std::pair<std::ostream&, bool>
subsat_log(LogLevel msg_level, std::string fn, std::string pretty_fn)
{
  std::ostream& os = std::cerr;
  int const fd = fileno(stderr);

  size_t width = 20;
  size_t padding = width - std::min(width, fn.size());

  auto color = level_color(msg_level);
  if (color && !isatty(fd)) { color = std::nullopt; }

  if (color) { os << *color; }
  os << level_name(msg_level) << " [" << fn << "] " << std::string(padding, ' ');
  return {os, (bool)color};
}

#endif  // LOGGING_ENABLED

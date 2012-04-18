/**
 * @file Log.hpp
 * Defines class Log.
 */

#ifndef __Debug_Log__
#define __Debug_Log__

#include <climits>
#include <string>
#include <iostream>

#ifndef LOGGING
#define LOGGING 1
#endif

#if LOGGING

namespace Kernel {
  class Unit;
}

namespace Debug {

class Logging
{
public:
  struct TagDeclTrigger {
    TagDeclTrigger() { doTagDeclarations(); }
  };

  class Impl;

  struct TagInfoBase {
    std::string name;

    bool statsEnabled;
    bool logEnabled;

    bool intOnly;
    bool unitOnly;

    TagInfoBase(std::string name)
    : name(name),
      statsEnabled(false),
      logEnabled(false),
      intOnly(false),
      unitOnly(false) {}
  };
private:
  struct TagInfo;
  struct ChildInfo;
  struct StatObserver;

  static TagDeclTrigger s_trigger;

  static Impl& impl();


  static void declareTag(const char* tag);
  static void addDoc(const char* tag, const char* doc);
  static void addParent(const char* child, const char* parent, unsigned depth);
  static void markUnitTag(const char* tag);
  static void markIntTag(const char* tag);
public:
  static TagInfoBase& getTagInfo(const char* tag);

  static void enableTag(const char* tag, unsigned depthLimit=UINT_MAX);
  static void processTraceSpecString(std::string str);
  static void pushTagStates();
  static void popTagStates();

  static void displayStats(std::ostream& stm);

  static bool isTagEnabled(const char* tag);

  static void logUnit(TagInfoBase& tib, Kernel::Unit* u);

  static void logSimpl(TagInfoBase& tib, Kernel::Unit* src, Kernel::Unit* tgt, const char* doc=0);
  static void logSimpl2(TagInfoBase& tib, Kernel::Unit* prem1, Kernel::Unit* prem2, Kernel::Unit* tgt, const char* doc=0);
  static void logTaut(TagInfoBase& tib, Kernel::Unit* u, const char* doc=0);


  static void statSimple(TagInfoBase& tib);
  static void statInt(TagInfoBase& tib, int val);
  static void statUnit(TagInfoBase& tib, Kernel::Unit* u);


  static void doTagDeclarations();

};

#define tout std::cerr
#define TAG_ENABLED(tag) Debug::Logging::isTagEnabled(tag)

#define DISPLAY_TRACE_STATS(stm) Debug::Logging::displayStats(stm)

#define TRACE_BASE(tag,stat_code,...)							\
  do {											\
    static Debug::Logging::TagInfoBase& LOGGING_tib = Debug::Logging::getTagInfo(tag);	\
    if(LOGGING_tib.statsEnabled) { stat_code } 						\
    if(LOGGING_tib.logEnabled) { __VA_ARGS__ } } while(false)				\


#define ENABLE_TAG(tag) Debug::Logging::enableTag(tag)
#define ENABLE_TAG_LIMITED(tag,limit) Debug::Logging::enableTag(tag,limit)

/**
 * Add marker to the current state of tags, so it can be later restored
 * by @c POP_TAG_STATES
 */
#define PUSH_TAG_STATES Debug::Logging::pushTagStates
/**
 * Restore state of tags that was earlier stored by PUSH_TAG_STATES
 */
#define POP_TAG_STATES Debug::Logging::popTagStates

/**
 * Process string specifying trace settings
 *
 * The format of the string is the following:
 *
 * [trace_name1[:depth_limit1][,trace_name2[:depth_limit2][,...]]]
 *
 * Depth limit can be used to cut-off subtraces of the specified
 * trace. When no limit is specified, the depth of enabled child
 * traces is not limited
 *
 * One can also pass some special strings:
 *   help -- displays help and exits the process with status 0
 *   help+ -- displays hep without exitting
 */
#define PROCESS_TRACE_SPEC_STRING(str) Debug::Logging::processTraceSpecString(str)
#define DISPLAY_HELP() PROCESS_TRACE_SPEC_STRING("help+")


struct ScopedTraceTag {
  ScopedTraceTag(const char* tag) {
    PUSH_TAG_STATES();
    ENABLE_TAG(tag);
  }
  ~ScopedTraceTag() {
    POP_TAG_STATES();
  }
};

struct ConditionalScopedTraceTag {
private:
  bool _active;
public:
  ConditionalScopedTraceTag(bool active, const char* tag) : _active(active) {
    if(_active) {
      PUSH_TAG_STATES();
      ENABLE_TAG(tag);
    }
  }
  ~ConditionalScopedTraceTag() {
    if(_active) {
      POP_TAG_STATES();
    }
  }
};

#define AUX_SCOPED_TRACE_TAG_(SEED,Tag) Debug::ScopedTraceTag _sct_##SEED##_(Tag);
#define AUX_SCOPED_TRACE_TAG(SEED,Tag) AUX_SCOPED_TRACE_TAG_(SEED,Tag)
#define SCOPED_TRACE_TAG(Tag) AUX_SCOPED_TRACE_TAG(__LINE__,Tag)

#define AUX_CONDITIONAL_SCOPED_TRACE_TAG_(SEED,Cond,Tag) Debug::ConditionalScopedTraceTag _csct_##SEED##_(Cond,Tag);
#define AUX_CONDITIONAL_SCOPED_TRACE_TAG(SEED,Cond,Tag) AUX_CONDITIONAL_SCOPED_TRACE_TAG_(SEED,Cond,Tag)
#define CONDITIONAL_SCOPED_TRACE_TAG(Cond,Tag) AUX_CONDITIONAL_SCOPED_TRACE_TAG(__LINE__,Cond,Tag)


}

#else

#define TAG_ENABLED(tag) false
#define DISPLAY_TRACE_STATS(stm)
#define TRACE_BASE(tag,stat_code,...)
#define ENABLE_TAG(tag)
#define ENABLE_TAG_LIMITED(tag,limit)
#define PUSH_TAG_STATES
#define POP_TAG_STATES
#define PROCESS_TRACE_SPEC_STRING(str)
#define DISPLAY_HELP()
#define SCOPED_TRACE_TAG(Tag)
#define CONDITIONAL_SCOPED_TRACE_TAG(Cond,Tag)

#endif


//These are derived macros. If the based macros are disabled, these are
//expanded into empty strings as well.

#define TRACE(tag,...) TRACE_BASE(tag, Debug::Logging::statSimple(LOGGING_tib); , __VA_ARGS__)
#define TRACE_OUTPUT_UNIT(u) Debug::Logging::logUnit(LOGGING_tib,u)

#define COND_TRACE_BASE(tag,cond,stat_code,...) TRACE_BASE(tag, if(cond) { stat_code }, if(cond) { __VA_ARGS__ } )
#define COND_TRACE(tag,cond,...) COND_TRACE_BASE(tag, cond, Debug::Logging::statSimple(LOGGING_tib);,	\
      ASS_REP(!LOGGING_tib.intOnly,LOGGING_tib.name); 							\
      ASS_REP(!LOGGING_tib.unitOnly,LOGGING_tib.name); __VA_ARGS__)
#define LOG(tag,msg) TRACE(tag, (tout << msg) << std::endl;)
#define COND_LOG(tag,cond,msg) COND_TRACE(tag, cond, (tout << msg) << std::endl;)
#define LOGV(tag,var) LOG(tag, #var<<": "<<(var))
#define LOG_UNIT(tag,u) TRACE_BASE(tag, Debug::Logging::statUnit(LOGGING_tib, u);, \
      ASS_REP(!LOGGING_tib.intOnly,LOGGING_tib.name); TRACE_OUTPUT_UNIT(u); )
#define COND_LOG_UNIT(tag,u) COND_TRACE_BASE(tag, cond, Debug::Logging::statUnit(LOGGING_tib, u);, \
      ASS_REP(!LOGGING_tib.intOnly,LOGGING_tib.name); TRACE_OUTPUT_UNIT(u); )
#define LOG_INT(tag,num) TRACE_BASE(tag, Debug::Logging::statInt(LOGGING_tib, num);, \
      ASS_REP(!LOGGING_tib.unitOnly,LOGGING_tib.name); tout << LOGGING_tib.name << ": " << (num) << std::endl; )
#define COND_LOG_INT(tag,cond,num) COND_TRACE_BASE(tag, cond, Debug::Logging::statInt(LOGGING_tib, num);, \
      ASS_REP(!LOGGING_tib.unitOnly,LOGGING_tib.name); tout << LOGGING_tib.name << ": " << (num) << std::endl; )

/**
 * Logs single-premise simplification of a unit
 *
 * Arguments are tag,src,tgt[,doc]
 */
#define LOG_SIMPL(tag,src,...) TRACE(tag, Debug::Logging::logSimpl(LOGGING_tib,src,__VA_ARGS__); )
/**
 * Logs two-premise simplification of a unit
 *
 * Arguments are tag,prem1,prem2,tgt[,doc]
 */
#define LOG_SIMPL2(tag,prem1,prem2,...) TRACE(tag, Debug::Logging::logSimpl2(LOGGING_tib,prem1,prem2,__VA_ARGS__); )

/**
 * Logs the fact that unit has been found a tautology
 *
 * Arguments are tag,unit[,doc]
 */
#define LOG_TAUT(tag,...) TRACE(tag, Debug::Logging::logTaut(LOGGING_tib,__VA_ARGS__); )


#endif // __Debug_Log__

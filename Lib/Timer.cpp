/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Timer.cpp
 * Implements class Timer.
 */

#include <csignal>
#include <unistd.h>
#include <sys/time.h>
#include <sys/times.h>

// for checking instruction count
#ifdef __linux__
#include <sys/ioctl.h>
#include <linux/perf_event.h>
#include <asm/unistd.h>
#endif

#include "Environment.hpp"
#include "System.hpp"
#include "Sys/Multiprocessing.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Timer.hpp"

#define DEBUG_TIMER_CHANGES 0
#define MEGA (1 << 20)

// things that need to be signal-safe because they are used in timer_sigalrm_handler
// in principle we also need is_lock_free() to avoid deadlock as well
// not sure it's worth assertion-failing over
std::atomic<int> timer_sigalrm_counter{-1};
std::atomic<unsigned> protectingTimeout{0};
std::atomic<unsigned char> callLimitReachedLater{0}; // 1 for a timelimit, 2 for an instruction limit
std::atomic<bool> Timer::s_limitEnforcement{true};

// TODO probably these should also be atomics, but not sure
#ifdef __linux__
char* error_to_report = nullptr;
int perf_fd = -1; // the file descriptor we later read the info from
long long last_instruction_count_read = -1;
#endif

long Timer::s_ticksPerSec;
int Timer::s_initGuarantedMiliseconds;

unsigned Timer::elapsedMegaInstructions() {
#ifdef __linux__
  return (last_instruction_count_read >= 0) ? last_instruction_count_read/MEGA : 0;
#else
  return 0;
#endif
}

[[noreturn]] void limitReached(unsigned char whichLimit)
{
  using namespace Shell;

  // for debugging crashes of limitReached: it is good to know what was called by vampire proper just before the interrupt
  // Debug::Tracer::printStack(cout);

  const char* REACHED[3] = {"","Time limit reached!\n","Instruction limit reached!\n"};
  const char* STATUS[3] = {"","% SZS status Timeout for ","% SZS status InstrOut for "};

  // CAREFUL, we might be in a signal handler and potentially at the same time inside Allocator which is not re-entrant
  // so any code below that allocates might corrupt the allocator state.
  // Therefore, the printing below should avoid allocations!

  env.beginOutput();
  reportSpiderStatus('t');
  if (outputAllowed()) {
    addCommentSignForSZS(env.out());
    env.out() << REACHED[whichLimit];

    if (UIHelper::portfolioParent) { // the boss
      addCommentSignForSZS(env.out());
      env.out() << "Proof not found in time ";
      Timer::printMSString(env.out(),env.timer->elapsedMilliseconds());

#ifdef __linux__
      if (last_instruction_count_read > -1) {
        env.out() << " nor after " << last_instruction_count_read << " (user) instruction executed.";
      }
#endif
      env.out() << endl;

      if (szsOutputMode()) {
        env.out() << STATUS[whichLimit] << (env.options ? env.options->problemName().c_str() : "unknown") << endl;
      }
    } else // the actual child
      if (env.statistics) {
        env.statistics->print(env.out());
    }
  }
  env.endOutput();

  System::terminateImmediately(1);
}

void
timer_sigalrm_handler (int sig)
{
#if DEBUG_TIMER_CHANGES
  if(timer_sigalrm_counter<0) {
    cout << "Timer value became negative in timer_sigalrm_handler: " << timer_sigalrm_counter <<endl;
    System::terminateImmediately(1);
  }
#endif

  timer_sigalrm_counter++;

  if(Timer::s_limitEnforcement && env.timeLimitReached()) {
    if (protectingTimeout) {
      callLimitReachedLater = 1; // 1 for a time limit
    } else {
      limitReached(1); // 1 for a time limit
    }
  }

#ifdef __linux__
  if(Timer::s_limitEnforcement && env.options->instructionLimit()) {
    if (perf_fd >= 0) {
      // we could also decide not to guard this read by env.options->instructionLimit(),
      // to get info about instructions burned even when not instruction limiting
      read(perf_fd, &last_instruction_count_read, sizeof(long long));
      
      if (last_instruction_count_read >= MEGA*(long long)env.options->instructionLimit()) {
        Timer::setLimitEnforcement(false);
        if (protectingTimeout) {
          callLimitReachedLater = 2; // 2 for an instr limit
        } else {
          limitReached(2); // 2 for an instr limit
        }
      }
    } else if (perf_fd == -1 && error_to_report) {
      // however, we definitely want this to be guarded by env.options->instructionLimit()
      // not to bother with the error people who don't even know about instruction limiting
      cerr << "perf_event_open failed (instruction limiting will be disabled): " << error_to_report << endl;
      error_to_report = nullptr;
    }
  }
#endif

#if DEBUG_TIMER_CHANGES
  if(timer_sigalrm_counter<0) {
    cout << "Timer value became negative after increase: " << timer_sigalrm_counter <<endl;
    System::terminateImmediately(1);
  }
#endif

}

/** number of miliseconds (of CPU time) passed since some moment */
int Timer::miliseconds()
{
  CALL("Timer::miliseconds");
  ASS_GE(timer_sigalrm_counter, 0);

  return timer_sigalrm_counter;
}

int Timer::guaranteedMilliseconds()
{
  tms aux;
  clock_t ticks=times(&aux);
#if DEBUG_TIMER_CHANGES
  if(ticks==((clock_t)-1)) {
    cout << "clock value -1 returned by times()" <<endl;
    System::terminateImmediately(1);
  }
#endif
  if(ticks==((clock_t)-1)) {
    return -1;
  }
  return static_cast<long long>(ticks)*1000/s_ticksPerSec;
}

void Timer::suspendTimerBeforeFork()
{
  //if we use SIGALRM, we must disable it before forking and the restore it
  //afterwards (in both processes)
  itimerval tv1, tv2;
  tv1.it_value.tv_usec=0;
  tv1.it_value.tv_sec=0;
  tv1.it_interval.tv_usec=0;
  tv1.it_interval.tv_sec=0;
  errno=0;
  int res=setitimer(ITIMER_REAL, &tv1, &tv2);
  if(res!=0) {
    SYSTEM_FAIL("Call to setitimer failed when suspending timer.",errno);
  }
}

void Timer::restoreTimerAfterFork()
{
  itimerval tv1, tv2;
  tv2.it_interval.tv_usec = 1000;
  tv2.it_interval.tv_sec = 0;
  tv2.it_value.tv_usec = 1000;
  tv2.it_value.tv_sec = 0;
  errno=0;
  int res=setitimer(ITIMER_REAL, &tv2, &tv1);
  if(res!=0) {
    SYSTEM_FAIL("Call to setitimer failed when restoring timer.",errno);
  }
}

#ifdef __linux__
// conveniece wrapper around a syscall (cf. https://linux.die.net/man/2/perf_event_open )
long perf_event_open(struct perf_event_attr *hw_event, pid_t pid, int cpu, int group_fd, unsigned long flags)
{
  int ret = syscall(__NR_perf_event_open, hw_event, pid, cpu,group_fd, flags);
  return ret;
}
#endif

void Timer::ensureTimerInitialized()
{
  CALL("Timer::ensureTimerInitialized");
  
  // When ensureTimerInitialized is called, env.options->instructionLimit() will not be set yet,
  // so we do this init unconditionally
  resetInstructionMeasuring();

  if(timer_sigalrm_counter!=-1) {
    return;
  }

  timer_sigalrm_counter=0;

  signal (SIGALRM, timer_sigalrm_handler);
  struct itimerval oldt, newt;
  newt.it_interval.tv_usec = 1000;
  newt.it_interval.tv_sec = 0;
  newt.it_value.tv_usec = 1000;
  newt.it_value.tv_sec = 0;
  setitimer (ITIMER_REAL, &newt, &oldt);

  s_ticksPerSec=sysconf(_SC_CLK_TCK);
  s_initGuarantedMiliseconds=guaranteedMilliseconds();

  Sys::Multiprocessing::instance()->registerForkHandlers(suspendTimerBeforeFork, restoreTimerAfterFork, restoreTimerAfterFork);
}

void Timer::resetInstructionMeasuring()
{
#ifdef __linux__ // if available, initialize the perf reading
  CALL("Timer::resetInstructionMeasuring");

  /*
   * NOTE: we need to do this before initializing the actual timer
   * (otherwise timer_sigalrm_handler could start asking the uninitialized perf_fd!)
   */
  
  last_instruction_count_read = -1;
  error_to_report = nullptr;
  perf_fd = -1;
  
  struct perf_event_attr pe;

  memset(&pe, 0, sizeof(struct perf_event_attr));
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(struct perf_event_attr);
    pe.config = PERF_COUNT_HW_INSTRUCTIONS;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;

  perf_fd = perf_event_open(&pe, 0, -1, -1, 0);
  if (perf_fd == -1) {
    // delay reporting the error until we can check instruction limiting has been actually requested
    error_to_report = std::strerror(errno);
  } else {
    ioctl(perf_fd, PERF_EVENT_IOC_RESET, 0);
    ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0);
  }
#endif
}

bool Timer::instructionLimitingInPlace()
{
#ifdef __linux__
  return (perf_fd >= 0);
#else
  return false;
#endif
}

void Timer::deinitializeTimer()
{
  CALL("Timer::deinitializeTimer");

  itimerval tv1, tv2;
  tv1.it_value.tv_usec=0;
  tv1.it_value.tv_sec=0;
  tv1.it_interval.tv_usec=0;
  tv1.it_interval.tv_sec=0;
  setitimer(ITIMER_REAL, &tv1, &tv2);
  
  signal (SIGALRM, SIG_IGN); // unregister the handler (and ignore the rest of SIGALRMs, should they still come) 
}

void Timer::syncClock()
{
  static bool reportedProblem = false;
  if(s_initGuarantedMiliseconds==-1) {
    //we're unable to sync clock as we weren't able to obtain number of ticks in the beginning
    if(!reportedProblem) {
      reportedProblem = true;
      cerr << "cannot syncronize clock as times() initially returned -1" << endl;
    }
    return;
  }
  int newMilliseconds = guaranteedMilliseconds();
  if(newMilliseconds==-1) {
    //we're unable to sync clock as we cannot get the current time
    if(!reportedProblem) {
      reportedProblem = true;
      cerr << "could not syncronize clock as times() returned -1" << endl;
    }
    return;
  }

  int newVal=newMilliseconds-s_initGuarantedMiliseconds;
  if(abs(newVal-timer_sigalrm_counter)>20) {
    timer_sigalrm_counter=newVal;
  }
}

vstring Timer::msToSecondsString(int ms)
{
  return Int::toString(static_cast<float>(ms)/1000)+" s";
}

/**
 * Print string representing @b ms of milliseconds to @b str
 */
void Timer::printMSString(ostream& str, int ms)
{
  //having the call macro here distorts the stacks printouts
//  CALL("Timer::printMSString");

  if(ms<0) {
    str << '-';
    ms = -ms;
  }

  int sec=ms/1000;
  int msonly=ms%1000;
  if(sec) {
    str<<sec;
  }
  else {
    str<<'0';
  }
  str<<'.';
  if(msonly<100) {
    str<<'0';
    if(msonly<10) {
      str<<'0';
      if(!msonly) {
	str<<'0';
      }
    }
  }
  str<<msonly<<" s";
}

Timer* Timer::instance()
{
  static Timer inst;
  return &inst;

}

TimeoutProtector::TimeoutProtector() {
  protectingTimeout++;
}

TimeoutProtector::~TimeoutProtector() {
  protectingTimeout--;
  if (!protectingTimeout && callLimitReachedLater) {
    unsigned howToCall = callLimitReachedLater;
    callLimitReachedLater = 0; // to prevent recursion (should limitReached itself reach TimeoutProtector)
    limitReached(howToCall);
  }
}

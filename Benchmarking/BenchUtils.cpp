#include "BenchUtils.hpp"

#include "Debug/Assertion.hpp"

#include <iostream>
#include <cstring>
#include <unistd.h>
#include <sys/ioctl.h>
#include <linux/perf_event.h>
#include <asm/unistd.h>
#include <vector>
#include <algorithm>

static unsigned nInstances = 0;
static long long instrOverhead = 0;
static long long totalOverHead = 0;
static int eventFd = -1;
static int pid = -1;

// Helper function for perf_event_open
static long perf_event_open(struct perf_event_attr *hw_event, pid_t pid,
                            int cpu, int group_fd, unsigned long flags) {
    return syscall(__NR_perf_event_open, hw_event, pid, cpu, group_fd, flags);
}

// Function to set up a counter
int setup_perf_event() {
    struct perf_event_attr pe{};
    memset(&pe, 0, sizeof(pe));
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(pe);
    pe.config = PERF_COUNT_HW_INSTRUCTIONS;
    pe.disabled = 1; // Start disabled
    pe.exclude_kernel = 1; // Exclude kernel instructions
    pe.exclude_hv = 1; // Exclude hypervisor instructions

    int fd = perf_event_open(&pe, 0, /*pid*/-1, /*cpu*/-1, 0);
    if (fd == -1) {
        std::cerr << "Error opening perf_event: " << strerror(errno) << std::endl;
    }
    return fd;
}

bench::InstrCounter::InstrCounter() :
  _startCount(-1),
  _totalInstrCount(0),
  _lastOverHead(0)
{
  int currPid = getpid();
  if (currPid != pid) {
    pid = currPid;
    eventFd = setup_perf_event();
  }
  if (nInstances == 0) {
    ioctl(eventFd, PERF_EVENT_IOC_RESET, 0);
    // Calibration of the counting
    // We count the number of instruction it takes to start and stop the counter
    // This is done to minimize the impact of the measuring device on the measurement.
    start();
    stop();
    instrOverhead = getTotalInstrCount();
    reset();
  }
  nInstances++;
}

bench::InstrCounter::~InstrCounter()
{
  nInstances--;
  if (nInstances == 0) {
    close(eventFd);
  }
}

void bench::InstrCounter::reset()
{
  _startCount = -1;
  _totalInstrCount = 0;
}

void bench::InstrCounter::start()
{
  ioctl(eventFd, PERF_EVENT_IOC_DISABLE, 0);
  ASS(!running());
  _lastOverHead = totalOverHead;  // record the last value of the overhead
  totalOverHead += instrOverhead; // record the overhead introduced to other counters
  if (read(eventFd, &_startCount, sizeof(long long)) == -1) {
    std::cerr << "Error reading the instruction counter" << std::endl;
  }
  ioctl(eventFd, PERF_EVENT_IOC_ENABLE, 0);
}

void bench::InstrCounter::stop()
{
  ioctl(eventFd, PERF_EVENT_IOC_DISABLE, 0);
  ASS(running());
  // substract the overhead from all the running instances
  long long endCount = 0;
  read(eventFd, &endCount, sizeof(long long));
  _totalInstrCount += endCount - _startCount;
  _totalInstrCount += _lastOverHead - totalOverHead; // correct the overhead introduced by other counters
  totalOverHead += instrOverhead; // record the overhead introduced to other counters
  _startCount = -1;
  ioctl(eventFd, PERF_EVENT_IOC_ENABLE, 0);
}

void bench::InstrCounter::startAndHold()
{
  ioctl(eventFd, PERF_EVENT_IOC_DISABLE, 0);
  ASS(!running());
  _lastOverHead = totalOverHead;
  totalOverHead += instrOverhead;
  read(eventFd, &_startCount, sizeof(long long));
}

void bench::InstrCounter::stopAndHold()
{
  ioctl(eventFd, PERF_EVENT_IOC_DISABLE, 0);
  ASS(running());
  long long endCount = 0;
  read(eventFd, &endCount, sizeof(long long));
  _totalInstrCount += endCount - _startCount;
  _startCount = -1;

  _totalInstrCount += endCount - _startCount;
  _totalInstrCount += _lastOverHead - totalOverHead; // correct the overhead introduced by other counters
}

void bench::InstrCounter::resume()
{
  ioctl(eventFd, PERF_EVENT_IOC_ENABLE, 0);
}

long long bench::InstrCounter::getTotalInstrCount()
{
  return _totalInstrCount;
}
/**
 * TimeCounter implementation
 */

bench::TimeCounter::TimeCounter()
{}

bench::TimeCounter::~TimeCounter()
{}

void bench::TimeCounter::start()
{
  ASS(_startTime == 0);
  _startTime = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::high_resolution_clock::now().time_since_epoch()).count();
}

void bench::TimeCounter::stop()
{
  ASS(_startTime != 0);
  long long endTime = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::high_resolution_clock::now().time_since_epoch()).count();
  _totalTime += endTime - _startTime;
  _startTime = 0;
}

long long bench::TimeCounter::getTotalTime()
{
  return _totalTime;
}

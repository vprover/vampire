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
static long long innerOverhead = 0;
static long long outerOverhead = 0;
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
    ioctl(fd, PERF_EVENT_IOC_ENABLE, 0);
    return fd;
}

static void calibrate() {
  bench::InstrCounter c0;
  bench::InstrCounter c1;
  // Calibration of the counting
  // We count the number of instruction it takes to start and stop the counter
  // This is done to minimize the impact of the measuring device on the measurement.
  c1.start();
  c0.start();
  c0.stop();
  c1.stop();
  innerOverhead = c0.getTotalInstrCount();
  outerOverhead = c1.getTotalInstrCount() - innerOverhead;
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
    nInstances++;
    ioctl(eventFd, PERF_EVENT_IOC_RESET, 0);

    calibrate();
    // std::cout << "Instruction inner overhead = " << innerOverhead <<std::endl;
    // std::cout << "Instruction outer overhead = " << outerOverhead <<std::endl;
    return;
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
  totalOverHead += outerOverhead; // record the overhead introduced to other counters
  _lastOverHead = totalOverHead;  // record the last value of the overhead
  read(eventFd, &_startCount, sizeof(long long));
}

void bench::InstrCounter::stop()
{
  long long endCount = 0;
  _totalInstrCount += _lastOverHead - totalOverHead; // correct the overhead introduced by other counters
  _totalInstrCount -= innerOverhead;;                // correct the overhead measured by the counter iteself
  read(eventFd, &endCount, sizeof(long long));
  _totalInstrCount += endCount - _startCount;        // increase the counter with the time recorded
  _startCount = -1;
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

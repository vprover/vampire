#ifndef __ScheduleExecutor__
#define __ScheduleExector__

#include <unistd.h>
#include "Schedules.hpp"

#include "Lib/List.hpp"
#include "Lib/PriorityQueue.hpp"
#include "Lib/VString.hpp"
#include "Lib/Set.hpp"

#include "Shell/Property.hpp"

namespace CASC
{
using namespace Lib;

class ProcessPriorityPolicy
{
public:
  virtual float staticPriority(Lib::vstring sliceCode) = 0;
  virtual float dynamicPriority(pid_t pid) = 0;
};

class SliceExecutor
{
public:
  virtual void runSlice(Lib::vstring sliceCode, int terminationTime) NO_RETURN = 0;
};

class Item
{
public:
  Item() : _started(true), _process(-1), _code("") {}
  Item(vstring code)
    : _started(false), _process(-1), _code(code) {}
  Item(pid_t process)
    : _started(true), _process(process), _code("") {}

  bool started() const {return _started;}
  vstring code() const
  {
    ASS(!started());
    return _code;
  }
  pid_t process() const
  {
    ASS(started());
    return _process;
  }

private:
  bool _started;
  pid_t _process;
  vstring _code;
};

class ScheduleExecutor
{
public:
  typedef pair<vstring, int> ProcessInfo;
  typedef List<pid_t> Pool;

  ScheduleExecutor(ProcessPriorityPolicy *policy, SliceExecutor *executor);
  bool run(const Schedule &schedule, int terminationTime, Shell::Property* prop);
  void killAllInPool(Pool**);
  void emptyQueue(PriorityQueue<Item>*);
  void addMutatedProcs(PriorityQueue<Item>*, Shell::Property* prop);

  enum Status {
    NOT_TRAINING = 0,
    FINDING_PROOF = 1,
    LOCAL_SEARCH = 2
  };

private:

  pid_t spawn(Lib::vstring code, int terminationTime);
  unsigned getNumWorkers();
  vstring mutate(vstring optStr, Shell::Property* prop);

  ProcessPriorityPolicy *_policy;
  SliceExecutor *_executor;
  unsigned _numWorkers;
  Status _status;
  ProcessInfo _currentBest;
  Map<pid_t, pair<vstring, int>> _processTimes;
  Set<vstring> triedStrategies;
  Stack<ProcessInfo> _successfulStrats;
  //memory leak here! opts will never be deleted
  Shell::Options* opts;
};
}

#endif

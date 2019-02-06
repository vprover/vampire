#include "ScheduleExecutor.hpp"

#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/System.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

using namespace CASC;
using namespace Lib;
using namespace Lib::Sys;

#define DECI(milli) (milli/100)

ScheduleExecutor::ScheduleExecutor(ProcessPriorityPolicy *policy, SliceExecutor *executor)
  : _policy(policy), _executor(executor)
{
  CALL("ScheduleExecutor::ScheduleExecutor");
  _numWorkers = getNumWorkers();
  _status = (env.options->mode() == Shell::Options::Mode::TRAINING) ? FINDING_PROOF : NOT_TRAINING;
  _currentBest = ProcessInfo("", 1000000000); //arbitrary large value. Need to check that this is large enough
}

bool ScheduleExecutor::run(const Schedule &schedule, int terminationTime, Shell::Property* prop)
{
  CALL("ScheduleExecutor::run");

  PriorityQueue<Item> queue;
  Schedule::BottomFirstIterator it(schedule);

  // insert all strategies into the queue
  while(it.hasNext())
  {
    vstring code = it.next();
    float priority = _policy->staticPriority(code);
    queue.insert(priority, code);
  }

  Pool *pool = Pool::empty();

  bool success = false;
  while(Timer::syncClock(), DECI(env.timer->elapsedMilliseconds()) < terminationTime)
  {
    unsigned poolSize = pool ? Pool::length(pool) : 0;

    // running under capacity, wake up more tasks
    while(poolSize < _numWorkers && !queue.isEmpty())
    {
      Item item = queue.pop();
      pid_t process;
      if(!item.started())
      {
        //cout << "starting item with code " + item.code() << endl;
        process = spawn(item.code(), terminationTime);
        if(_status){
          _processTimes.insert(process, ProcessInfo(item.code(), env.timer->elapsedMilliseconds()));
        }
      }
      else
      {
        process = item.process();
        Multiprocessing::instance()->kill(process, SIGCONT);
      }
      Pool::push(process, pool);
      poolSize++;
    }

    bool stopped, exited;
    int code;
    // sleep until process changes state
    pid_t process = Multiprocessing::instance()
      ->poll_children(stopped, exited, code);

    // child died, remove it from the pool and check if succeeded
    if(exited)
    {
      pool = Pool::remove(process, pool);
      if(!code)
      {
        if(_status){
          ProcessInfo inf = _processTimes.get(process);
          int runningTime = env.timer->elapsedMilliseconds() - inf.second;
          if(runningTime < _currentBest.second){
            //cout << "Current best was " + _currentBest.first + " with time " << _currentBest.second << endl;
            //cout << "Because (" << process << ") found a proof the curren best is " + inf.first + " with time " << runningTime << endl; 
            _currentBest = ProcessInfo(inf.first, runningTime);
            if(_status == FINDING_PROOF){
              _origSucStrat = _currentBest;
            }
            killAllInPool(&pool);
            emptyQueueAndAddMutatedProcs(&queue, prop);
            _status = LOCAL_SEARCH;
          }
        } else {
          success = true;
          goto exit;
        }
      } else if(code != 1){
        cout << "ERROR " << code << endl;
        cout << "The process id is " << process << endl;
        cout << "The process code is " + _processTimes.get(process).first << endl;
      }
    }
    // child stopped, re-insert it in the queue
    else if(stopped)
    {
      pool = Pool::remove(process, pool);
      float priority = _policy->dynamicPriority(process);
      queue.insert(priority, Item(process));
    }

    // pool empty and queue exhausted - we failed
    if(!pool && queue.isEmpty())
    {
      if(_status == LOCAL_SEARCH){
        emptyQueueAndAddMutatedProcs(&queue, prop);
        continue;
      }
      goto exit;
    }
  }

exit:
  if(_status /*&& (env.remainingTime() <= 0)*/){
    env.beginOutput();
    bool out = (_currentBest.first != _origSucStrat.first);
    if(out){
      env.out() << "The first successful strategy found for the problem is " + _origSucStrat.first + 
                 " which found a proof in time " << _origSucStrat.second << endl;
    }
    env.out() << "The best strategy found for the problem is " + _currentBest.first + 
                 " which found a proof in time " << _currentBest.second << endl;
    if(out){
      env.out() << "Training saved " << (_origSucStrat.second - _currentBest.second) << " milliseconds" << endl;             
    }
    env.endOutput();
  } 
  // kill all running processes first
  killAllInPool(&pool);
  return success;
}

void ScheduleExecutor::killAllInPool(Pool** p)
{
  CALL("ScheduleExecutor::killAllInPool");  

  //Pool::DestructiveIterator killIt(*p);
  while(!Pool::isEmpty(*p))
  {
    pid_t process = Pool::pop(*p);
    Multiprocessing::instance()->killNoCheck(process, SIGKILL);
  }
  ASS(*p == 0);
}

void ScheduleExecutor::emptyQueueAndAddMutatedProcs(PriorityQueue<Item>* queue, Shell::Property* prop)
{
  CALL("ScheduleExecutor::emptyQueueAndAddMutatedProcs");  

  while(!queue->isEmpty()){
    queue->pop();
  }

  for(unsigned i = 0; i < getNumWorkers(); i++){
    vstring code = env.options->mutate(_currentBest.first, prop);
    float priority = _policy->staticPriority(code);
    queue->insert(priority, code);         
  }
}

unsigned ScheduleExecutor::getNumWorkers()
{
  CALL("ScheduleExecutor::getNumWorkers");

  unsigned cores = System::getNumberOfCores();
  cores = cores < 1 ? 1 : cores;
  unsigned workers = min(cores, env.options->multicore());
  if(!workers)
  {
    workers = cores >= 8 ? cores - 2 : cores;
  }
  return workers;
}

pid_t ScheduleExecutor::spawn(vstring code, int terminationTime)
{
  CALL("ScheduleExecutor::spawn");

  pid_t pid = Multiprocessing::instance()->fork();
  ASS_NEQ(pid, -1);

  // parent
  if(pid)
  {
    return pid;
  }
  // child
  else
  {
    _executor->runSlice(code, terminationTime);
    ASSERTION_VIOLATION; // should not return
  }
}

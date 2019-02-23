#include "ScheduleExecutor.hpp"

#include "Lib/Array.hpp"
#include "Lib/Random.hpp"
#include "Lib/Environment.hpp"
#include "Lib/System.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

using namespace CASC;
using namespace Lib;
using namespace Lib::Sys;
using namespace Shell;

#define DECI(milli) (milli/100)

ScheduleExecutor::ScheduleExecutor(ProcessPriorityPolicy *policy, SliceExecutor *executor)
  : _policy(policy), _executor(executor)
{
  CALL("ScheduleExecutor::ScheduleExecutor");
  _numWorkers = getNumWorkers();
  _status = (env.options->mode() == Options::Mode::TRAINING) ? FINDING_PROOF : NOT_TRAINING;
  _currentBest = ProcessInfo("", 1000000000); //arbitrary large value. Need to check that this is large enough
  opts = new Options;
}

bool ScheduleExecutor::run(const Schedule &schedule, int terminationTime, Shell::Property* prop)
{
  CALL("ScheduleExecutor::run");

  PriorityQueue<Item> queue;
  PriorityQueue<Item> trainingQueue;
  Schedule::BottomFirstIterator it(schedule);

  unsigned count = 0;
  // insert all strategies into the queue
  while(count++, it.hasNext())
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
    if(_status == LOCAL_SEARCH){
      while(poolSize < _numWorkers && !trainingQueue.isEmpty())
      {
        Item item;
        int randInt = Random::getInteger(8);
        if(randInt < 2 && !queue.isEmpty()){ //for every 6 chosen from trainingQueue, choose 2 from strategy queue
          item = queue.pop();
        } else {
          item = trainingQueue.pop();
        }
      
        ASS(!item.started());
        
        pid_t process = spawn(item.code(), terminationTime);

        ASS(!_processTimes.find(process));
        _processTimes.insert(process, ProcessInfo(item.code(), env.timer->elapsedMilliseconds()));
        
        Pool::push(process, pool);
        poolSize++;
      }
    } else {
      while(poolSize < _numWorkers && !queue.isEmpty())
      {
        Item item = queue.pop();
        //cout << "ABOUT TO START " + item.code() << endl;
        pid_t process;
        if(!item.started())
        {
          process = spawn(item.code(), terminationTime);
          if(_status){
            ASS(!_processTimes.find(process));
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
          inf = ProcessInfo(inf.first, runningTime);
          if(runningTime < _currentBest.second){
            _currentBest = inf;
            //far from ideal, because this will kill non-training strategies as well...
            killAllInPool(&pool);
            emptyQueue(&trainingQueue);
            addMutatedProcs(&trainingQueue, prop);
            _status = LOCAL_SEARCH;
          }
          _successfulStrats.push(inf);
        } else {
          success = true;
          goto exit;
        }
      }
    }
    // child stopped, re-insert it in the queue
    else if(stopped)
    {
      pool = Pool::remove(process, pool);
      float priority = _policy->dynamicPriority(process);
      queue.insert(priority, Item(process));
    }

    if(_status == LOCAL_SEARCH && trainingQueue.isEmpty()){
      addMutatedProcs(&trainingQueue, prop);
    }

    // pool empty and queue exhausted - we failed
    if(!pool && queue.isEmpty() && _status != LOCAL_SEARCH)
    {
      goto exit;
    }
  }

exit:
  if(_status){
    if(_currentBest.first != ""){ success = true; }
    env.beginOutput();
    UIHelper::outputTrainingResult(env.out(), _successfulStrats, _currentBest);
    env.endOutput();
  } 
  // kill all running processes first
  Pool::DestructiveIterator killIt(pool);
  while(killIt.hasNext())
  {
    pid_t process = killIt.next();
    Multiprocessing::instance()->killNoCheck(process, SIGKILL);
  }
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

void ScheduleExecutor::emptyQueue(PriorityQueue<Item>* queue)
{
  CALL("ScheduleExecutor::emptyQueue");  

  while(!queue->isEmpty()){
    queue->pop();
  }
}

void ScheduleExecutor::addMutatedProcs(PriorityQueue<Item>* queue, Shell::Property* prop)
{
  CALL("ScheduleExecutor::emptyQueueAndAddMutatedProcs");  

  while(!queue->isEmpty()){
    queue->pop();
  }

  for(unsigned i = 0; i < getNumWorkers(); i++){
    vstring code = mutate(_currentBest.first, prop);
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


vstring ScheduleExecutor::mutate(vstring optStr, Property* prop)
{
  CALL("Options::mutate");

  ASS(prop);

  //the first call to this function will be made
  //with a successful strategy not already in triedStrategies.
  if(!triedStrategies.contains(optStr)){
    triedStrategies.insert(optStr);
  }

  vstring res = "";

  // whilst doing this don't report any bad options
  Options::BadOption saved_bad_option = env.options->getBadOptionChoice();
  env.options->setBadOptionChoice(Options::BadOption::OFF);

  while(true){
    opts->setAllOptsToDefault();
    opts->readFromEncodedOptions(optStr);
    opts->mutate();
    
    bool valid = opts->checkGlobalOptionConstraints(true);

    if(!valid){ continue; }

    res = opts->generateEncodedOptions();

    if(!triedStrategies.contains(res)){ break; }
  }

  env.options->setBadOptionChoice(saved_bad_option);

  triedStrategies.insert(res);
  return res;
}
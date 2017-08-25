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
 * @file RuntimeStatistics.hpp
 * Defines class RuntimeStatistics.
 */

#ifndef __RuntimeStatistics__
#define __RuntimeStatistics__

/**
If RUNTIME_STATS is defined as 0, runtime statistics are not being
collected nor output.
*/

#ifndef RUNTIME_STATS
#if VDEBUG
#define RUNTIME_STATS 1
#else
#define RUNTIME_STATS 1
#endif
#endif

#define RSTAT_COLLECTION 1

#if RUNTIME_STATS

/**
Defined macros:
RSTAT_CTR_INC(ctr) -- Increases counter named ctr by one
RSTAT_CTR_INC_MANY(ctr,num) -- Increases counter named ctr by @b num
RSTAT_MCTR_INC(ctr, index) -- Increases counter ctr[index] by one. index must be non-negative integer.
RSTAT_MST_INC(stat, index, val) -- Collects integer values @b val in classes @b index to output some simple statistics in the end.
RSTAT_PRINT(stream) -- Outputs current values of counters into stream (typically std::cout)

RSTAT_CTR_INC and RSTAT_MCTR_INC cannot use a counter of the same name

To disable statistics collection from part of the code, add
#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0



Usage:

#include <iostream>
#include "Debug/RuntimeStatistics.hpp"

int main(int argc, char* argv [])
{
  CALL ("main");

  for(int i=0;i<100;i++) {
    if((i*i)%7==1) {
      RSTAT_CTR_INC("numbers with (i*i)%7==1");
    }
    RSTAT_MCTR_INC("square's last digit", (i*i)%10);
  }
  RSTAT_PRINT(std::cout);
}

outputs:
----  Runtime statistics ----
numbers with (i*i)%7==1: 29
square's last digit:
  0: 10
  1: 20
  4: 20
  5: 10
  6: 20
  9: 20
-----------------------------
*/


#include <cstring>
#include <ostream>

#include "Lib/Array.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/SkipList.hpp"

namespace Debug {

using namespace std;
using namespace Lib;

class RSObject
{
public:
  virtual ~RSObject() {};

  CLASS_NAME(RSObject);
  USE_ALLOCATOR_UNK;

  virtual void print(ostream& out) = 0;

  const char* name() { return _name; }
  bool hasName(const char* str) { return !strcmp(str, name()); }
protected:
  RSObject(const char* name) : _name(name) {}

  const char* _name;
};

class RSCounter
: public RSObject
{
public:
  RSCounter(const char* name) : RSObject(name), _counter(0) {}

  void print(ostream& out) { out << name() << ": " << _counter << endl; }
  void inc() { _counter++; }
  void inc(size_t num) { _counter+=num; }
private:
  size_t _counter;
};

class RSMultiCounter
: public RSObject
{
public:
  RSMultiCounter(const char* name) : RSObject(name) {}

  void print(ostream& out);
  void inc(size_t index) { _counters[index]++; }
private:
  ZIArray<size_t> _counters;
};

class RSMultiStatistic
: public RSObject
{
  typedef List<int> ValList;
public:
  RSMultiStatistic(const char* name) : RSObject(name) {}
  ~RSMultiStatistic();

  void print(ostream& out);
  void addRecord(size_t index, int value) { ValList::push(value, _values[index]); }
private:
  ZIArray<ValList* > _values;
};

class RuntimeStatistics
{
public:
  static RuntimeStatistics* instance();

  struct RSObjComparator
  {
    static Comparison compare(const char* name, RSObject* o2)
    {
      int res=strcmp(name, o2->name());
      return (res>0) ? GREATER : ((res==0) ? EQUAL : LESS);
    }
  };

  template<class T>
  T* get(const char* name)
  {
    RSObject** o;
    if (_objs.getPosition(name,o,true)) {
      return static_cast<T*>(*o);
    }
    T* res=new T(name);
    *o = res;
    return res;
  }

  void print(ostream& out);
private:
  RuntimeStatistics();
  ~RuntimeStatistics();

  typedef SkipList<RSObject*,RSObjComparator> ObjSkipList;
  ObjSkipList _objs;
};

#define RSTAT_AUX_NAME__(SEED) _rstat_tmp_##SEED##_
#define RSTAT_AUX_NAME_(SEED) RSTAT_AUX_NAME__(SEED)
#define RSTAT_AUX_NAME RSTAT_AUX_NAME_(__LINE__)

#define RSTAT_CTR_INC(stat) if(RSTAT_COLLECTION) { static Debug::RSCounter* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSCounter>(stat); RSTAT_AUX_NAME->inc(); }
#define RSTAT_CTR_INC_MANY(stat,num) if(RSTAT_COLLECTION) { static Debug::RSCounter* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSCounter>(stat); RSTAT_AUX_NAME->inc(num); }
#define RSTAT_MCTR_INC(stat, index) if(RSTAT_COLLECTION) { static Debug::RSMultiCounter* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSMultiCounter>(stat); RSTAT_AUX_NAME->inc(index); }
#define RSTAT_MST_INC(stat, index, val) if(RSTAT_COLLECTION) { static Debug::RSMultiStatistic* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSMultiStatistic>(stat); RSTAT_AUX_NAME->addRecord(index, val); }

#define RSTAT_PRINT(out) Debug::RuntimeStatistics::instance()->print(out)


}

#else // RUNTIME_STATS

#define RSTAT_CTR_INC(stat)
#define RSTAT_CTR_INC_MANY(stat,num)
#define RSTAT_MCTR_INC(stat, index)
#define RSTAT_MST_INC(stat, index, val)

#define RSTAT_PRINT(out)

#endif

#endif // __RuntimeStatistics__

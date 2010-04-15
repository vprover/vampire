/**
 * @file RuntimeStatistics.hpp
 * Defines class RuntimeStatistics.
 */

#ifndef __RuntimeStatistics__
#define __RuntimeStatistics__

#ifndef NO_RUNTIME_STATS
#define NO_RUNTIME_STATS 0
#endif

#if NO_RUNTIME_STATS

#define RSTAT_CTR_INC(stat)
#define RSTAT_MCTR_INC(stat, index)

#define RSTAT_PRINT(out)

#else

#include <string.h>
#include <ostream>

#include "../Lib/Array.hpp"
#include "../Lib/Allocator.hpp"
#include "../Lib/List.hpp"

namespace Debug {

using namespace std;
using namespace Lib;

class RSObject
{
public:
  virtual ~RSObject() {};

  CLASS_NAME("RSObject");
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

class RuntimeStatistics
{
public:
  static RuntimeStatistics* instance();

  template<class T>
  T* get(const char* name)
  {
    ObjList::Iterator it(_objs);
    while(it.hasNext()) {
      RSObject* o=it.next();
      if(o->hasName(name)) {
	return static_cast<T*>(o);
      }
    }
    T* res=new T(name);
    ObjList::push(res, _objs);
    return res;
  }

  void print(ostream& out);
private:
  RuntimeStatistics();
  ~RuntimeStatistics();

  struct RSObjComparator;

  typedef List<RSObject*> ObjList;
  ObjList* _objs;
};

#define RSTAT_AUX_NAME__(SEED) _rstat_tmp_##SEED##_
#define RSTAT_AUX_NAME_(SEED) RSTAT_AUX_NAME__(SEED)
#define RSTAT_AUX_NAME RSTAT_AUX_NAME_(__LINE__)

#define RSTAT_CTR_INC(stat) static Debug::RSCounter* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSCounter>(stat); RSTAT_AUX_NAME->inc()
#define RSTAT_MCTR_INC(stat, index) static Debug::RSMultiCounter* RSTAT_AUX_NAME = Debug::RuntimeStatistics::instance()->get<Debug::RSMultiCounter>(stat); RSTAT_AUX_NAME->inc(index)

#define RSTAT_PRINT(out) Debug::RuntimeStatistics::instance()->print(out)


}

#endif // else branch of NO_RUNTIME_STATS

#endif // __RuntimeStatistics__

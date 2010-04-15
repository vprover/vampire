/**
 * @file RuntimeStatistics.cpp
 * Implements class RuntimeStatistics.
 */

#include "../Lib/Comparison.hpp"
#include "../Lib/Sort.hpp"
#include "../Lib/Stack.hpp"

#include "RuntimeStatistics.hpp"

#if !NO_RUNTIME_STATS

namespace Debug
{

void RSMultiCounter::print(ostream& out)
{
  out << name() << ":"<< endl;
  for(size_t i=0;i<_counters.size();i++) {
    if(_counters[i]) {
      out << "  " << i << ": " << _counters[i] <<endl;
    }
  }
}


RuntimeStatistics* RuntimeStatistics::instance()
{
  static RuntimeStatistics inst;

  return &inst;
}

RuntimeStatistics::RuntimeStatistics()
: _objs(0)
{
}

RuntimeStatistics::~RuntimeStatistics()
{
  _objs->destroyWithDeletion();
}

struct RuntimeStatistics::RSObjComparator
{
  static Comparison compare(RSObject* o1, RSObject* o2)
  {
    int res=strcmp(o1->name(), o2->name());
    return (res>0) ? GREATER : ((res==0) ? EQUAL : LESS);
  }
};

void RuntimeStatistics::print(ostream& out)
{
  Stack<RSObject*> objStack;
  ObjList::Iterator it(_objs);
  while(it.hasNext()) {
    objStack.push(it.next());
  }
  sort<RSObjComparator>(objStack.begin(), objStack.end());

  out<<"----  Runtime statistics ----"<<endl;

  for(size_t i=0;i<objStack.size();i++) {
    objStack[i]->print(out);
  }
  out<<"-----------------------------"<<endl;
}


}

#endif

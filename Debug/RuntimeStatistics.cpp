/**
 * @file RuntimeStatistics.cpp
 * Implements class RuntimeStatistics.
 */

#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Sort.hpp"
#include "../Lib/Stack.hpp"

#include "RuntimeStatistics.hpp"

#if RUNTIME_STATS

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

RSMultiStatistic::~RSMultiStatistic()
{
  for(size_t i=0;i<_values.size();i++) {
    _values[i]->destroy();
  }
}

void RSMultiStatistic::print(ostream& out)
{
  out << name() << ":"<< endl;
  for(size_t i=0;i<_values.size();i++) {
    if(_values[i]) {

      ValList* vals=_values[i];

      ValList::Iterator vit(vals);
      size_t cnt=0;
      long long int sum=0;
      int min=vals->head();
      int max=vals->head();
      while(vit.hasNext()) {
	int val=vit.next();
	cnt++;
	sum+=val;
	if(val<min) {
	  min=val;
	}
	if(val>max) {
	  max=val;
	}
      }

      string statSum;
      statSum+="cnt: "+Int::toString(cnt)+
	  ", avg: "+Int::toString(static_cast<float>(sum)/cnt)+
	  ", min: "+Int::toString(min)+
	  ", max: "+Int::toString(max);

      out << "  " << i << ": " << statSum << endl;
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

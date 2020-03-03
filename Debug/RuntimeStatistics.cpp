
/*
 * File RuntimeStatistics.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file RuntimeStatistics.cpp
 * Implements class RuntimeStatistics.
 */

#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Stack.hpp"

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
    ValList::destroy(_values[i]);
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
      
      out << "  " << i << ": " << 
              "cnt: "+Int::toString(cnt)+
              ", avg: "+Int::toString(static_cast<float>(sum)/cnt)+
              ", min: "+Int::toString(min)+
              ", max: "+Int::toString(max) << endl;
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
  ObjList::destroyWithDeletion(_objs);
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

  out<<"%----  Runtime statistics ----"<<endl;

  for(size_t i=0;i<objStack.size();i++) {
    objStack[i]->print(out);
  }
  out<<"%-----------------------------"<<endl;
}


}

#endif

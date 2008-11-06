#include <iostream>
#include "Lib/SkipList.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Random.hpp"

using namespace std;
using namespace Lib;

#define LOG(x) cout<<x<<endl

const int cnt=105000;

void print(SkipList<int, Int>& sl)
{
  SkipList<int, Int>::Iterator slit(sl);
  while(slit.hasNext()) {
    cout<<slit.next()<<" ";
  }
  cout<<endl;
}

typedef int StoredType;

StoredType arr[cnt];

void test()
{
  SkipList<StoredType, Int> sl1;
  DHMultiset<StoredType> ms;

  for(int i=0;i<cnt;i++)
  {
    int num=(rand()%cnt)/100;
    ms.insert(num);
    sl1.insert(num);
    arr[i]=num;
  }
  
  Timer tmr;
  tmr.start();
  for(int i=0;i<cnt/2;i++)
  {
    ms.remove(arr[i]);
  }
  tmr.stop();
  LOG("DHMultiset took "<<tmr.elapsedMilliseconds()<<" ms.");

  tmr.reset();
  tmr.start();
  for(int i=0;i<cnt/2;i++)
  {
    sl1.remove(arr[i]);
  }
  tmr.stop();
  LOG("SkipList took "<<tmr.elapsedMilliseconds()<<" ms.");

  return;
  
}

int main()
{
  test();
  return 0;
}

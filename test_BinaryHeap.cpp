#include <iostream>
#include "Lib/BinaryHeap.hpp"
#include "Lib/Int.hpp"

using namespace std;
using namespace Lib;

#define LOG(x) cout<<x<<endl

void test()
{
  BinaryHeap<int, Int> bh;
  
  int cnt=10;
  
  for(int i=0;i<cnt;i++)
  {
    int num=rand()%cnt;
    bh.insert(num);
  }
  
  
  int prev=0;
  while(!bh.isEmpty()) {
    int cur=bh.pop();
    LOG(cur);
    ASS(cur>=prev);
    prev=cur;
  }
  LOG("last was "<<prev);
  
  LOG("done");
}

int main()
{
  test();
  return 0;
}

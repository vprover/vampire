#include <iostream>
#include "Lib/SkipList.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Int.hpp"

using namespace std;
using namespace Lib;

#define LOG(x) cout<<x<<endl

const int cnt=20;

void print(SkipList<int, Int>& sl)
{
  SkipList<int, Int>::Iterator slit(sl);
  while(slit.hasNext()) {
    cout<<slit.next()<<" ";
  }
  cout<<endl;
}

void test()
{
  SkipList<int, Int> sl1;
  SkipList<int, Int> sl2;
  DHMultiset<int> bh;
  int arr[cnt];

  
  for(int i=0;i<cnt;i++)
  {
    int num=rand()%cnt;
    //cout<<"Inserting "<<num<<endl;
    bh.insert(num);
    sl1.insert(num);
    //sl2.insert(num);
    int* pos=0;
    bool res=sl2.getPosition(num,pos,true);
    if(res) {
      pos=sl2.insertPosition(num);
    }
    *pos=num;
    arr[i]=num;
  }
  
  
  SkipList<int, Int>::Iterator slit(sl2);
  while(!bh.isEmpty()) {
    int bhn=bh.pop();
    int sln=sl1.pop();
    ASS(slit.hasNext());
    int sl2n=slit.next();
    ASS(bhn==sln);
    ASS(bhn==sl2n);
  }
  ASS(sl1.isEmpty());
  ASS(!slit.hasNext());
  
  for(int i=0;i<cnt;i++) {
    sl2.remove(arr[i]);
  }
  ASS(sl2.isEmpty());
  
  LOG("done");
}

int main()
{
  test();
  return 0;
}

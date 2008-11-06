#include <iostream>
#include "Lib/DHMultiset.hpp"

using namespace std;
using namespace Lib;

#define LOG(x) cout<<x<<endl

class IdHash {
public:
  static unsigned hash(int i)
  {
    return i;
  }
};

class ConstHash {
public:
  static unsigned hash(int i)
  {
    return 1;
  }
};

typedef DHMultiset<int, ConstHash, IdHash> MySet; 

void test()
{
  MySet m1;

  //cnt has to be even number
  int cnt=100000;
  LOG("testing "<<cnt<<" items..");
  for(int i=0;i<cnt;i++) {
    m1.insert(i);
  }
  LOG("Filled size:"<<m1.size());
  for(int i=0;i<cnt;i++) {
    ASS(m1.find(i));
  }
  ASS(!m1.find(cnt));
  LOG("deleting every odd and adding every even once more..");
  for(int i=1;i<cnt;i+=2) {
    m1.remove(i);
    m1.insert(i-1);
  }
  LOG("Current size:"<<m1.size());
  LOG("checking and removing..");
  for(int i=0;i<cnt;i++) {
    ASS(m1.find(i)==(i%2==0));
  }
  for(int i=0;i<cnt;i+=2) {
    m1.remove(i);
    ASS(m1.find(i));
    m1.remove(i);
    ASS(!m1.find(i));
  }
  LOG("Current size:"<<m1.size());
  
  LOG("done");
}

int main()
{
  test();
  return 0;
}

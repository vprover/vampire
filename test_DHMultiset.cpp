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

//typedef DHMultiset<int, ConstHash, IdHash> MySet;
typedef DHMultiset<int> MySet;

void test()
{
  MySet m1;

  //cnt has to be even number
  int cnt=100000;
  LOG("testing "<<cnt<<" items..");
  for(int i=0;i<cnt;i++) {
    m1.insert(i);
    if(i%1000==0) {
      ASSERT_VALID(m1);
    }
  }
  LOG("Filled size:"<<m1.size());
  for(int i=0;i<cnt;i++) {
    ASS(m1.find(i));
  }
  ASS(!m1.find(cnt));
  ASSERT_VALID(m1);
  LOG("deleting every odd and adding every even once more..");
  for(int i=1;i<cnt;i+=2) {
    m1.remove(i);
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
    m1.insert(i-1);
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
  }
  LOG("Current size:"<<m1.size());
  LOG("checking and removing..");
  for(int i=0;i<cnt;i++) {
    ASS(m1.find(i)==(i%2==0));
  }
  for(int i=0;i<cnt;i+=2) {
    m1.remove(i);
    ASS(m1.find(i));
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
    m1.remove(i);
    ASS(!m1.find(i));
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
  }
  LOG("Current size:"<<m1.size());

  LOG("done");
}

int main()
{
  test();
  return 0;
}

#include <iostream>
#include "Lib/DHMap.hpp"

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

/**
 * Hash class for integers which iterates through
 * {0,1,...,capacity-1} in a zig-zag manner:
 * 
 * E.g. for capacity==3, the transformation is { 0->2,
 * 1->1, 2->0, 3->0, 4->1, 5->2, 6->2,... }
 */
class ZigZagHash {
public:
  /**
   * Hash function for integers which iterates through
   * {0,1,...,capacity-1} in a zig-zag manner:
   * 
   * E.g. for capacity==3, the transformation is { 0->2,
   * 1->1, 2->0, 3->0, 4->1, 5->2, 6->2,... }
   */
  static unsigned hash(int i, int capacity)
  {
    int res=(i%(capacity*2) - capacity);
    if(res<0)
      //this turns x into -x-1
      res = ~res;
    return static_cast<unsigned>(res);
  }
};

namespace Lib 
{
/**
 * Traits structure specialisation. (See DHMap.hpp) 
 */
template<>
struct HashTraits<ZigZagHash>
{
  enum {SINGLE_PARAM_HASH=0};
};
};



typedef DHMap<int, int, ZigZagHash, ConstHash> MyMap; 

void test()
{
  MyMap m1;
  m1.insert(1,1);
  m1.insert(2,4);
  m1.insert(3,9);
  m1.insert(5,25);

  MyMap::Iterator mit(m1);
  LOG("printing 1,2,3,5");
  while(mit.hasNext())
  {
    int k=mit.nextKey();
    int v;
    if(m1.find(k,v))
      cout<<k<<"->"<<v<<endl;
  }
  cout<<m1.find(4)<<m1.find(5)<<endl;

  m1.reset();
  MyMap::Iterator mit2(m1);
  LOG("printing after reset..");
  while(mit2.hasNext())
  {
    int k=mit2.nextKey();
    int v;
    if(m1.find(k,v))
      LOG("->"<<v);
  }
  LOG("done");

  m1.reset();
  m1.reset();

  int cnt=10000;
  LOG("testing "<<cnt<<" items..");
  for(int i=0;i<cnt;i++) {
    m1.insert(i,i*i);
  }
  LOG("Filled size:"<<m1.size());
  for(int i=0;i<cnt;i++) {
    int v;
    bool res=m1.find(i,v);
    ASS(res&&v==i*i);
  }
  ASS(!m1.find(cnt));
  LOG("deleting every odd..");
  for(int i=1;i<cnt;i+=2) {
    m1.remove(i);
  }
  LOG("Current size:"<<m1.size());
  LOG("checking..");
  for(int i=0;i<cnt;i++) {
    int v;
    bool res=m1.find(i,v);
    ASS(res==(i%2==0));
    ASS(!res||v==i*i);
  }
  
  LOG("done");


}

int main()
{
  test();
  return 0;
}

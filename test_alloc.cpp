#include <iostream>
#include "Lib/Allocator.hpp"

using namespace std;

void testVal(unsigned num) {
  cout<<"trying "<<num<<"\n";
  int* c = (int*)ALLOC_UNKNOWN(num, "abcd");
  DEALLOC_UNKNOWN(c,"abcd");
}

int main()
{
  testVal(65491);
  testVal(65492);
  testVal(65493);
  testVal(65494);
  testVal(65495);
  testVal(65496);
  testVal(65497);
  testVal(654970);
  testVal(6549700);
  return 0;
}

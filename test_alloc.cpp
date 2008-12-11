#include <iostream>
#include "Lib/Allocator.hpp"

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
  return 0;
}

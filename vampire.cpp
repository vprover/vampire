#include <iostream>
#include <ostream>

#include <vector>

int distance();


int main(int argc, char* argv[])
{
  std::cout << "running..." << std::endl;
  try { 
    throw 42; 
  } catch(int i) { 
    std::cout << "caught i: " << i  << std::endl;
  } catch(...) { 
    std::cout << "caught unknown " << std::endl;
  }
} // main


int distance()
{
  std::vector<size_t> v(0);
  return 0;
}

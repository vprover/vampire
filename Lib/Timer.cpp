
#include <iostream>
#include "Timer.hpp"

int main (int argc, char* argv [])
{
  int counter = 0;
  Lib::Timer timer;
  int last = -1;
  timer.start();

  for (;;) {
    counter++;
    int current = timer.elapsedDeciseconds();
    if (current <= last) {
      continue;
    }
    last = current;
//      cout << current << "\n";
    if (current == 100) {
      cout << "Total calls to clock() during "
	   << current
	   << " deciseconds is "
	   << counter
	   << '\n';
      return 0;
    }
  }
}

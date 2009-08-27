/**
 * @file Timer.cpp
 * Implements class Timer.
 */

#include <ctime>

#include "Portability.hpp"

#include "Timer.hpp"

using namespace std;

#if COMPILER_MSVC

#include <windows.h>

int Lib::Timer::miliseconds()
{
  static bool init=false;
  static LARGE_INTEGER freq;
  if(!init) {
    ALWAYS(QueryPerformanceFrequency(&freq));
    init=true;
  }

  LARGE_INTEGER counter;
  QueryPerformanceCounter(&counter);

  return counter.QuadPart*1000/freq.QuadPart;
}


#else

#include <sys/time.h>
#include <sys/resource.h>

/** number of miliseconds (of CPU time) passed since some moment */
int Lib::Timer::miliseconds()
{
  struct timeval tim;
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  tim=ru.ru_utime;
  int t=tim.tv_sec*1000 + tim.tv_usec / 1000;
  tim=ru.ru_stime;
  t+=tim.tv_sec*1000 + tim.tv_usec / 1000;
  return t;
//  return (int)( ((long long)clock())*1000/CLOCKS_PER_SEC );
}

#endif

//#include <iostream>
//
//int main (int argc, char* argv [])
//{
//  int counter = 0;
//  Lib::Timer timer;
//  int last = -1;
//  timer.start();
//
//  for (;;) {
//    counter++;
//    int current = timer.elapsedDeciseconds();
//    if (current <= last) {
//      continue;
//    }
//    last = current;
////      cout << current << "\n";
//    if (current == 100) {
//      cout << "Total calls to clock() during "
//	   << current
//	   << " deciseconds is "
//	   << counter
//	   << '\n';
//      return 0;
//    }
//  }
//}
//

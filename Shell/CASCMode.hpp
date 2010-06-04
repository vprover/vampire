/**
 * @file CASCMode.hpp
 * Defines class CASCMode.
 */

#ifndef __CASCMode__
#define __CASCMode__

#include <string>

#include "Forwards.hpp"

namespace Shell {

using namespace std;

class CASCMode {
public:

  static bool perform(int argc, char* argv []);
private:
  CASCMode(string executable);

  bool perform();

  bool runStrategySet(const char** strategies, unsigned ds);
  bool runStrategy(string strategy, unsigned ds);

  unsigned getStrategyTime(string st);

  string _executable;
  string _inputFile;
};

}

#endif // __CASCMode__

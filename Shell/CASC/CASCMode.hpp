/**
 * @file CASCMode.hpp
 * Defines class CASCMode.
 */

#ifndef __CASCMode__
#define __CASCMode__

#include <string>

#include "Forwards.hpp"

#include "Lib/Portability.hpp"

namespace Shell {
namespace CASC
{

using namespace std;

class CASCMode {
public:

  static bool perform(int argc, char* argv []);
protected:
  virtual Property* getProperty() = 0;

  /**
   * Run Vampire with strategy @b strategy for @b ds deciseconds.
   *
   * Return true iff the proof or satisfiability was found
   */
  virtual bool runStrategy(string strategy, unsigned ds) = 0;

  void handleSIGINT() __attribute__((noreturn));

private:
  bool perform();

  bool runStrategySet(const char** strategies, unsigned ds);

  unsigned getStrategyTime(string st);
};

}
}

#endif // __CASCMode__

/**
 * @file CLTBMode.hpp
 * Defines class CLTBMode.
 */

#ifndef __CLTBMode__
#define __CLTBMode__

#include <string>
#include <utility>

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

namespace Shell {
namespace CASC {

using namespace std;
using namespace Lib;

class CLTBMode {
public:
  void perform();
private:
  void readInput();

  typedef Stack<string> StringStack;
  typedef Stack<pair<string,string> > StringPairStack;

  string division;
  int problemTimeLimit;
  int overallTimeLimit;

  StringStack includes;
  /** The first string in the pair is problem file, the second
   * one is output file. The problemFiles[0] is the first
   * problem that should be attempted. */
  StringPairStack problemFiles;
};

}
}

#endif // __CLTBMode__

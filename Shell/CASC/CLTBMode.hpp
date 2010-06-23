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

#include "Shell/SineUtils.hpp"

namespace Shell {
namespace CASC {

using namespace std;
using namespace Lib;

class CLTBMode {
public:
  void perform();
private:
  void readInput();

  void loadIncludes();

  typedef List<string> StringList;
  typedef Stack<string> StringStack;
  typedef pair<string,string> StringPair;
  typedef Stack<StringPair> StringPairStack;

  string division;
  int problemTimeLimit;
  int overallTimeLimit;

  StringList* theoryIncludes;
  /** The first string in the pair is problem file, the second
   * one is output file. The problemFiles[0] is the first
   * problem that should be attempted. */
  StringPairStack problemFiles;

  SineSelector theorySelector;
  UnitList* theoryAxioms;
};

}
}

#endif // __CLTBMode__

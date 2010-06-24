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

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace Shell {
namespace CASC {

using namespace std;
using namespace Lib;

class CLTBProblem;

class CLTBMode
{
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

  SineTheorySelector theorySelector;
  UnitList* theoryAxioms;

  Property property;

  friend class CLTBProblem;
};


class CLTBProblem
{
public:
  CLTBProblem(CLTBMode* parent, string problemFile, string outFile);

  void perform();
private:

  bool runSchedule(const char** sliceCodes, unsigned ds);

  void childRun(Options& opt);

  CLTBMode* parent;
  string problemFile;
  string outFile;

  UnitList* probUnits;
  Property property;

};

}
}

#endif // __CLTBMode__

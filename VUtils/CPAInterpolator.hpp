/**
 * @file CPAInterpolator.hpp
 * Defines class CPAInterpolator.
 */

#ifndef __CPAInterpolator__
#define __CPAInterpolator__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"

namespace VUtils {

using namespace Lib;
using namespace Kernel;


class CPAInterpolator {
public:
  int perform(unsigned argc, char** argv);
private:
  void printUsageAndExit(unsigned argc, char** argv);
  void declareColors();
  void loadFormulas();
  void doProving();
  void displayResult();

  void loadFormula(string fname);

  typedef pair<string,unsigned> FuncSpec;
  typedef DHSet<FuncSpec> FuncSet;
  typedef DHMap<FuncSpec,BaseType*> FuncTypeMap;

  void collectSMTLIBFileFunctions(string fname, FuncSet& acc);


  Stack<string> _leftFNames;
  Stack<string> _rightFNames;

  FuncTypeMap _funcTypes;

  UnitList* _forms;
  UnitList* _defs;
};


}

#endif // __CPAInterpolator__

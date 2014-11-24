/**
 * @file CPAInterpolator.hpp
 * Defines class CPAInterpolator.
 */

#ifndef __CPAInterpolator__
#define __CPAInterpolator__

#include "Forwards.hpp"

#include "Kernel/Problem.hpp"
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

  void loadFormula(vstring fname);

  typedef pair<vstring,unsigned> FuncSpec;
  typedef DHSet<FuncSpec> FuncSet;
  typedef DHMap<FuncSpec,BaseType*> FuncTypeMap;

  void collectSMTLIBFileFunctions(vstring fname, FuncSet& acc);


  Stack<vstring> _leftFNames;
  Stack<vstring> _rightFNames;

  FuncTypeMap _funcTypes;

  Problem _prb;
  UnitList* _forms;
  UnitList* _defs;

private:
  //slicing

  typedef DHSet<vstring> StrategySet;
  typedef Stack<vstring> Schedule;

  bool runSchedule(Schedule& schedule,StrategySet& ss,bool fallback);
  bool runSlice(vstring slice, unsigned ds);
  bool runSlice(Options& opt);
  void childRun(Options& opt);

  bool tryMakeAdmissibleStrategy(Options& opt);

};


}

#endif // __CPAInterpolator__

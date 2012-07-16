/*
 * InvariantHelper.h
 *      Location: Vienna
 */

#ifndef INVARIANTHELPER_H_
#define INVARIANTHELPER_H_

#include <string>
#include "Lib/Set.hpp"
#include "Lib/List.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

namespace Kernel {
  class Term;
  class Unit;
};

using namespace std;
using namespace Lib;
using namespace Kernel;


/*
 * Helper class in order to generate invariants for a while loop
 *
 */
namespace Program
{

class InvariantHelper {
public:
  InvariantHelper(List<Unit*>* un, int timeLim=10):_units(un),_timeLimit(timeLim){};
  virtual ~InvariantHelper();
  void run();
private:
  void setSEIOptions(int timelimit=10);
  void preprocessUnits(Problem& prb);
  Problem* preprocessUnits();
  //void createProblem();
  void runSEI();
  void runVampireSaturationN(Problem& prb);
  void showSignature();
  void showPreprocUnits(Problem *prb);
  int _timeLimit;
  List<Unit*>* _units;
};

}

#endif /* INVARIANTHELPER_H_ */

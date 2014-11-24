/**
 * @file Environment.hpp
 * Defines an Environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#ifndef __Environment__
#define __Environment__

#include <iostream>

#include "Forwards.hpp"
#include "Exception.hpp"

#include "Lib/SmartPtr.hpp"
#include "Shell/OptionsList.hpp"

namespace Lib {

using namespace std;
using namespace Sys;

/**
 * Class Environment.
 * Implements environment used by the top-level run procedures.
 *
 * @since 06/05/2007 Manchester
 */
class Environment
{
public:
  Environment();
  Environment(const Environment& e, Shell::Options& o);
  ~Environment();

  CLASS_NAME(Environment);
  USE_ALLOCATOR(Environment);

  /** options container for all proof attempts */
  Lib::SmartPtr<Shell::OptionsList> optionsList;
  /** currently used sorts */
  Lib::SmartPtr<Kernel::Sorts> sorts;
  /** currently used signature */
  Lib::SmartPtr<Kernel::Signature> signature;
  /** Term sharing structure */
  Lib::SmartPtr<Indexing::TermSharing> sharing;
  /** Currently used timer, this is used by all timers as a global clock */
  Lib::SmartPtr<Timer> timer;


  /** Last read properties */
  Shell::Property* property;
  /** Currently used statistics */
  Shell::Statistics* statistics;
  /** options for the current proof attempt */
  Shell::Options* options;

  bool haveOutput();
  void beginOutput();
  void endOutput();
  ostream& out();

  void setPipeOutput(SyncPipe* pipe);
  SyncPipe* getOutputPipe() { return _pipe; }

  void setPriorityOutput(ostream* stm);
  ostream* getPriorityOutput() { return _priorityOutput; }

  bool timeLimitReached() const;

  void checkTimeLimit() const {
	  if(timeLimitReached()) {
		  throw TimeLimitExceededException();
	  }
  }

  void checkAllTimeLimits() const;

  template<int Period>
  void checkTimeSometime() const
  {
    static int counter=0;
    counter++;
    if(counter==Period) {
      counter=0;
      //if(timeLimitReached()) {
      //  throw TimeLimitExceededException();
      //}
      checkAllTimeLimits();
    }
  }
  /** Time remaining until the end of the time-limit in miliseconds */
  int remainingTime() const;
  /** Currently used ordering */
  Kernel::Ordering* ordering;
  /** set to true when coloring is used for symbol elimination or interpolation */
  bool colorUsed;
  /** set to true when there are some interpreted operations */
  bool interpretedOperationsUsed;

  bool isSingleStrategy() const {
	  return (optionsList -> size() < 2);
  }

private:
  int _outputDepth;
  /** if non-zero, all output will go here */
  ostream* _priorityOutput;
  SyncPipe* _pipe;
}; // class Environment

extern Environment* env;

}

#endif





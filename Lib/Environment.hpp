
/*
 * File Environment.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
#include "DHMap.hpp"

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
  ~Environment();

  /** options for the current proof attempt */
  Shell::Options* options;
  /** currently used sorts */
  Kernel::Sorts* sorts;
  /** currently used signature */
  Kernel::Signature* signature;
  /** Term sharing structure */
  Indexing::TermSharing* sharing;
  /** Currently used statistics */
  Shell::Statistics* statistics;
  /** Last read properties */
  Shell::Property* property;
  /** Currently used timer, this is used by all timers as a global clock */
  Timer* timer;

  DHMap<const Kernel::Unit*,unsigned>* clausePriorities;
  unsigned maxClausePriority;

  DHMap<const Kernel::Unit*,unsigned>* clauseSineLevels;
  DHMap<unsigned, unsigned>* predicateSineLevels;

  bool haveOutput();
  void beginOutput();
  void endOutput();
  ostream& out();

  void setPipeOutput(SyncPipe* pipe);
  SyncPipe* getOutputPipe() { return _pipe; }

  void setPriorityOutput(ostream* stm);
  ostream* getPriorityOutput() { return _priorityOutput; }

  bool timeLimitReached() const;

  template<int Period>
  void checkTimeSometime() const
  {
    static int counter=0;
    counter++;
    if(counter==Period) {
      counter=0;
      if(timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }
  }
  /** Time remaining until the end of the time-limit in miliseconds */
  int remainingTime() const;
  /** set to true when coloring is used for symbol elimination or interpolation */
  bool colorUsed;
  /** set to true when there are some interpreted operations */
  bool interpretedOperationsUsed;

private:
  int _outputDepth;
  /** if non-zero, all output will go here */
  ostream* _priorityOutput;
  SyncPipe* _pipe;
}; // class Environment

extern Environment env;

}

#endif





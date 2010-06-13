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
  /** currently used signature */
  Kernel::Signature* signature;
  /** Term sharing structure */
  Indexing::TermSharing* sharing;
  /** Currently used statistics */
  Shell::Statistics* statistics;
  /** Currently used timer */
  Timer* timer;

  bool haveOutput();
  void beginOutput();
  void endOutput();
  ostream& out();

  void setPipeOutput(SyncPipe* pipe);

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
  /** Currently used ordering */
  Kernel::Ordering* ordering;
  /** set to true when coloring is used for symbol elimination or interpolation */
  bool colorUsed;

private:
  int _outputDepth;
  SyncPipe* _pipe;
}; // class Environment

extern Environment env;

}

#endif





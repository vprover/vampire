/**
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Indexing/TermSharing.hpp"

#include "Kernel/Theory.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#include "Environment.hpp"

namespace Lib
{

using namespace std;
using namespace Kernel;
using namespace Indexing;
using namespace Shell;

#if COMPIT_GENERATOR
struct nullstream:
public std::ostream {
  struct nullbuf: public std::streambuf {
    int overflow(int c) { return traits_type::not_eof(c); }
  } m_sbuf;
  nullstream(): std::ios(&m_sbuf), std::ostream(&m_sbuf) {}
};
nullstream nullStream;
#endif

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : signature(0),
    sharing(0),
    ordering(0),
    colorUsed(false),
    _outputDepth(0),
    _pipe(0)
{
  options=new Options;
  statistics=new Statistics;
  timer=new Timer;
  sharing=new TermSharing;

  timer->start();

  ASS_EQ(Kernel::theory, 0);
  Kernel::theory = Theory::instance();
} // Environment::Environment

Environment::~Environment()
{
  ASS_EQ(_outputDepth,0);

  delete sharing;
  delete timer;
  delete statistics;
  delete options;
}

/**
 * If the global time limit reached set Statistics::terminationReason
 * to TIME_LIMIT and return true, otherwise return false.
 * @since 25/03/2008 Torrevieja
 */
bool Environment::timeLimitReached() const
{
  CALL("ProofAttempt::timeLimitReached");

  if (options->timeLimitInDeciseconds() &&
      timer->elapsedDeciseconds() > options->timeLimitInDeciseconds()) {
    statistics->terminationReason = Shell::Statistics::TIME_LIMIT;
    return true;
  }
  return false;
} // Environment::timeLimitReached


/**
 * Return remaining time in miliseconds.
 */
int Environment::remainingTime() const
{
  return options->timeLimitInDeciseconds()*100 - timer->elapsedMilliseconds();
}

/**
 * Acquire an output stream
 *
 * A process cannot hold an output stream during forking.
 */
void Environment::beginOutput()
{
  CALL("Environment::beginOutput");
  ASS_GE(_outputDepth,0);

  _outputDepth++;
  if(_outputDepth==1 && _pipe) {
    _pipe->acquireWrite();
  }
}

/**
 * Release the output stream
 */
void Environment::endOutput()
{
  CALL("Environment::endOutput");
  ASS_G(_outputDepth,0);

  _outputDepth--;
  if(_outputDepth==0 && _pipe) {
    _pipe->releaseWrite();
  }
}

/**
 * Return true if we have an output stream acquired
 */
bool Environment::haveOutput()
{
  CALL("Environment::haveOutput");

  return _outputDepth;
}

/**
 * Return the output stream if we have it acquired
 *
 * Process must have an output stream acquired in order to call
 * this function.
 */
ostream& Environment::out()
{
  CALL("Environment::out");
  ASS(_outputDepth);

#if COMPIT_GENERATOR
  static nullstream ns;
  return ns;
#else
  if(_pipe) {
    return _pipe->out();
  }
  else {
    return cout;
  }
#endif
}

/**
 * Direct @b env.out() into @b pipe or to @b cout if @b pipe is zero
 *
 * This function cannot be called when an output is in progress.
 */
void Environment::setPipeOutput(SyncPipe* pipe)
{
  CALL("Environment::setPipeOutput");
  ASS(!haveOutput());

  _pipe=pipe;
}

}

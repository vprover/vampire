/**
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "../Debug/Tracer.hpp"

//#include "../Indexing/TermSharing.hpp"
#include "Indexing/TermSharing.hpp"

#include "../Kernel/Theory.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

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
#if COMPIT_GENERATOR// && !VDEBUG
    out(nullStream),
#else
    out(std::cout),
#endif
    sharing(0),
    ordering(0),
    colorUsed(false)
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

}

/**
 * @file Shell/Preprocess.hpp
 * Defines class Preprocess implementing problem preprocessing.
 * @since 05/01/2004 Manchester
 */

#ifndef __Preprocess__
#define __Preprocess__

#include "Kernel/Unit.hpp"
#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

class Property;
class Options;

/**
 * Class implementing preprocessing-related procedures.
 * @since 16/04/2005 Manchester, made non-static
 */
class Preprocess
{
public:
  /** Initialise the preprocessor */
  explicit Preprocess(const Options& options)
    : _options(options)
  {}
  void preprocess(Problem& prb);
#if GNUMP
  void preprocess(ConstraintRCList*& constraints);
#endif

  void preprocess1(Problem& prb);
private:
  void preprocess2(Problem& prb);
  void naming(Problem& prb);
  void secondStageEprPreservingNaming(Problem& prb);
  Unit* preprocess3(Unit* u);
  void preprocess3(Problem& prb);
  void clausify(Problem& prb);

  /** Options used in the normalisation */
  const Options& _options;
#if GNUMP
  void unfoldEqualities(ConstraintRCList*& constraints);
#endif
}; // class Preprocess


}

#endif

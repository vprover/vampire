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
 * @aauthor Andrei Voronkov
 * @since 16/04/2005 Manchester, made non-static
 * @since 02/07/2013 Manchester, _clausify added to support the preprocess mode
 */
class Preprocess
{
public:
  /** Initialise the preprocessor */
  explicit Preprocess(const Options& options)
  : _options(options),
    _clausify(false)
  {}
  void preprocess(Problem& prb);
#if GNUMP
  void preprocess(ConstraintRCList*& constraints);
#endif

  void preprocess1(Problem& prb);
  /** turn off clausification, can be used when only preprocessing without clausification is needed */
  void turnClausifierOff() {_clausify = false;}
private:
  void preprocess2(Problem& prb);
  void naming(Problem& prb);
  void secondStageEprPreservingNaming(Problem& prb);
  Unit* preprocess3(Unit* u);
  void preprocess3(Problem& prb);
  void clausify(Problem& prb);

  /** Options used in the normalisation */
  const Options& _options;
  /** If true, clausification is included in preprocessing */
  bool _clausify;
#if GNUMP
  void unfoldEqualities(ConstraintRCList*& constraints);
#endif
}; // class Preprocess


}

#endif

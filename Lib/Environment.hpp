/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Environment.hpp
 * Defines an Environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#ifndef __Environment__
#define __Environment__

#include "Forwards.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/DArray.hpp"
#include "Lib/ProofExtra.hpp"

namespace Lib {

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

  unsigned char maxSineLevel;

  DHMap<unsigned, unsigned>* predicateSineLevels;

  ProofExtra proofExtra;

  DArray<float> inferenceAgeCorrections; // for each inference rule, what is the age correction of the clause we obtain using that rule?

  /** Time remaining until the end of the time-limit in miliseconds */
  int remainingTime() const;
  /** set to true when coloring is used for symbol elimination or interpolation */
  bool colorUsed;

  /**
   * A global way of accessing "the problem vampire is working on", maily for checking its properties.
   * Note that if in some special cases there is more than one Problem instance used at one time moment,
   * one should know which is the main one and that one should be set/reset here.
   *
   * (In an ideal world, there would be no need for this function, as the correct Problem object would
   * be explicitly passed to all the functions interested in knowning...)
   */
  Kernel::Problem* getMainProblem() { return _problem; }
  void setMainProblem(Kernel::Problem* p) {
    _problem = p;
    _higherOrder = _problem->isHigherOrder();
  }

  bool higherOrder() const {
    return _higherOrder;
  }

  void setHigherOrder(bool value) {
    _higherOrder = value;
  }

private:
  Kernel::Problem* _problem;
  bool _higherOrder;
}; // class Environment

extern Environment env;

}
#endif

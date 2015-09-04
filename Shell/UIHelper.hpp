/**
 * @file UIHelper.hpp
 * Defines class UIHelper.
 */

#ifndef __UIHelper__
#define __UIHelper__

#include <ostream>

#include "Forwards.hpp"
#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class UIHelper {
public:
  static Problem* getInputProblem(const Options& opts);
  static void outputResult(ostream& out);

  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem" or "Unsatisfiable"
   * based on this value.
   */
  static bool haveConjecture() { return s_haveConjecture; }
  static void setConjecturePresence(bool haveConjecture) { s_haveConjecture=haveConjecture; }

  static void outputAllPremises(ostream& out, UnitList* units, vstring prefix="");


  static void outputSatisfiableResult(ostream& out);
  static void outputSaturatedSet(ostream& out, UnitIterator uit);

  static void outputSymbolDeclarations(ostream& out);
  static void outputSymbolTypeDeclarationIfNeeded(ostream& out, bool function, unsigned symNumber);

  static void outputSortDeclarations(ostream& out);

  /**
   * True if we are running in the CASC mode
   *
   * CASC mode means that we will output messages also in the SZS format.
   */
  static bool cascMode;
  /**
   * True if we are running in the CASC mode and we are the child process
   */
  static bool cascModeChild;

  /**
   * Hack not to output satisfiable status twice (we may output it earlier in
   * IGAlgorithm, before we start generating model)
   */
  static bool satisfiableStatusWasAlreadyOutput;
#if GNUMP
  static ConstraintRCList* getInputConstraints(const Options& opts);
  static ConstraintRCList* getPreprocessedConstraints(const ConstraintRCList* inputConstraints);
  static ConstraintRCList* getPreprocessedConstraints(const Options& opts);
  
  static void outputConstraint(const Constraint& constraint, ostream& out, Options::InputSyntax syntax = Options::IS_HUMAN);
  static void outputConstraints(ConstraintList* constraints, ostream& out, Options::InputSyntax syntax=Options::IS_HUMAN);
  
  static void outputAssignment(Assignment& assignemt, ostream& out, Options::InputSyntax syntax=Options::IS_HUMAN);
#endif //GNUMP
  
private:
#if GNUMP
  static void outputConstraintInHumanFormat(const Constraint& constraint, ostream& out);
  static void outputConstraintInSMTFormat(const Constraint& constraint, ostream& out);
#endif //GNUMP

  static bool unitSpecNumberComparator(UnitSpec us1, UnitSpec us2);
  static void addCommentIfCASC(ostream&); 

  static bool s_haveConjecture;
#if VDEBUG
  static bool _inputHasBeenRead;
#endif
  
};

}

#endif // __UIHelper__

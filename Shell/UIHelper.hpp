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

bool outputAllowed(bool debug=false);
bool inSpiderMode();
void reportSpiderFail();
void reportSpiderStatus(char status);

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
   * Hacky global flag indicating that reporting should be done in a Geoff-compliant way.
   * (http://www.cs.miami.edu/~tptp/TPTP/TPTPTParty/2007/PositionStatements/GeoffSutcliffe_SZS.html)
   */
  static bool szsOutput;
  /**
   * A hacky global flag distinguishing the parent and the child in portfolio modes.
   * Currently affects how things are reported during timeout (see Timer.cpp)
   */
  static bool portfolioChild;
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

  static bool unitNumberComparator(Unit* us1, Unit* us2);
  static void addCommentIfCASC(ostream&); 

  static bool s_haveConjecture;
#if VDEBUG
  static bool _inputHasBeenRead;
#endif
  
};

}

#endif // __UIHelper__

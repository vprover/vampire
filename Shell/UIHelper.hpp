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

bool szsOutputMode();
ostream& addCommentSignForSZS(ostream&);
void reportSpiderFail();
void reportSpiderStatus(char status);
bool outputAllowed(bool debug=false);

class UIHelper {
public:
  static UnitList* tryParseTPTP(istream* input);
  static UnitList* tryParseSMTLIB2(const Options& opts,istream* input,SMTLIBLogic& logic);
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
  static bool haveConjectureInProof() { return s_proofHasConjecture; }
  static void setConjectureInProof(bool haveConjectureInProof) { s_proofHasConjecture = haveConjectureInProof; }

  static void outputAllPremises(ostream& out, UnitList* units, vstring prefix="");


  static void outputSatisfiableResult(ostream& out);
  static void outputSaturatedSet(ostream& out, UnitIterator uit);

  static void outputSymbolDeclarations(ostream& out);
  static void outputSymbolTypeDeclarationIfNeeded(ostream& out, bool function, bool typecon, unsigned symNumber);

  static void outputSortDeclarations(ostream& out);//TODO modify all places that call function

  /**
   * A hacky global flag distinguishing the parent and the child in portfolio modes.
   * Currently affects how things are reported during timeout (see Timer.cpp)
   */
  static bool portfolioParent;
  /**
   * Hack not to output satisfiable status twice (we may output it earlier in
   * IGAlgorithm, before we start generating model)
   */
  static bool satisfiableStatusWasAlreadyOutput;

  static void setExpectingSat(){ s_expecting_sat=true; }
  static void setExpectingUnsat(){ s_expecting_unsat=true; }
private:
  static bool s_expecting_sat;
  static bool s_expecting_unsat;

  static bool s_haveConjecture;
  static bool s_proofHasConjecture;
#if VDEBUG
  static bool _inputHasBeenRead;
#endif

};

}

#endif // __UIHelper__

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

#include "Lib/Stack.hpp"

namespace Shell {

using namespace Kernel;

bool szsOutputMode();
std::ostream& addCommentSignForSZS(std::ostream&);
void reportSpiderFail();
void reportSpiderStatus(char status);
bool outputAllowed(bool debug=false);

class UIHelper {
private:
  // a helper class to live on a stack of loaded pieces in interactive metamode
  // (in the standard modes, only a single instance lives on top of _loadedPieces)
  struct LoadedPiece {
    std::string _id;
    UnitList::FIFO _units;
    SMTLIBLogic _smtLibLogic = SMT_UNDEFINED;
    bool _hasConjecture = false;
  };
  static Lib::Stack<LoadedPiece> _loadedPieces;

  static void tryParseTPTP(std::istream& input);
  static void tryParseSMTLIB2(std::istream& input);
public:
  static void parseSingleLine(const std::string& lineToParse, Options::InputSyntax inputSyntax);

  static void parseStream(std::istream& input, Options::InputSyntax inputSyntax, bool verbose, bool preferSMTonAuto);
  static void parseStandardInput(Options::InputSyntax inputSyntax);
  static void parseFile(const std::string& inputFile, Options::InputSyntax inputSyntax, bool verbose);

  static Problem* getInputProblem();

  static void listLoadedPieces(std::ostream& out);
  static void popLoadedPiece(int numPops);

  static void outputResult(std::ostream& out);

  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem"/"ContradictoryAxioms" or "Unsatisfiable"
   * based on this value.
   */
  static bool haveConjecture() { return _loadedPieces.top()._hasConjecture; }

  static void outputAllPremises(std::ostream& out, UnitList* units, std::string prefix="");

  static void outputSatisfiableResult(std::ostream& out);
  static void outputSaturatedSet(std::ostream& out, UnitIterator uit);

  static void outputSymbolDeclarations(std::ostream& out);
  static void outputSymbolTypeDeclarationIfNeeded(std::ostream& out, bool function, bool typecon, unsigned symNumber);

  /**
   * A hacky global flag distinguishing the parent and the child in portfolio modes.
   * Currently affects how things are reported during timeout (see Timer.cpp)
   */
  static bool portfolioParent;
  /**
   * Hack not to output satisfiable status twice (we may output it earlier in
   * FiniteModelBuilder, before we start generating model)
   */
  static bool satisfiableStatusWasAlreadyOutput;

  static void unsetExpecting() { s_expecting_sat = s_expecting_unsat = false; }
  static void setExpectingSat(){ s_expecting_sat=true; }
  static void setExpectingUnsat(){ s_expecting_unsat=true; }

  /** To avoid duplicate Spider outputs, which are are hard to control
   *  in presence of exceptions */
  static bool spiderOutputDone;

private:
  static bool s_expecting_sat;
  static bool s_expecting_unsat;
};

}

#endif // __UIHelper__

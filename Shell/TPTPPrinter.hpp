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
 * @file TPTPPrinter.hpp
 * Defines class TPTPPrinter.
 */

#ifndef __TPTPPrinter__
#define __TPTPPrinter__

#include <iosfwd>

#include "Forwards.hpp"



namespace Shell {

using namespace Kernel;

/**
 * All purpose TPTP printer class. It has two major roles:
 * 1. returns as a TPTP string a Unit/Formula
 * 2. it outputs to the desired output stream any Unit specified
 */
class TPTPPrinter {
public:
  TPTPPrinter(std::ostream* tgtStream=0);

  void print(Unit* u);
  void printAsClaim(std::string name, Unit* u);
  void printWithRole(std::string name, std::string role, Unit* u, bool includeSplitLevels = true);

  static std::string toString(const Unit*);
  static std::string toString(const Formula*);
  static std::string toString(const Term*);
  static std::string toString(const Literal*);

  // if true, headers are not printed again
  bool headersPrinted = false;
private:

  std::string getBodyStr(Unit* u, bool includeSplitLevels);

  void ensureHeadersPrinted(Unit* u);
  void outputSymbolTypeDefinitions(unsigned symNumber, SymbolType symType);

  void ensureNecesarySorts();
  void printTffWrapper(Unit* u, std::string bodyStr);

  std::ostream& tgt();

  /** if zero, we print to std::cout */
  std::ostream* _tgtStream;
};

}

#endif // __TPTPPrinter__

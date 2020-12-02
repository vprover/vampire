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
 * 1. returns as a tptp string a Unit/Formula
 * 2. it outputs to the desired output stream any Unit specified
 */
class TPTPPrinter {
public:
  TPTPPrinter(ostream* tgtStream=0);

  enum SymbolType{FUNC, PRED, TYPE_CON};

  void print(Unit* u);
  void printAsClaim(vstring name, Unit* u);
  void printWithRole(vstring name, vstring role, Unit* u, bool includeSplitLevels = true);

  static vstring toString(const Unit*);
  static vstring toString(const Formula*);
  static vstring toString(const Term*);
  static vstring toString(const Literal*);

private:

  vstring getBodyStr(Unit* u, bool includeSplitLevels);

  void ensureHeadersPrinted(Unit* u);
  void outputSymbolTypeDefinitions(unsigned symNumber, SymbolType symType);

  void ensureNecesarySorts();
  void printTffWrapper(Unit* u, vstring bodyStr);

  void beginOutput();
  void endOutput();
  ostream& tgt();

  /** if zero, we print to env.out() */
  ostream* _tgtStream;

  bool _headersPrinted;
};

}

#endif // __TPTPPrinter__

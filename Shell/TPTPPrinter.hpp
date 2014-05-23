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

  void print(Unit* u);
  void printAsClaim(string name, Unit* u);

  static string toString(const Unit*);
  static string toString(const Formula*);
  static string toString(const Term*);
  static string toString(const Literal*);

private:

  string getBodyStr(Unit* u);

  void ensureHeadersPrinted(Unit* u);
  void outputSymbolTypeDefinitions(unsigned symNumber, bool function);

  void ensureNecesarySorts();
  void printTffWrapper(Unit* u, string bodyStr);

  void beginOutput();
  void endOutput();
  ostream& tgt();

  /** if zero, we print to env -> out() */
  ostream* _tgtStream;

  bool _headersPrinted;
};

}

#endif // __TPTPPrinter__

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

class TPTPPrinter {
public:
  TPTPPrinter(ostream* tgtStream=0);

  void print(Unit* u);
  void printAsClaim(string name, Unit* u);

private:

  string getBodyStr(Unit* u);

  void ensureHeadersPrinted(Unit* u);
  void outputSymbolTypeDefinitions(unsigned symNumber, bool function);

  void ensureNecesarySorts();
  void printTffWrapper(Unit* u, string bodyStr);

  void beginOutput();
  void endOutput();
  ostream& tgt();

  /** if zero, we print to env.out() */
  ostream* _tgtStream;

  bool _headersPrinted;
};

}

#endif // __TPTPPrinter__

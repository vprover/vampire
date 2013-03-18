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

  /** if zero, we print to env.out() */
  ostream* _tgtStream;

  bool _headersPrinted;
};

/**
 * The intended meaning of this class is to print the output invariants in FramaC syntax.
 * This class is not fully implemented. Nor tested
 * TODO framaCPrinter
 */

class FramaCPrinter {

public:
    FramaCPrinter(ostream* tgtStream=0);

    void print(Unit* u);

    void printAsClaim(string name, Unit* u);

private:
      string getBodyString(Unit* u);

      /**
       * This function is intended to replace the classical literal->toString() behaviour.
       * The work is due to the fact that the framaC syntax is diffenent than TPTP
       * param @lit
       * */
      string literalToString(Literal* lit);
      /**
       * This function has similar behaviour as TermLista::argsToString()
       */
      string argsToString(Stack<const TermList*>& stack);
      string termListToString(const TermList tl);
      void printFramaWrapper(Unit* u, string bodyStr);
      void beginOutput();
      void endOutput();
      ostream& tgt();
      /** if zero, we print to env.out()*/
      ostream* _tgtStream;
      bool _headersPrinted;
};


}

#endif // __TPTPPrinter__

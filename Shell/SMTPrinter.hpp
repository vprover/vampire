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
 * @file SMTPrinter.hpp
 * Defines class SMTPrinter.
 * translates Vampire formulas into SMT
 */

#ifndef __SMTPrinter__
#define __SMTPrinter__

#include "Forwards.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Renaming.hpp"

namespace Shell {

using namespace Kernel;

/**
 * All-purpose SMTLIB printer class.
 */
class SMTPrinter {
public:

  SMTPrinter();
  void printTypeDecl(Signature::Symbol *symb, ostream &out);
  void printAsAssertion(Clause* clause, ostream& out, Saturation::Splitter *splitter = nullptr);
private:
  enum class TermFlavour {
    THING,
    PREDICATE,
    SORT,
  };
  void print(Clause* clause, ostream& out, Saturation::Splitter *splitter = nullptr);
  void print(Literal* literal, ostream& out);
  void print(Term* term, ostream& out, TermFlavour flavour);
  void print(Signature::Symbol* symb, ostream& out, bool sort);
  void printVar(unsigned var, ostream &out);

  Renaming _renaming;
};

}

#endif // __SMTPrinter__

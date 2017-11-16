
/*
 * File SMTPrinter.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SMTPrinter.hpp
 * Defines class SMTPrinter.
 * translates Vampire formulas into SMT
 */

#ifndef __SMTPrinter__
#define __SMTPrinter__

#include <iosfwd>

#include "Forwards.hpp"
#include "SineUtils.hpp"


#include "Kernel/Signature.hpp"


namespace Shell {

using namespace Kernel;

/**
 * All purpose SMT printer class. It has two major roles:
 * 1. returns as an SMT  string a Unit/Formula
 * 2. it outputs to the desired output stream any Unit specified
 */
class SMTPrinter {
public:
    
  typedef Signature::Symbol Symbol;
  
  SMTPrinter();
  void smtPrint(Formula* formula, ostream& out);
  void smtPrint(Term* term, ostream& out);
  void smtPrint(Symbol* symb, ostream& out);
  void smtPrintName(const vstring& name, ostream& out);
  void smtPrintSort(const vstring& sortName, ostream& out);  
  void smtPrintDeclaration(Symbol* symb, ostream& out);

private:

  FormulaList* _formulas;
  Set<Symbol*>* _symbols;
  Set<Symbol*>* _predicates;
  bool _getProof;
  bool _smtlib2;
};

}

#endif // __SMTPrinter__

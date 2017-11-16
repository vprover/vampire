
/*
 * File SMTPrinter.cpp.
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
 * @file SMTPrinter.cpp
 * Implements class SMTPrinter.
 * Prints Vampire native format into smtlib1.
 * @author Laura Kovacs 
 * @since 05/07/2013 Gothenburg 
 */

#include <sstream>

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "Parse/TPTP.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"

#include "SMTPrinter.hpp"
#include "Forwards.hpp"

using namespace Shell;
using namespace Indexing;
   
SMTPrinter::SMTPrinter()
  : _formulas(0),
    _symbols(0),
    _predicates(0),
    _getProof(false),
    _smtlib2(false)
{
  CALL("SMTPrinter::SMTPrinter");
}
    
void SMTPrinter::smtPrint(Formula* formula, ostream& out)
{
  CALL("SMTPrinter::smtPrint");
        
  Signature *sig = env.signature;
  unsigned symbNum;
  Symbol* symb;
  TermList* args;
  FormulaList* fs;
  switch (formula->connective()) {
  case LITERAL:
    symbNum = formula->literal()->functor();
    symb = sig->getPredicate(symbNum);
                
    if (formula->literal()->args()->isNonEmpty()) {
      out << "(";
    }
                
    smtPrint(symb, out);
                
    args = formula->literal()->args();
    while (args->isNonEmpty()) {
      out << " ";
      if (args->isVar()) {
	out << "x" << args->var();
      }
      else {
	smtPrint(args->term(), out);
      }
      args = args->next();
    }
                
    if (formula->literal()->args()->isNonEmpty()) {
      out << ")";
    }
    return;
  case AND:
  case OR:
    if (formula->connective() == AND) {
      out << "(and ";
    }
    else {
      out << "(or ";
    }
                
    for (fs = formula->args(); FormulaList::isNonEmpty(fs); fs = fs->tail()) {
      smtPrint(fs->head(), out);
      out << " ";
    }
                
    out << ")";
    return;
  case IMP:
  case IFF:
  case XOR:
    if (formula->connective() == IMP) {
      out << "(implies ";
    }
    else { 
      if (formula->connective() == IFF) {
        out << "(= ";
      } 
      else {
      ASS(false);
      }
    }            
    smtPrint(formula->left(), out);
    out << " ";
    smtPrint(formula->right(), out);
    out << ")";
    return;
  case NOT:
    out << "(not ";
    smtPrint(formula->uarg(), out);
    out << ")";
    return;
  case FORALL:
    return;
  case EXISTS:
    return;
  case BOOL_TERM:
    smtPrint(formula->getBooleanTerm().term(), out);
  case TRUE:
    out << "true";
    return;
  case FALSE:
    out << "false";
    return;
  default:
    out << "WARNING!!! This is not a literal\n";
    ASS(false);
    return;
  }
}
    
/*print terms in SMT format*/    
void SMTPrinter::smtPrint(Term* term, ostream& out)
{
  Signature *sig = env.signature;
  unsigned int symbNum = term->functor();
  Symbol* symb = sig->getFunction(symbNum);
        
  if (term->args()->isNonEmpty()) {
    out << "(";
  }
        
  smtPrint(symb, out);
        
  TermList* args = term->args();
  while (args->isNonEmpty()) {
    out << " ";
    if (args->isVar()) {
      out << "x" << args->var();
    }
    else {
      smtPrint(args->term(), out);
    }
    args = args->next();
  }
        
  if (term->args()->isNonEmpty()) {
    out << ")";
  }
}
    
/*print symbols in SMT*/
void SMTPrinter::smtPrint(Symbol* symb, ostream& out)
{
  vstring name = symb->name();
   if (symb->interpreted()) {
    if (name == "$less") {
      out << "<";
      return;
    }
    if (name == "$lesseq") {
      out << "<=";
      return;
    }
    if (name == "$greater") {
      out << ">";
      return;
    }
    if (name == "$greatereq") {
      out << ">=";
      return;
    }
    if (name == "=") {
      out << "=";
      return;
    }
    if (name == "$plus") {
      out << "+";
      return;
    }
    if (name == "$sum") {
      out << "+";
      return;
    }
    if (name == "$times") {
      out << "*";
      return;
    }
    if (name == "$product") {
      out << "*"; 
      return;
    }
    if (name == "$uminus") {
      out << "-";
      return;
    }
    if (name == "$divide") {
      out << "div";
      return;
    }
    /* it is not an interpreted arithmetic predicate/function with non-zero arity, but it is an interpreted theory symbol, e.g. constant 0*/
    out << name; 
  }
  else {
    /*the symbol is uninterpreted*/
   out<<name;
   return;
 }
}
    
    

/**
 * @file SMTPrinter.cpp
 * Implements class SMTPrinter.
 */

#include <sstream>

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
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
                
    if (formula->literal()->args()->isNonEmpty())
      out << "(";
                
    smtPrint(symb, out);
                
    args = formula->literal()->args();
    while(args->isNonEmpty()) {
      out << " ";
      if (args->isVar())
	out << "x" << args->var();
      else
	smtPrint(args->term(), out);
      args = args->next();
    }
                
    if (formula->literal()->args()->isNonEmpty())
      out << ")";
                
    return;
  case AND:
  case OR:
    if (formula->connective() == AND) {
      out << "(and ";
    }
    else {
      out << "(or ";
    }
                
    for(fs = formula->args(); fs->isNonEmpty (); fs = fs->tail()) {
      smtPrint(fs->head(), out);
      out << " ";
    }
                
    out << ")";
    return;
  case IMP:
  case IFF:
  case XOR:
    if (formula->connective() == IMP)
      out << "(implies ";
    else if (formula->connective() == IFF)
      out << "(= ";
    else
      ASS(false);
                
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
    
    
    
/*print terms in SMT*/    
void SMTPrinter::smtPrint(Term* term, ostream& out)
{
  Signature *sig = env.signature;
  unsigned int symbNum = term->functor();
  Symbol* symb = sig->getFunction(symbNum);
        
  if (term->args()->isNonEmpty())
    out << "(";
        
  smtPrint(symb, out);
        
  TermList* args = term->args();
  while(args->isNonEmpty()) {
    out << " ";
    if (args->isVar())
      out << "x" << args->var();
    else
      smtPrint(args->term(), out);
    args = args->next();
  }
        
  if (term->args()->isNonEmpty())
    out << ")";
}
    
/*print symbols in SMT*/
//TODO: use builtin enumerator for builtin operators instead of this trick...
//unfortunately I only discovered about those later..
void SMTPrinter::smtPrint(Symbol* symb, ostream& out)
{
  string name = symb->name();
  if (symb->interpreted()) {
    if (name == "$less")
      {out << "<";}
    else if (name == "$lesseq")
      {out << "<=";}
    else if (name == "$greater")
      {out << ">";}
    else if (name == "$greatereq")
      {out << ">=";}
    else if (name == "=")
      {out << "=";}
    else if (name == "$plus")
      {out << "+";}
    else if (name == "$sum")
      {out << "+";}
    else if (name == "$times")
      {out << "*";}
    else if (name == "$product")
      {out << "*";}
    else if (name == "$uminus")
      {out << "-";}
    else 
      {out << name;} //TODO: handle negative number and print them as (- N)
  }
  else{out<<name;}
}
    
    



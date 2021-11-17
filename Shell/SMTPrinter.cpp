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
 * @file SMTPrinter.cpp
 * Implements class SMTPrinter.
 * Routines for printing Vampire objects as SMTLIB
 * @author Laura Kovacs 
 * @since 05/07/2013 Gothenburg 
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/SharedSet.hpp"
#include "Saturation/Splitter.hpp"

#include "SMTPrinter.hpp"

using namespace Shell;

SMTPrinter::SMTPrinter()
{
  CALL("SMTPrinter::SMTPrinter");
}

/*print symbol type in SMT format*/
void SMTPrinter::printTypeDecl(Signature::Symbol *symb, ostream &out)
{
  CALL("SMTPrinter::printTypeDecl");
  if(symb->interpreted())
    return;

  const vstring &name = symb->name();

  // built-in types are not required
  if(name == "$i" || name == "$o" || name == "$tType" || name == "$int" || name == "$rat" || name == "$real")
    return;

  auto type = symb->fnType();
  unsigned arity = type->arity();
  auto ret = type->result().term();

  // special-case (declare-nat Nat zero s p Sub)
  // Rapid-specific, a bit gross
  // TODO: look at this again if/when Rapid support is merged
  const char *nat = "'Nat()'";
  if(name == nat) {
    out << "(declare-nat Nat zero s p Sub)" << std::endl;
    return;
  }
  // avoid re-definitions
  else if(
    // zero
    (name == "zero" && arity == 0 && ret->functionName() == nat) ||
    // s
    (name == "s" && arity == 1 && ret->functionName() == nat) ||
    // p
    (name == "p" && arity == 1 && ret->functionName() == nat) ||
    // Sub
    (name == "'Sub'" && arity == 2
      && type->arg(0).term()->functionName() == nat
      && type->arg(1).term()->functionName() == nat
    )
  )
    return;

  if(ret->functionName() == "$tType") {
    out << "(declare-sort ";
    print(symb, out, true);
    out << " " << arity << ")" << std::endl;
    return;
  }

  // TODO: if/when Rapid features get merged, enable this
  if(symb->isLemmaPredicate)
    out << "(declare-lemma-predicate ";
  else
  if(arity == 0)
    out << "(declare-const ";
  else
    out << "(declare-fun ";

  print(symb, out, false);
  out << " ";
  if(arity != 0)
    out << "(";

  for(unsigned i = 0; i < arity; i++) {
    if(i > 0)
      out << " ";
    print(type->arg(i).term(), out, TermFlavour::SORT);
  }

  if(arity != 0)
    out << ") ";

  print(ret, out, TermFlavour::SORT);
  out << ")";
  out << std::endl;
}

/*print clause in SMT format*/
void SMTPrinter::printAsAssertion(Clause *cl, ostream& out, Saturation::Splitter *splitter)
{
  CALL("SMTPrinter::printAsAssertion(Clause *, ostream &)");

  out << "(assert ";
  print(cl, out, splitter);
  out << ")" << std::endl;
}

/*print clause in SMT format*/
void SMTPrinter::print(Clause *cl, ostream& out, Saturation::Splitter *splitter)
{
  CALL("SMTPrinter::print(Clause *, ostream &)");

  bool splits = splitter && !cl->noSplits();
  if(splits) {
    out << "(=>";

    SplitSet::Iterator lengthit(*cl->splits());
    unsigned num_splits = 0;
    while(lengthit.hasNext()) { lengthit.next(); num_splits++; }
    if(num_splits > 1)
      out << " (and";

    SplitSet::Iterator sit(*cl->splits());
    while(sit.hasNext()) {
      SplitLevel split = sit.next();
      out << " ";
      Clause *compCl = splitter->getComponentClause(split);
      print(compCl, out);
    }

    if(num_splits > 1)
      out << ")";

    out << " ";
  }

  typedef DHMap<unsigned,TermList> SortMap;
  SortMap varSorts;
  SortHelper::collectVariableSorts(static_cast<Unit *>(cl), varSorts);
  SortMap::Iterator vit(varSorts);
  bool quantified = vit.hasNext();

  if(quantified) {
    _renaming.reset();
    out << "(forall (";
    bool separate = false;
    while(vit.hasNext()) {
      unsigned var;
      TermList varSort;
      vit.next(var, varSort);

      if(separate)
        out << " ";
      out << "(";
      printVar(var, out);
      out << " ";
      print(varSort.term(), out, TermFlavour::SORT);
      out << ")";
      separate = true;
    }
    out << ") ";
  }

  if(cl->isEmpty()) {
    out << "false" << std::endl;
  }
  else {
    if(cl->length() > 1)
      out << "(or ";
    for(int i = 0; i < cl->length(); i++) {
      if(i > 0)
        out << " ";
      print(cl->literals()[i], out);
    }
    if(cl->length() > 1)
      out << ")";
  }

  if(quantified)
    out << ")";

  if(splits)
    out << ")";
}

/*print literals in SMT format*/
void SMTPrinter::print(Literal *l, ostream& out)
{
  CALL("SMTPrinter::print(Literal *, ostream &)");

  if(!l->polarity())
    out << "(not ";
  print(static_cast<Term *>(l), out, TermFlavour::PREDICATE);
  if(!l->polarity())
    out << ")";
}

/*print terms in SMT format*/    
void SMTPrinter::print(Term* term, ostream& out, TermFlavour flavour)
{
  CALL("SMTPrinter::print(Term *, ostream &)");

  unsigned int functor = term->functor();
  Signature::Symbol *sym = nullptr;
  switch(flavour) {
  case TermFlavour::THING:
    sym = env.signature->getFunction(functor);
    break;
  case TermFlavour::PREDICATE:
    sym = env.signature->getPredicate(functor);
    break;
  case TermFlavour::SORT:
    sym = env.signature->getFunction(functor);
    break;
  }

  if (term->args()->isNonEmpty())
    out << "(";

  print(sym, out, flavour == TermFlavour::SORT);
  TermList* args = term->args();
  while (args->isNonEmpty()) {
    out << " ";
    if (args->isVar()) {
      printVar(args->var(), out);
    }
    else {
      auto childFlavour = flavour == TermFlavour::SORT ? flavour : TermFlavour::THING;
      print(args->term(), out, childFlavour);
    }
    args = args->next();
  }
        
  if (term->args()->isNonEmpty())
    out << ")";
}
    
/*print symbols in SMT*/
void SMTPrinter::print(Signature::Symbol* sym, ostream& out, bool sort)
{
  CALL("SMTPrinter::print(Symbol *, ostream &)");
  if(sort) {
    const vstring &name = sym->name();
    if(name == "$int")
      out << "Int";
    else if(name == "$real")
      out << "Real";
    else if(name == "$o")
      out << "Bool";
    // Rapid-specific types
    else if(name == "'Nat()'")
      out << "Nat";
    else if(name == "'Time()'")
      out << "Time";
    else if(name == "'Trace()'")
      out << "Trace";
    else
      out << name;
  }
  else if(sym->integerConstant() || sym->realConstant()) {
    const vstring &name = sym->name();
    if(name[0] == '-')
      out << "(- " << name.substr(1) << ")";
    else
      out << name;
  }
  else if(sym->interpreted()) {
    auto interpreted = static_cast<Signature::InterpretedSymbol *>(sym);
    const char *interpretation = nullptr;
    switch(interpreted->getInterpretation()) {
    case Interpretation::EQUAL:
      interpretation = "=";
      break;
    case Interpretation::INT_LESS:
    case Interpretation::REAL_LESS:
      interpretation = "<";
      break;
    case Interpretation::INT_LESS_EQUAL:
    case Interpretation::REAL_LESS_EQUAL:
      interpretation = "<=";
      break;
    case Interpretation::INT_GREATER_EQUAL:
    case Interpretation::REAL_GREATER_EQUAL:
      interpretation = ">=";
      break;
    case Interpretation::INT_GREATER:
    case Interpretation::REAL_GREATER:
      interpretation = ">";
      break;
    case Interpretation::INT_UNARY_MINUS:
    case Interpretation::REAL_UNARY_MINUS:
    case Interpretation::INT_MINUS:
    case Interpretation::REAL_MINUS:
      interpretation = "-";
      break;
    case Interpretation::INT_PLUS:
    case Interpretation::REAL_PLUS:
      interpretation = "+";
      break;
    case Interpretation::INT_MULTIPLY:
    case Interpretation::REAL_MULTIPLY:
      interpretation = "*";
      break;
    case Interpretation::INT_QUOTIENT_E:
      interpretation = "div";
      break;
    case Interpretation::REAL_QUOTIENT:
      interpretation = "/";
      break;
    case Interpretation::INT_REMAINDER_E:
      interpretation = "mod";
      break;
    case Interpretation::INT_ABS:
      interpretation = "abs";
      break;
    case Interpretation::INT_TO_REAL:
      interpretation = "to_real";
      break;
    case Interpretation::REAL_TO_INT:
      interpretation = "to_int";
      break;
    case Interpretation::REAL_IS_INT:
      interpretation = "is_int";
      break;
    case Interpretation::ARRAY_SELECT:
    case Interpretation::ARRAY_BOOL_SELECT:
      interpretation = "select";
      break;
    case Interpretation::ARRAY_STORE:
      interpretation = "store";
      break;
    // stuff SMTLIB doesn't have
    case Interpretation::INT_IS_INT:
    case Interpretation::INT_IS_RAT:
    case Interpretation::INT_IS_REAL:
    case Interpretation::REAL_IS_RAT:
    case Interpretation::REAL_IS_REAL:
    case Interpretation::INT_DIVIDES:
    case Interpretation::INT_SUCCESSOR:
    case Interpretation::INT_QUOTIENT_F:
    case Interpretation::INT_QUOTIENT_T:
    case Interpretation::INT_REMAINDER_F:
    case Interpretation::INT_REMAINDER_T:
    case Interpretation::INT_FLOOR:
    case Interpretation::INT_CEILING:
    case Interpretation::INT_TRUNCATE:
    case Interpretation::INT_ROUND:
    case Interpretation::REAL_FLOOR:
    case Interpretation::REAL_CEILING:
    case Interpretation::REAL_TRUNCATE:
    case Interpretation::REAL_ROUND:
    case Interpretation::REAL_QUOTIENT_E:
    case Interpretation::REAL_QUOTIENT_F:
    case Interpretation::REAL_QUOTIENT_T:
    case Interpretation::REAL_REMAINDER_E:
    case Interpretation::REAL_REMAINDER_F:
    case Interpretation::REAL_REMAINDER_T:
    case Interpretation::INT_TO_INT:
    case Interpretation::REAL_TO_REAL:
    // no rationals in SMTLIB (yet?)
    case Interpretation::RAT_IS_INT:
    case Interpretation::RAT_IS_RAT:
    case Interpretation::RAT_IS_REAL:
    case Interpretation::RAT_GREATER:
    case Interpretation::RAT_GREATER_EQUAL:
    case Interpretation::RAT_LESS:
    case Interpretation::RAT_LESS_EQUAL:
    case Interpretation::RAT_UNARY_MINUS:
    case Interpretation::RAT_PLUS:
    case Interpretation::RAT_MINUS:
    case Interpretation::RAT_MULTIPLY:
    case Interpretation::RAT_QUOTIENT:
    case Interpretation::RAT_QUOTIENT_E:
    case Interpretation::RAT_QUOTIENT_T:
    case Interpretation::RAT_QUOTIENT_F:
    case Interpretation::RAT_REMAINDER_E:
    case Interpretation::RAT_REMAINDER_T:
    case Interpretation::RAT_REMAINDER_F:
    case Interpretation::RAT_FLOOR:
    case Interpretation::RAT_CEILING:
    case Interpretation::RAT_TRUNCATE:
    case Interpretation::RAT_ROUND:
    case Interpretation::INT_TO_RAT:
    case Interpretation::REAL_TO_RAT:
    case Interpretation::RAT_TO_INT:
    case Interpretation::RAT_TO_RAT:
    case Interpretation::RAT_TO_REAL:
    // invalid
    case Interpretation::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION_REP(interpreted->name());
    }

    out << interpretation;
  }
  // avoid clashing when reading the generated file in again
  // e.g. sK0 becomes sK0X
  else if(sym->introduced()) {
    out << sym->name() + 'X';
  }
  else {
    out << sym->name();
  }
}

/*print variables in SMT*/
void SMTPrinter::printVar(unsigned var, ostream& out) {
  CALL("SMTPrinter::printVar");
  var = _renaming.getOrBind(var);
  out << "x" << var;
}
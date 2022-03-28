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
 * @file TPTPPrinter.cpp
 * Implements class TPTPPrinter.
 */

#include <sstream>

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "Parse/TPTP.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"

#include "Shell/Statistics.hpp"

#include "TPTPPrinter.hpp"

#include "Forwards.hpp"

namespace Shell
{
TPTPPrinter::TPTPPrinter(ostream* tgtStream)
: _tgtStream(tgtStream), _headersPrinted(false)
{
  CALL("TPTPPrinter::TPTPPrinter");
}

/**
 * Print the Unit @param u to the desired output
 */
void TPTPPrinter::print(Unit* u)
{
  CALL("TPTPPrinter::print");

  vstring body = getBodyStr(u, true);

  beginOutput();
  ensureHeadersPrinted(u);
  printTffWrapper(u, body);
  endOutput();
}

/**
 * Print on the desired output the Unit with the specified name
 * @param name
 * @param u
 */
void TPTPPrinter::printAsClaim(vstring name, Unit* u)
{
  CALL("TPTPPrinter::printAsClaim");
  printWithRole(name, "claim", u);
}

void TPTPPrinter::printWithRole(vstring name, vstring role, Unit* u, bool includeSplitLevels)
{
  CALL("TPTPPrinter::printWithRole");

  vstring body = getBodyStr(u, includeSplitLevels);

  beginOutput();
  ensureHeadersPrinted(u);
  tgt() << "tff(" << name << ", " << role << ", " << body << ")." << endl;
  endOutput();
}

/**
 * Return as a vstring the body of the Unit u
 * @param u
 * @param includeSplitLevels
 * @return the body vstring
 */
vstring TPTPPrinter::getBodyStr(Unit* u, bool includeSplitLevels)
{
  CALL("TPTPPrinter::getBodyStr");

  vostringstream res;

  typedef DHMap<unsigned,TermList> SortMap;
  static SortMap varSorts;
  varSorts.reset();
  SortHelper::collectVariableSorts(u, varSorts);

  if(u->isClause()) {
    SortMap::Iterator vit(varSorts);
    bool quantified = vit.hasNext();
    if(quantified) {
      res << "![";
      while(vit.hasNext()) {
        unsigned var;
        TermList varSort;
        vit.next(var, varSort);

        res << 'X' << var;
        if(varSort!= AtomicSort::defaultSort()) {
          res << " : " << varSort.toString();
        }
        if(vit.hasNext()) {
          res << ',';
        }
      }
      res << "]: (";
    }

    Clause* cl = static_cast<Clause*>(u);
    Clause::Iterator cit(*cl);
    if(!cit.hasNext()) {
      res << "$false";
    }
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      res << lit->toString();
      if(cit.hasNext()) {
        res << " | ";
      }
    }

    if(quantified) {
      res << ')';
    }

    if(includeSplitLevels && !cl->noSplits()) {
      SplitSet::Iterator sit(*cl->splits());
      while(sit.hasNext()) {
        SplitLevel split = sit.next();
        res << " | " << "$splitLevel" << split;
      }
    }
  }
  else {
    return static_cast<FormulaUnit*>(u)->formula()->toString();
  }
  return res.str();
}

/**
 * Surround by tff() the body of the unit u
 * @param u
 * @param bodyStr
 */
void TPTPPrinter::printTffWrapper(Unit* u, vstring bodyStr)
{
  CALL("TPTPPrinter::printTffWrapper");

  tgt() << "tff(";
  vstring unitName;
  if(Parse::TPTP::findAxiomName(u, unitName)) {
    tgt() << unitName;
  }
  else {
    tgt() << "u_" << u->number();
  }
  tgt() << ", ";
  switch(u->inputType()) {
  case UnitInputType::AXIOM:
    tgt() << "axiom"; break;
  case UnitInputType::ASSUMPTION:
    tgt() << "hypothesis"; break;
  case UnitInputType::CONJECTURE:
    tgt() << "conjecture"; break;
  case UnitInputType::NEGATED_CONJECTURE:
    tgt() << "negated_conjecture"; break;
  case UnitInputType::CLAIM:
    tgt() << "claim"; break;
  case UnitInputType::EXTENSIONALITY_AXIOM:
    tgt() << "extensionality"; break;
  default:
     ASSERTION_VIOLATION;
  }
  tgt() << ", " << endl << "    " << bodyStr << " )." << endl;
}

/**
 * Output the symbol definition
 * @param symNumber
 * @param function - true if the symbol is a function symbol
 */
void TPTPPrinter::outputSymbolTypeDefinitions(unsigned symNumber, SymbolType symType)
{
  CALL("TPTPPrinter::outputSymbolTypeDefinitions");

  Signature::Symbol* sym;
  OperatorType* type;
  if(symType == SymbolType::FUNC){
    sym = env.signature->getFunction(symNumber);
    type = sym->fnType();
  } else if(symType == SymbolType::PRED){
    sym = env.signature->getPredicate(symNumber);
    type = sym->predType();    
  } else {
    sym = env.signature->getTypeCon(symNumber);
    type = sym->typeConType();
  }

  if(type->isAllDefault()) {
    return;
  }

  bool func = symType == SymbolType::FUNC ;
  if(func && theory->isInterpretedConstant(symNumber)) { return; }

  if (func && sym->overflownConstant()) { return; }

  if(sym->interpreted()) {
    Interpretation interp = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch(interp) {
    case Theory::INT_SUCCESSOR:
    case Theory::INT_ABS:
    case Theory::INT_DIVIDES:
      //for interpreted symbols that do not belong to TPTP standard we still have to output sort
      break;
    default:
      return;
    }
  }

  vstring cat = "tff(";
  if(env.property->higherOrder()){
    cat = "thf(";
  }

  vstring st = "func";
  if(symType == SymbolType::PRED){
    st = "pred"; 
  } else if(symType == SymbolType::TYPE_CON){
    st = "sort";
  }

  tgt() << cat << st << "_def_" << symNumber << ",type, "
      << sym->name() << ": ";

  tgt() <<  type->toString();

  tgt() << " )." << endl;
}

/**
 * Print only the necessary headers for the sorts. This is needed in order to avoid
 * having in the TPTP problem sorts that are not used
 * @since 08/10/2012, Vienna
 * @author Ioan Dragan
 */
/*void TPTPPrinter::ensureNecesarySorts()
{
  CALL("TPTPPrinter::ensureNecesarySorts");
  if (_headersPrinted) {
    return;
  }
  unsigned i;
  List<TermList> *_usedSorts(0);
  OperatorType* type;
  Signature::Symbol* sym;
  unsigned sorts = env.sorts->count();
  //check the sorts of the function symbols and collect information about used sorts
  for (i = 0; i < env.signature->functions(); i++) {
    if(env.signature->isTypeConOrSup(f)){ continue; }
    sym = env.signature->getFunction(i);
    type = sym->fnType();
    unsigned arity = sym->arity();
    // NOTE: for function types, the last entry (i.e., type->arg(arity)) contains the type of the result
    for (unsigned i = 0; i <= arity; i++) {
      if(! List<unsigned>::member(type->arg(i), _usedSorts))
        List<unsigned>::push(type->arg(i), _usedSorts);
    }
  }
  //check the sorts of the predicates and collect information about used sorts
  for (i = 0; i < env.signature->predicates(); i++) {
    sym = env.signature->getPredicate(i);
    type = sym->predType();
    unsigned arity = sym->arity();
    if (arity > 0) {
      for (unsigned i = 0; i < arity; i++) {
        if(! List<unsigned>::member(type->arg(i), _usedSorts))
          List<unsigned>::push(type->arg(i), _usedSorts);
      }
    }
  }
  //output the sort definition for the used sorts, but not for the built-in sorts
  for (i = Sorts::FIRST_USER_SORT; i < sorts; i++) {
    if (List<unsigned>::member(i, _usedSorts))
      tgt() << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i)
            	      << ": $tType" << " )." << endl;

  }
} */ //TODO fix this function. At te moment, not sure how important it is

/**
 * Makes sure that only the needed headers in the @param u are printed out on the output
 */
void TPTPPrinter::ensureHeadersPrinted(Unit* u)
{
  CALL("TPTPPrinter::ensureHeadersPrinted");

  if(_headersPrinted) {
    return;
  }
  
  //ensureNecesarySorts();

  unsigned typeCons = env.signature->typeCons();
  for(unsigned i=Signature::FIRST_USER_CON; i<typeCons; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::TYPE_CON);
  }
  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::FUNC);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::PRED);
  }

  _headersPrinted = true;
}

/**
 * Retrieve the output stream to which vampire prints out
 */
ostream& TPTPPrinter::tgt()
{
  CALL("TPTPPrinter::tgt");

  if(_tgtStream) {
    return *_tgtStream;
  }
  else {
    return env.out();
  }
}

/**
 * In case there is no specified output stream, than print to the one
 * specified in the env.beginOutput();
 */
void TPTPPrinter::beginOutput()
{
  CALL("TPTPPrinter::beginOutput");

  if(!_tgtStream) { env.beginOutput(); }
}

void TPTPPrinter::endOutput()
{
  CALL("TPTPPrinter::endOutput");

  if(!_tgtStream) { env.endOutput(); }
}

/**
 * Return the vstring representing the formula f.
 */
vstring TPTPPrinter::toString(const Formula* formula)
{
  CALL("TPTPPrinter::toString(const Formula*)");
  static vstring names [] =
    { "", " & ", " | ", " => ", " <=> ", " <~> ",
      "~", "!", "?", "$term", "$false", "$true", "", ""};
  ASS_EQ(sizeof(names)/sizeof(vstring), NOCONN+1);

  vstring res;

  // render a connective if specified, and then a Formula (or ")" of formula is nullptr)
  typedef pair<Connective,const Formula*> Todo;
  Stack<Todo> stack;

  stack.push(make_pair(NOCONN,formula));

  while (stack.isNonEmpty()) {
    Todo todo = stack.pop();

    // in any case start by rendering the connective passed from "above"
    res += names[todo.first];

    const Formula* f = todo.second;

    if (!f) {
      res += ")";
      continue;
    }

    Connective c = f->connective();

    switch (c) {
    case LITERAL: {
      vstring result = f->literal()->toString();
      if (f->literal()->isEquality()) {
        res += "(" + result + ")";
      } else {
        res += result;
      }
      continue;
    }
    case AND:
    case OR:
      {
        // we will reverse the order
        // but that should not matter

        const FormulaList* fs = f->args();
        res += "(";
        stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket
        while (FormulaList::isNonEmpty(fs)) {
          const Formula* arg = fs->head();
          fs = fs->tail();
          // the last argument, which will be printed first, is the only one not preceded by a rendering of con
          stack.push(make_pair(FormulaList::isNonEmpty(fs) ? c : NOCONN,arg));
        }

        continue;
      }
    case IMP:
    case IFF:
    case XOR:
      // here we can afford to keep the order right

      res += "(";

      stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket

      stack.push(make_pair(c,f->right())); // second argument with con

      stack.push(make_pair(NOCONN,f->left())); // first argument without con

      continue;

    case NOT:
      res += "(";

      stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket

      stack.push(make_pair(c,f->uarg()));

      continue;

    case FORALL:
    case EXISTS:
      {
        vstring result = vstring("(") + names[c] + "[";
        bool needsComma = false;
        VList::Iterator vs(f->vars());
        SList::Iterator ss(f->sorts());
        bool hasSorts = f->sorts();

        while (vs.hasNext()) {
          unsigned var = vs.next();

          if (needsComma) {
            result += ", ";
          }
          result += 'X';
          result += Int::toString(var);
          TermList t;
          if (hasSorts) {
            ASS(ss.hasNext());
            t = ss.next();
            if (t != AtomicSort::defaultSort()) {
              result += " : " + t.toString();
            }
          } else if (SortHelper::tryGetVariableSort(var, const_cast<Formula*>(f),
              t) && t != AtomicSort::defaultSort()) {
            result += " : " + t.toString();
          }
          needsComma = true;
        }
        res += result + "] : (";

        stack.push(make_pair(NOCONN,nullptr));
        stack.push(make_pair(NOCONN,nullptr)); // here we close two brackets

        stack.push(make_pair(NOCONN,f->qarg()));

        continue;
      }

    case BOOL_TERM:
      res += f->getBooleanTerm().toString();

      continue;

    case FALSE:
    case TRUE:
      res += names[c];

      continue;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return res;
}

/**
 * Output unit @param unit in TPTP format as a vstring
 *
 * If the unit is a formula of type @b CONJECTURE, output the
 * negation of Vampire's internal representation with the
 * TPTP role conjecture. If it is a clause, just output it as
 * is, with the role negated_conjecture.
 */
vstring TPTPPrinter::toString (const Unit* unit)
{
  CALL("TPTPPrinter::toString(const Unit*)");
//  const Inference* inf = unit->inference();
//  Inference::Rule rule = inf->rule();

  vstring prefix;
  vstring main = "";

  bool negate_formula = false;
  vstring kind;
  switch (unit->inputType()) {
  case UnitInputType::ASSUMPTION:
    kind = "hypothesis";
    break;

  case UnitInputType::CONJECTURE:
    if(unit->isClause()) {
      kind = "negated_conjecture";
    }
    else {
      negate_formula = true;
      kind = "conjecture";
    }
    break;

  case UnitInputType::EXTENSIONALITY_AXIOM:
    kind = "extensionality";
    break;

  case UnitInputType::NEGATED_CONJECTURE:
    kind = "negated_conjecture";
    break;

  default:
    kind = "axiom";
    break;
  }

  if (unit->isClause()) {
    prefix = "cnf";
    main = static_cast<const Clause*>(unit)->toTPTPString();
  }
  else {
    prefix = "tff";
    const Formula* f = static_cast<const FormulaUnit*>(unit)->formula();
    if(negate_formula) {
      Formula* quant=Formula::quantify(const_cast<Formula*>(f));
      if(quant->connective()==NOT) {
	ASS_EQ(quant, f);
	main = toString(quant->uarg());
      }
      else if(quant->connective()==LITERAL && quant->literal()->isNegative()){
        ASS_EQ(quant,f);
        Literal* comp = Literal::complementaryLiteral(quant->literal());
        main = comp->toString();
      }
      else {
	Formula* neg=new NegatedFormula(quant);
	main = toString(neg);
	neg->destroy();
      }
      if(quant!=f) {
	ASS_EQ(quant->connective(),FORALL);
        VList::destroy(static_cast<QuantifiedFormula*>(quant)->vars());
	quant->destroy();
      }
    }
    else {
      main = toString(f);
    }
  }

  vstring unitName;
  if(!Parse::TPTP::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }

  return prefix + "(" + unitName + "," + kind + ",\n"
    + "    " + main + ").\n";
}


vstring TPTPPrinter::toString(const Term* t){
  NOT_IMPLEMENTED;
}

vstring TPTPPrinter::toString(const Literal* l){
  NOT_IMPLEMENTED;
}

}

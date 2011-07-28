/**
 * @file TPTPPrinter.cpp
 * Implements class TPTPPrinter.
 */

#include <sstream>

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "Parse/TPTP.hpp"

#include "TPTPPrinter.hpp"

namespace Shell
{
TPTPPrinter::TPTPPrinter(ostream* tgtStream)
: _tgtStream(tgtStream), _headersPrinted(false)
{
  CALL("TPTPPrinter::TPTPPrinter");
}

void TPTPPrinter::print(Unit* u)
{
  CALL("TPTPPrinter::print");

  string body = getBodyStr(u);

  beginOutput();
  ensureHeadersPrinted(u);
  printTffWrapper(u, body);
  endOutput();
}

void TPTPPrinter::printAsClaim(string name, Unit* u)
{
  string body = getBodyStr(u);

  beginOutput();

  ensureHeadersPrinted(u);

  tgt() << "tff(" << name << ", claim, " << body << ")." << endl;

  endOutput();
}

string TPTPPrinter::getBodyStr(Unit* u)
{
  CALL("TPTPPrinter::getBodyStr");

  stringstream res;

  typedef DHMap<unsigned,unsigned> SortMap;
  static SortMap varSorts;
  varSorts.reset();
  SortHelper::collectVariableSorts(u, varSorts);

  if(u->isClause()) {
    SortMap::Iterator vit(varSorts);
    bool quantified = vit.hasNext();
    if(quantified) {
      res << "![";
      while(vit.hasNext()) {
	unsigned var, varSort;
	vit.next(var, varSort);

	res << 'X' << var;
	if(varSort!=Sorts::SRT_DEFAULT) {
	  res << " : " << env.sorts->sortName(varSort);
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

    if(!cl->noProp()) {
      res << " | " << BDD::instance()->toTPTPString(cl->prop());
    }
    if(!cl->noSplits()) {
      SplitSet::Iterator sit(cl->splits());
      while(sit.hasNext()) {
	SplitLevel split = sit.next();
	res << " | " << "$splitLevel" << split;
      }
    }
  }
  else {
    NOT_IMPLEMENTED;
  }
  return res.str();
}

void TPTPPrinter::printTffWrapper(Unit* u, string bodyStr)
{
  CALL("TPTPPrinter::printTffWrapper");

  tgt() << "tff(";
  string unitName;
  if(Parse::TPTP::findAxiomName(u, unitName)) {
    tgt() << unitName;
  }
  else {
    tgt() << "u_" << u->number();
  }
  tgt() << ", ";
  switch(u->inputType()) {
  case Unit::AXIOM:
    tgt() << "axiom"; break;
  case Unit::ASSUMPTION:
    tgt() << "hypothesis"; break;
  case Unit::CONJECTURE:
    tgt() << "conjecture"; break;
  case Unit::NEGATED_CONJECTURE:
    tgt() << "negated_conjecture"; break;
  case Unit::CLAIM:
    tgt() << "claim"; break;
  }
  tgt() << ", " << endl << "    " << bodyStr << " )." << endl;
}

void TPTPPrinter::outputSymbolTypeDefinitions(unsigned symNumber, bool function)
{
  CALL("TPTPPrinter::outputSymbolTypeDefinitions");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);
  BaseType* type = function ? static_cast<BaseType*>(sym->fnType()) : sym->predType();

  if(type->isAllDefault()) {
    return;
  }
  if(function && theory->isInterpretedConstant(symNumber)) { return; }

  if(sym->interpreted()) {
    Interpretation interp = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch(interp) {
    case Theory::INT_SUCCESSOR:
    case Theory::INT_DIVIDE:
    case Theory::RAT_DIVIDE:
    case Theory::REAL_DIVIDE:
      //for interpreted symbols that do not belong to TPTP standard we still have to output sort
      break;
    default:
      return;
    }
  }

  tgt() << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ",type, "
      << sym->name() << ": ";

  unsigned arity = sym->arity();
  if(arity>0) {
    tgt() << "(";
    for(unsigned i=0; i<arity; i++) {
      if(i>0) {
	tgt() << " * ";
      }
      tgt() << env.sorts->sortName(type->arg(i));
    }
    tgt() << ") > ";
  }
  if(function) {
    tgt() << env.sorts->sortName(sym->fnType()->result());
  }
  else {
    tgt() << "$o";
  }
  tgt() << " )." << endl;
}


void TPTPPrinter::ensureHeadersPrinted(Unit* u)
{
  CALL("TPTPPrinter::ensureHeadersPrinted");

  if(_headersPrinted) {
    return;
  }

  //TODO: print only necessary headers
  unsigned sorts = env.sorts->sorts();
  for(unsigned i=Sorts::FIRST_USER_SORT; i<sorts; i++) {
    tgt() << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i) << ": $tType" << " )." << endl;
  }


  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(i, true);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(i, false);
  }

  _headersPrinted = true;
}

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


}

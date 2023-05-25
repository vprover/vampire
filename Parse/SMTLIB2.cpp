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
 * @file SMTLIB.cpp
 * Implements class SMTLIB.
 */

#include <climits>
#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/NameArray.hpp"
#include "Lib/StringUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"

#include "Shell/LispLexer.hpp"
#include "Shell/Options.hpp"
#include "Shell/SMTLIBLogic.hpp"
#include "Shell/TermAlgebra.hpp"

#include "SMTLIB2.hpp"

#include "TPTP.hpp"

#undef LOGGING
#define LOGGING 0

#if LOGGING
#define LOG1(arg) cout << arg << endl;
#define LOG2(a1,a2) cout << a1 << a2 << endl;
#define LOG3(a1,a2,a3) cout << a1 << a2 << a3 << endl;
#define LOG4(a1,a2,a3,a4) cout << a1 << a2 << a3 << a4 << endl;
#else
#define LOG1(arg)
#define LOG2(a1,a2)
#define LOG3(a1,a2,a3)
#define LOG4(a1,a2,a3,a4)
#endif

#define USER_ERROR_EXPR(msg) USER_ERROR(vstring(msg)+" in top-level expression '"+_topLevelExpr->toString()+"'")

namespace Parse {

static const char* PAR = "par";
static const char* TYPECON_POSTFIX = "()";

SMTLIB2::SMTLIB2(const Options& opts)
: _logicSet(false),
  _logic(SMT_UNDEFINED),
  _numeralsAreReal(false),
  _formulas(nullptr),
  _topLevelExpr(nullptr)
{
  CALL("SMTLIB2::SMTLIB2");
}

void SMTLIB2::parse(istream& str)
{
  CALL("SMTLIB2::parse(istream&)");

  LispLexer lex(str);
  LispParser lpar(lex);
  LExpr* expr = lpar.parse();
  parse(expr);
}

void SMTLIB2::parse(LExpr* bench)
{
  CALL("SMTLIB2::parse(LExpr*)");

  ASS(bench->isList());
  readBenchmark(bench->list);
}

void SMTLIB2::readBenchmark(LExprList* bench)
{
  CALL("SMTLIB2::readBenchmark");
  LispListReader bRdr(bench);

  bool afterCheckSat = false;

  // iteration over benchmark top level entries
  while(bRdr.hasNext()) {
    LExpr* lexp = bRdr.next();
    _topLevelExpr = lexp;
    _nextVar = 0;

    LOG2("readBenchmark ",lexp->toString(true));

    LispListReader ibRdr(lexp);

    if (ibRdr.tryAcceptAtom("set-logic")) {
      if (_logicSet) {
        USER_ERROR_EXPR("set-logic can appear only once in a problem");
      }
      readLogic(ibRdr.readAtom());
      ibRdr.acceptEOL();
      continue;
    }

    if (ibRdr.tryAcceptAtom("set-info")) {

      if (ibRdr.tryAcceptAtom(":status")) {
        _statusStr = ibRdr.readAtom();
        ibRdr.acceptEOL();
        continue;
      }

      if (ibRdr.tryAcceptAtom(":source")) {
        _sourceInfo = ibRdr.readAtom();
        ibRdr.acceptEOL();
        continue;
      }

      // ignore unknown info
      ibRdr.readAtom();
      ibRdr.readAtom();
      ibRdr.acceptEOL();
      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-sort")) {
      vstring name = ibRdr.readAtom();
      vstring arity;
      if (!ibRdr.tryReadAtom(arity)) {
        USER_ERROR_EXPR("Unspecified arity while declaring sort: "+name);
      }

      readDeclareSort(name,arity);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-sort")) {
      vstring name = ibRdr.readAtom();
      LExprList* args = ibRdr.readList();

      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("define-sort expects a sort definition body");
      }
      LExpr* body = ibRdr.readNext();

      readDefineSort(name,args,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-fun")) {
      vstring name = ibRdr.readAtom();
      LExprList* iSorts = ibRdr.readList();
      LispListReader iSortRdr(iSorts);
      auto lookup = new TermLookup();
      _scopes.push(lookup);
      if (iSortRdr.hasNext() && iSortRdr.peekAtNext()->isAtom() && iSortRdr.peekAtNext()->str == PAR) {
        ibRdr.acceptEOL();
        iSortRdr.readAtom(); // the "par" atom
        readTypeParameters(iSortRdr, lookup);
        iSorts = iSortRdr.readList();
        ibRdr = iSortRdr;
      }
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("declare-fun expects an output sort");
      }
      LExpr* oSort = ibRdr.readNext();

      readDeclareFun(name,iSorts,oSort,lookup->size());

      ibRdr.acceptEOL();
      delete _scopes.pop();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-datatype")) {
      LExpr *sort = ibRdr.readNext();
      LExprList *datatype = ibRdr.readList();

      readDeclareDatatype(sort, datatype);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-datatypes")) {
      LExprList* sorts = ibRdr.readList();
      LExprList* datatypes = ibRdr.readList();

      readDeclareDatatypes(sorts, datatypes, false);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-codatatypes")) {
      LExprList* sorts = ibRdr.readList();
      LExprList* datatypes = ibRdr.readList();

      readDeclareDatatypes(sorts, datatypes, true);

      ibRdr.acceptEOL();

      continue;
    }
    
    if (ibRdr.tryAcceptAtom("declare-const")) {
      vstring name = ibRdr.readAtom();
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("declare-const expects a const definition body");
      }
      LExpr* oSort = ibRdr.readNext();
      auto lookup = new TermLookup();
      _scopes.push(lookup);
      if (oSort->isList()) {
        LispListReader oSortRdr(oSort);
        if (oSortRdr.hasNext() && oSortRdr.peekAtNext()->isAtom() && oSortRdr.peekAtNext()->str == PAR) {
          ibRdr.acceptEOL();
          oSortRdr.readAtom(); // the "par" atom
          readTypeParameters(oSortRdr, lookup);
          oSort = oSortRdr.readNext();
          ibRdr = oSortRdr;
        }
      }

      readDeclareFun(name,nullptr,oSort,lookup->size());

      ibRdr.acceptEOL();
      delete _scopes.pop();

      continue;
    }

    bool recursive = false;
    if (ibRdr.tryAcceptAtom("define-fun") || (recursive = ibRdr.tryAcceptAtom("define-fun-rec"))) {
      vstring name = ibRdr.readAtom();
      LExprList* iArgs = ibRdr.readList();
      LispListReader iArgRdr(iArgs);
      auto lookup = new TermLookup();
      TermStack typeArgs;
      _scopes.push(lookup);
      if (iArgRdr.hasNext() && iArgRdr.peekAtNext()->isAtom() && iArgRdr.peekAtNext()->str == PAR) {
        ibRdr.acceptEOL();
        iArgRdr.readAtom(); // the "par" atom
        readTypeParameters(iArgRdr, lookup, &typeArgs);
        iArgs = iArgRdr.readList();
        ibRdr = iArgRdr;
      }
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("define-fun expects an output sort");
      }
      LExpr* oSort = ibRdr.readNext();
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("define-fun expects a fun definition body");
      }
      LExpr* body = ibRdr.readNext();

      readDefineFun(name,iArgs,oSort,body,typeArgs,recursive);

      ibRdr.acceptEOL();
      delete _scopes.pop();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert")) {
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("assert expects a body");
      }
      LExpr* body = ibRdr.readNext();
      readAssert(body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-not")) {
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("assert-not expects a body");
      }
      LExpr* body = ibRdr.readNext();
      readAssertNot(body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-theory")) {
      if (!ibRdr.hasNext()) {
        USER_ERROR_EXPR("assert-theory expects a body");
      }
      LExpr* body = ibRdr.readNext();
      readAssertTheory(body);

      ibRdr.acceptEOL();

      continue;
    }

    // not an official SMTLIB command
    if (ibRdr.tryAcceptAtom("color-symbol")) {
      vstring symbol = ibRdr.readAtom();

      if (ibRdr.tryAcceptAtom(":left")) {
        colorSymbol(symbol, Color::COLOR_LEFT);
      } else if (ibRdr.tryAcceptAtom(":right")) {
        colorSymbol(symbol, Color::COLOR_RIGHT);
      } else {
        USER_ERROR_EXPR("'"+ibRdr.readAtom()+"' is not a color keyword");
      }

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("check-sat")) {
      ibRdr.acceptEOL();
      afterCheckSat = true;
      break;
    }

    if (ibRdr.tryAcceptAtom("exit")) {
      bRdr.acceptEOL();
      break;
    }

    if (ibRdr.tryAcceptAtom("reset")) {
      LOG1("ignoring reset");
      continue;
    }

    if (ibRdr.tryAcceptAtom("set-option")) {
      LOG2("ignoring set-option", ibRdr.readAtom());
      continue;
    }

    if (ibRdr.tryAcceptAtom("push")) {
      LOG1("ignoring push");
      continue;
    }

    if (ibRdr.tryAcceptAtom("get-info")) {
      LOG2("ignoring get-info", ibRdr.readAtom());
      continue;
    }

    USER_ERROR_EXPR("unrecognized entry "+ibRdr.readAtom());
  }
  
  // the above while loop is aborted on the first check-sat,
  // however, we want to learn about an unsat core printing request
  // (or other things we might support in the future)
  if (afterCheckSat) {
    while(bRdr.hasNext()) {
      LispListReader ibRdr(bRdr.next());
      
      if (ibRdr.tryAcceptAtom("exit")) {
        ibRdr.acceptEOL(); // no arguments of exit
        bRdr.acceptEOL();  // exit should be the last thing in the file
        break;
      }
      
      if (ibRdr.tryAcceptAtom("get-unsat-core")) {
        env.options->setOutputMode(Options::Output::UCORE);
        ibRdr.acceptEOL(); // no arguments of get-unsat-core
        continue;
      }
      
      // can't read anything else (and it does not make sense to read get-unsat-core more than once)
      // so let's just warn and exit
      if(env.options->mode()!=Options::Mode::SPIDER) {
        env.beginOutput();
        env.out() << "% Warning: check-sat is not the last entry. Skipping the rest!" << endl;
        env.endOutput();
      }
      break;
    }
  }
}

//  ----------------------------------------------------------------------

const char * SMTLIB2::s_smtlibLogicNameStrings[] = {
    "ALIA",
    "ALL",
    "ANIA",
    "AUFDTLIA",
    "AUFDTLIRA",
    "AUFDTNIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIA",
    "AUFNIRA",
    "BV",
    "LIA",
    "LRA",
    "NIA",
    "NRA",
    "QF_ABV",
    "QF_ALIA",
    "QF_ANIA",
    "QF_AUFBV",
    "QF_AUFLIA",
    "QF_AUFNIA",
    "QF_AX",
    "QF_BV",
    "QF_IDL",
    "QF_LIA",
    "QF_LIRA",
    "QF_LRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_RDL",
    "QF_UF",
    "QF_UFBV",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNIA",
    "QF_UFNRA",
    "UF",
    "UFBV",
    "UFDT",
    "UFDTLIA",
    "UFDTLIRA",
    "UFDTNIA",
    "UFDTNIRA",
    "UFIDL",
    "UFLIA",
    "UFLRA",
    "UFNIA"
};

SMTLIBLogic SMTLIB2::getLogicFromString(const vstring& str)
{
  CALL("SMTLIB2::getLogicFromString");

  static NameArray smtlibLogicNames(s_smtlibLogicNameStrings, sizeof(s_smtlibLogicNameStrings)/sizeof(char*));
  ASS_EQ(smtlibLogicNames.length, SMT_UNDEFINED);

  int res = smtlibLogicNames.tryToFind(str.c_str());
  if(res==-1) {
    return SMT_UNDEFINED;
  }
  return static_cast<SMTLIBLogic>(res);
}

void SMTLIB2::readLogic(const vstring& logicStr)
{
  CALL("SMTLIB2::checkLogic");

  _logic = getLogicFromString(logicStr);
  _logicSet = true;

  switch (_logic) {
  case SMT_ALL:
  case SMT_ALIA:
  case SMT_ANIA:
  case SMT_AUFDTLIA:
  case SMT_AUFDTLIRA:
  case SMT_AUFDTNIRA:
  case SMT_AUFLIA:
  case SMT_AUFNIA:
  case SMT_AUFLIRA:
  case SMT_AUFNIRA:
  case SMT_LIA:
  case SMT_NIA:
  case SMT_QF_ALIA:
  case SMT_QF_ANIA:
  case SMT_QF_AUFLIA:
  case SMT_QF_AUFNIA:
  case SMT_QF_AX:
  case SMT_QF_IDL:
  case SMT_QF_LIA:
  case SMT_QF_LIRA:
  case SMT_QF_NIA:
  case SMT_QF_NIRA:
  case SMT_QF_UF:
  case SMT_QF_UFIDL:
  case SMT_QF_UFLIA:
  case SMT_QF_UFNIA:
  case SMT_UF:
  case SMT_UFDT:
  case SMT_UFDTLIA:
  case SMT_UFDTLIRA:
  case SMT_UFDTNIA:
  case SMT_UFDTNIRA:
  case SMT_UFIDL:
  case SMT_UFLIA:
  case SMT_UFNIA:
    break;

  // pure real arithmetic theories treat decimals as Real constants
  case SMT_LRA:
  case SMT_NRA:
  case SMT_QF_LRA:
  case SMT_QF_NRA:
  case SMT_QF_RDL:
  case SMT_QF_UFLRA:
  case SMT_QF_UFNRA:
  case SMT_UFLRA:
    _numeralsAreReal = true;
    break;

  // we don't support bit vectors
  case SMT_BV:
  case SMT_QF_ABV:
  case SMT_QF_AUFBV:
  case SMT_QF_BV:
  case SMT_QF_UFBV:
  case SMT_UFBV:
    USER_ERROR_EXPR("unsupported logic "+logicStr);
  default:
    if (env.options->ignoreUnrecognizedLogic()) {
      break;
    } else {
      USER_ERROR_EXPR("unrecognized logic " + logicStr + " ( use `--ignore_unrecognized_logic on` if you want vampire to try proof search anyways)");
    }
  }

}

//  ----------------------------------------------------------------------

void SMTLIB2::readDeclareSort(const vstring& name, const vstring& arity)
{
  CALL("SMTLIB2::readDeclareSort");

  vstring pName = name + TYPECON_POSTFIX;
  if (isAlreadyKnownSymbol(pName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  if (not StringUtils::isPositiveInteger(arity)) {
    USER_ERROR_EXPR("Unrecognized declared sort arity: "+arity);
  }

  unsigned val;
  if (!Int::stringToUnsignedInt(arity, val)) {
    USER_ERROR_EXPR("Couldn't convert sort arity: "+arity);
  }

  bool added;
  unsigned srt = env.signature->addTypeCon(pName,val,added);
  ASS(added);
  ALWAYS(_declaredSymbols.insert(pName,make_pair(srt,SymbolType::TYPECON)));
  env.signature->getTypeCon(srt)->setType(OperatorType::getTypeConType(val));
}

void SMTLIB2::readDefineSort(const vstring& name, LExprList* args, LExpr* body)
{
  CALL("SMTLIB2::readDefineSort");

  vstring pName = name + TYPECON_POSTFIX;
  if (isAlreadyKnownSymbol(pName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  // here we could check the definition for well-formed-ness
  // current solution: crash only later, at application site

  ALWAYS(_sortDefinitions.insert(pName,SortDefinition(args,body)));
}

//  ----------------------------------------------------------------------

/**
 * Helper function for parsing a sort expression.
 */
TermList SMTLIB2::parseSort(LExpr* sExpr)
{
  ParseResult pr = parseTermOrFormula(sExpr,true/*isSort*/);
  TermList sort;
  ALWAYS(pr.asTerm(sort) == AtomicSort::superSort());
  return sort;
}

static const char* EXISTS = "exists";
static const char* FORALL = "forall";

const char * SMTLIB2::s_formulaSymbolNameStrings[] = {
    "<",
    "<=",
    "=",
    "=>",
    ">",
    ">=",
    "and",
    "distinct",
    EXISTS,
    "false",
    FORALL,
    "is_int",
    "not",
    "or",
    PAR,
    "true",
    "xor"
};

SMTLIB2::FormulaSymbol SMTLIB2::getBuiltInFormulaSymbol(const vstring& str)
{
  CALL("SMTLIB::getFormulaSymbol");

  static NameArray formulaSymbolNames(s_formulaSymbolNameStrings, sizeof(s_formulaSymbolNameStrings)/sizeof(char*));
  ASS_EQ(formulaSymbolNames.length, FS_USER_PRED_SYMBOL);

  int res = formulaSymbolNames.tryToFind(str.c_str());
  if(res==-1) {
    return FS_USER_PRED_SYMBOL;
  }
  return static_cast<FormulaSymbol>(res);
}

static const char* LET = "let";
static const char* MATCH = "match";

const char * SMTLIB2::s_termSymbolNameStrings[] = {
    "*",
    "+",
    "-",
    "/",
    "Array",
    "Bool",
    "Int",
    "Real",
    "abs",
    "div",
    "ite",
    LET,
    MATCH,
    "mod",
    "select",
    "store",
    "to_int",
    "to_real"
};

SMTLIB2::TermSymbol SMTLIB2::getBuiltInTermSymbol(const vstring& str)
{
  CALL("SMTLIB::getTermSymbol");

  static NameArray termSymbolNames(s_termSymbolNameStrings, sizeof(s_termSymbolNameStrings)/sizeof(char*));
  ASS_EQ(termSymbolNames.length, TS_USER_FUNCTION);

  int resInt = termSymbolNames.tryToFind(str.c_str());
  if(resInt==-1) {
    return TS_USER_FUNCTION;
  }
  return static_cast<TermSymbol>(resInt);
}

bool SMTLIB2::isAlreadyKnownSymbol(const vstring& name)
{
  CALL("SMTLIB2::isAlreadyKnownSymbol");

  if (getBuiltInFormulaSymbol(name) != FS_USER_PRED_SYMBOL) {
    return true;
  }

  if (getBuiltInTermSymbol(name) != TS_USER_FUNCTION) {
    return true;
  }

  if (_declaredSymbols.find(name)) {
    return true;
  }

  return false;
}

void SMTLIB2::readDeclareFun(const vstring& name, LExprList* iSorts, LExpr* oSort, unsigned taArity)
{
  CALL("SMTLIB2::readDeclareFun");

  if (isAlreadyKnownSymbol(name)) {
    USER_ERROR_EXPR("Redeclaring function symbol: "+name);
  }

  TermList rangeSort = parseSort(oSort);

  LispListReader isRdr(iSorts);

  static TermStack argSorts;
  argSorts.reset();

  while (isRdr.hasNext()) {
    argSorts.push(parseSort(isRdr.next()));
  }

  declareFunctionOrPredicate(name,rangeSort,argSorts,taArity);
}

SMTLIB2::DeclaredSymbol SMTLIB2::declareFunctionOrPredicate(const vstring& name, TermList rangeSort, const TermStack& argSorts, unsigned taArity)
{
  CALL("SMTLIB2::declareFunctionOrPredicate");

  bool added = false;
  unsigned symNum;
  Signature::Symbol* sym;
  OperatorType* type;

  if (rangeSort == AtomicSort::boolSort()) { // predicate
    symNum = env.signature->addPredicate(name, argSorts.size()+taArity, added);

    sym = env.signature->getPredicate(symNum);

    type = OperatorType::getPredicateType(argSorts.size(),argSorts.begin(),taArity);

    LOG1("declareFunctionOrPredicate-Predicate");
  } else { // proper function
    if (argSorts.size() > 0 || taArity > 0) {
      symNum = env.signature->addFunction(name, argSorts.size()+taArity, added);
    } else {
      symNum = TPTP::addUninterpretedConstant(name,_overflow,added);
    }

    sym = env.signature->getFunction(symNum);

    type = OperatorType::getFunctionType(argSorts.size(), argSorts.begin(), rangeSort, taArity);

    LOG1("declareFunctionOrPredicate-Function");
  }

  ASS(added);
  sym->setType(type);

  DeclaredSymbol res = make_pair(symNum,type->isFunctionType()?SymbolType::FUNCTION:SymbolType::PREDICATE);

  LOG2("declareFunctionOrPredicate -name ",name);
  LOG2("declareFunctionOrPredicate -symNum ",symNum);
  LOG2("declareFunctionOrPredicate -arity ",argSorts.size());

  ALWAYS(_declaredSymbols.insert(name,res));

  return res;
}

//  ----------------------------------------------------------------------

void SMTLIB2::readDefineFun(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body, const TermStack& typeArgs, bool recursive)
{
  CALL("SMTLIB2::readDefineFun");

  if (isAlreadyKnownSymbol(name)) {
    USER_ERROR_EXPR("Redeclaring function symbol: "+name);
  }

  TermList rangeSort = parseSort(oSort);

  TermLookup* lookup = new TermLookup();

  static TermStack argSorts;
  argSorts.reset();

  static TermStack args;
  args.reset();
  for (const auto& ta : typeArgs) {
    args.push(ta);
  }

  LispListReader iaRdr(iArgs);
  while (iaRdr.hasNext()) {
    LExprList* pair = iaRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    TermList vSort = parseSort(pRdr.readNext());

    pRdr.acceptEOL();

    TermList arg = TermList(_nextVar++, false);
    args.push(arg);

    if (!lookup->insert(vName,make_pair(arg,vSort))) {
      USER_ERROR_EXPR("Multiple occurrence of variable "+vName+" in the definition of function "+name);
    }

    argSorts.push(vSort);
  }

  _scopes.push(lookup);

  DeclaredSymbol fun;
  if (recursive) {
    fun = declareFunctionOrPredicate(name, rangeSort, argSorts, typeArgs.size());
  }

  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  delete _scopes.pop();

  TermList rhs;
  if (res.asTerm(rhs) != rangeSort) {
    USER_ERROR_EXPR("Defined function body "+body->toString()+" has different sort than declared "+oSort->toString());
  }

  if (!recursive) {
    fun = declareFunctionOrPredicate(name, rangeSort, argSorts, typeArgs.size());
  }

  unsigned symbIdx = fun.first;
  ASS(fun.second != SymbolType::TYPECON);
  bool isTrueFun = fun.second==SymbolType::FUNCTION;

  TermList lhs;
  if (isTrueFun) {
    lhs = TermList(Term::create(symbIdx,args.size(),args.begin()));
  } else {
    Formula* frm = new AtomicFormula(Literal::create(symbIdx,args.size(),true,false,args.begin()));
    lhs = TermList(Term::createFormula(frm));
  }

  Formula* fla = new AtomicFormula(Literal::createEquality(true,lhs,rhs,rangeSort));

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));

  UnitList::push(fu, _formulas);
}

void SMTLIB2::readTypeParameters(LispListReader& rdr, TermLookup* lookup, TermStack* ts)
{
  CALL("SMTLIB2::readTypeParameters");

  if (!rdr.hasNext()) {
    USER_ERROR_EXPR("'par' keyword must be followed by a list of parameters");
  }
  LExpr* pars = rdr.next();
  if (!pars->isList()) {
    USER_ERROR_EXPR("'par' keyword must be followed by a list of parameters");
  }
  LispListReader parRdr(pars);
  while (parRdr.hasNext()) {
    auto par = parRdr.next();
    if (!par->isAtom()) {
      USER_ERROR_EXPR("List of parameters contains non-atomic expression '"+par->str+"'");
    }
    TermList sortVar(_nextVar++, false);
    if (!lookup->insert(par->str, make_pair(sortVar, AtomicSort::superSort()))) {
      USER_ERROR_EXPR("Type parameter '" + par->str + "' has already been defined");
    }
    if (ts) {
      ts->push(sortVar);
    }
  }
}

void SMTLIB2::readDeclareDatatype(LExpr *sort, LExprList *datatype)
{
  CALL("SMTLIB2::readDeclareDatatype");

  // first declare the sort
  vstring dtypeName = sort->str+TYPECON_POSTFIX;
  if (isAlreadyKnownSymbol(dtypeName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol as datatype: " + dtypeName);
  }
  LispListReader dtypeRdr(datatype);
  auto lookup = new TermLookup();
  _scopes.push(lookup);
  if (dtypeRdr.hasNext() && dtypeRdr.peekAtNext()->isAtom() && dtypeRdr.peekAtNext()->str == PAR) {
    dtypeRdr.readAtom();
    readTypeParameters(dtypeRdr, lookup);
    auto rest = dtypeRdr.readList();
    dtypeRdr.acceptEOL();
    dtypeRdr = LispListReader(rest);
  }
  auto numTypeVars = lookup->size();

  bool added = false;
  unsigned srt = env.signature->addTypeCon(dtypeName,numTypeVars,added);
  ALWAYS(_declaredSymbols.insert(dtypeName, make_pair(srt,SymbolType::TYPECON)));
  Stack<TermAlgebraConstructor *> constructors;
  TermStack argSorts;
  Stack<vstring> destructorNames;

  ASS(added);
  env.signature->getTypeCon(srt)->setType(OperatorType::getTypeConType(numTypeVars));
  TermStack parSorts;
  for (unsigned i = 0; i < numTypeVars; i++) {
    parSorts.push(TermList(i,false));
  }
  TermList taSort(AtomicSort::create(srt,parSorts.size(),parSorts.begin()));

  while (dtypeRdr.hasNext()) {
    argSorts.reset();
    destructorNames.reset();
    // read each constructor declaration
    vstring constrName;
    LExpr *constr = dtypeRdr.next();
    ASS(constr->isList());
    LispListReader constrRdr(constr);
    constrName = constrRdr.readAtom();

    while (constrRdr.hasNext()) {
      LExpr *arg = constrRdr.next();
      if (arg->isAtom()) {
        USER_ERROR_EXPR("Constructor argument must be a pair of destructor name and argument type:" + arg->toString());
      }
      LispListReader argRdr(arg);
      destructorNames.push(argRdr.readAtom());
      argSorts.push(parseSort(argRdr.next()));

      if (argRdr.hasNext()) {
        USER_ERROR_EXPR("Bad constructor argument:" + arg->toString());
      }
    }
    constructors.push(buildTermAlgebraConstructor(constrName, taSort, destructorNames, argSorts));
  }
  delete _scopes.pop();

  ASS(!env.signature->isTermAlgebraSort(taSort));
  TermAlgebra* ta = new TermAlgebra(taSort, constructors.size(), constructors.begin(), false);

  if (ta->emptyDomain()) {
    USER_ERROR_EXPR("Datatype " + dtypeName + " defines an empty sort");
  }

  env.signature->addTermAlgebra(ta);
}

void SMTLIB2::readDeclareDatatypes(LExprList* sorts, LExprList* datatypes, bool codatatype)
{
  CALL("SMTLIB2::readDeclareDatatypes");
  
  if(LExprList::length(sorts) != LExprList::length(datatypes)){
    USER_ERROR_EXPR("declare-datatype(s) declaration mismatch between declared datatypes and definitions");
  }

  // first declare all the sorts, and then only the constructors, in
  // order to allow mutually recursive datatypes definitions
  LispListReader dtypesNamesRdr(sorts);
  Stack<vstring> dtypeNames;
  while (dtypesNamesRdr.hasNext()) {
    LispListReader dtypeNRdr(dtypesNamesRdr.readList());

    vstring dtypeName = dtypeNRdr.readAtom()+TYPECON_POSTFIX;
    const vstring& dtypeSize = dtypeNRdr.readAtom();
    unsigned arity;
    if(!Int::stringToUnsignedInt(dtypeSize,arity)){ USER_ERROR_EXPR("datatype arity not given"); }
    if(arity>0){ USER_ERROR_EXPR("unsupported parametric datatype declaration"); }
    if (isAlreadyKnownSymbol(dtypeName)) {
      USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol as datatype: "+dtypeName);
    }

    bool added = false;
    unsigned srt = env.signature->addTypeCon(dtypeName,0,added);
    ASS(added);
    ALWAYS(_declaredSymbols.insert(dtypeName, make_pair(srt, SymbolType::TYPECON)));
    env.signature->getTypeCon(srt)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    TermList sort = TermList(AtomicSort::createConstant(srt));
    (void)sort; // to get rid of compiler warning when logging is off
    // TODO: is it really OK we normally don't need the sort?
    LOG2("reading datatype "+dtypeName+" as sort ",sort);
    dtypeNames.push(dtypeName);
  }

  Stack<TermAlgebraConstructor*> constructors;
  TermStack argSorts;
  Stack<vstring> destructorNames;

  LispListReader dtypesDefsRdr(datatypes);
  Stack<vstring>::BottomFirstIterator dtypeNameIter(dtypeNames);
  while(dtypesDefsRdr.hasNext()) {
    ASS(dtypeNameIter.hasNext());
    constructors.reset();
    const vstring& taName = dtypeNameIter.next(); 
    bool added = false;
    unsigned sort = env.signature->addTypeCon(taName,0,added);
    ASS(!added);
    TermList taSort(AtomicSort::createConstant(sort));

    LispListReader dtypeRdr(dtypesDefsRdr.readList());
    while (dtypeRdr.hasNext()) {
      argSorts.reset();
      destructorNames.reset();
      // read each constructor declaration
      vstring constrName;
      LExpr *constr = dtypeRdr.next();
      if (constr->isAtom()) {
        // atom, construtor of arity 0
        constrName = constr->str;
      } else {
        ASS(constr->isList());
        LispListReader constrRdr(constr);
        constrName = constrRdr.readAtom();

        while (constrRdr.hasNext()) {
          LExpr *arg = constrRdr.next();
          LispListReader argRdr(arg);
          destructorNames.push(argRdr.readAtom());
          argSorts.push(parseSort(argRdr.next()));
          if (argRdr.hasNext()) {
            USER_ERROR_EXPR("Bad constructor argument:" + arg->toString());
          }
        }
      }
      constructors.push(buildTermAlgebraConstructor(constrName, taSort, destructorNames, argSorts));
    }

    ASS(!env.signature->isTermAlgebraSort(taSort));
    TermAlgebra* ta = new TermAlgebra(taSort, constructors.size(), constructors.begin(), codatatype);

    if (ta->emptyDomain()) {
      USER_ERROR_EXPR("Datatype " + taName + " defines an empty sort");
    }

    env.signature->addTermAlgebra(ta);
  }
}

TermAlgebraConstructor* SMTLIB2::buildTermAlgebraConstructor(vstring constrName, TermList taSort,
                                                             Stack<vstring> destructorNames, TermStack argSorts) {
  CALL("SMTLIB2::buildTermAlgebraConstructor");

  if (isAlreadyKnownSymbol(constrName)) {
    USER_ERROR_EXPR("Redeclaring function symbol: " + constrName);
  }

  ASS(taSort.isTerm() && taSort.term()->isSort());
  unsigned numTypeArgs = taSort.term()->arity();
  unsigned arity = (unsigned)argSorts.size();

  bool added;
  unsigned functor = env.signature->addFunction(constrName, numTypeArgs+arity, added);
  ASS(added);

  OperatorType* constructorType = OperatorType::getFunctionType(arity, argSorts.begin(), taSort, numTypeArgs);
  env.signature->getFunction(functor)->setType(constructorType);
  env.signature->getFunction(functor)->markTermAlgebraCons();

  LOG1("build constructor "+constrName+": "+constructorType->toString());

  ALWAYS(_declaredSymbols.insert(constrName, make_pair(functor, SymbolType::FUNCTION)));

  Lib::Array<unsigned> destructorFunctors(arity);
  for (unsigned i = 0; i < arity; i++) {
    vstring destructorName = destructorNames[i];
    TermList destructorSort = argSorts[i];

    if (isAlreadyKnownSymbol(destructorName)) {
      USER_ERROR_EXPR("Redeclaring function symbol: " + destructorName);
    }

    bool isPredicate = destructorSort == AtomicSort::boolSort();
    bool added;
    unsigned destructorFunctor = isPredicate ? env.signature->addPredicate(destructorName, numTypeArgs+1, added)
                                             : env.signature->addFunction(destructorName,  numTypeArgs+1, added);
    ASS(added);

    OperatorType* destructorType = isPredicate ? OperatorType::getPredicateType(1, &taSort, numTypeArgs)
                                           : OperatorType::getFunctionType(1, &taSort, destructorSort, numTypeArgs);

    LOG1("build destructor "+destructorName+": "+destructorType->toString());

    auto destSym = isPredicate ? env.signature->getPredicate(destructorFunctor)
                               : env.signature->getFunction (destructorFunctor);
    destSym->setType(destructorType);
    destSym->markTermAlgebraDest();

    ALWAYS(_declaredSymbols.insert(destructorName, make_pair(destructorFunctor, isPredicate ? SymbolType::PREDICATE : SymbolType::FUNCTION)));

    destructorFunctors[i] = destructorFunctor;
  }

  return new TermAlgebraConstructor(functor, destructorFunctors);
}

bool SMTLIB2::ParseResult::asFormula(Formula*& resFrm)
{
  CALL("SMTLIB2::ParseResult::asFormula");

  if (formula) {
    ASS_EQ(sort, AtomicSort::boolSort());
    resFrm = attachLabelToFormula(frm);


    LOG2("asFormula formula ",resFrm->toString());
    return true;
  }

  if (sort == AtomicSort::boolSort()) {
    // can we unwrap instead of wrapping back and forth?
    if (trm.isTerm()) {
      Term* t = trm.term();
      if (t->isFormula()) {
        resFrm = attachLabelToFormula(t->getSpecialData()->getFormula());

        // t->destroy(); -- we cannot -- it can be accessed more than once

        LOG2("asFormula unwrap ",trm.toString());

        return true;
      }
    }

    LOG2("asFormula wrap ",trm.toString());

    resFrm = attachLabelToFormula(new BoolTermFormula(trm));
    return true;
  }

  return false;
}

TermList SMTLIB2::ParseResult::asTerm(TermList& resTrm)
{
  CALL("SMTLIB2::ParseResult::asTerm");

  if (formula) {
    ASS_EQ(sort, AtomicSort::boolSort());

    LOG2("asTerm wrap ",frm->toString());

    resTrm = TermList(Term::createFormula(frm));

    LOG2("asTerm sort ",sort);
    return AtomicSort::boolSort();
  } else {
    resTrm = trm;

    LOG2("asTerm native ",trm.toString());

    LOG2("asTerm sort ",sort);

    return sort;
  }
}

vstring SMTLIB2::ParseResult::toString()
{
  CALL("SMTLIB2::ParseResult::toString");
  if (isSeparator()) {
    return "separator";
  }
  if (formula) {
    return "formula of sort "+sort.toString()+": "+frm->toString();
  }
  return "term of sort "+sort.toString()+": "+trm.toString();
}

Formula* SMTLIB2::ParseResult::attachLabelToFormula(Formula* frm)
{
  if (!label.empty()) {
    frm->label(label);
  }
  return frm;
}

Interpretation SMTLIB2::getFormulaSymbolInterpretation(FormulaSymbol fs, TermList firstArgSort)
{
  CALL("SMTLIB2::getFormulaSymbolInterpretation");

  switch(fs) {
  case FS_LESS:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_LESS;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_LESS;
    } 
    break;
  case FS_LESS_EQ:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_LESS_EQUAL;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_LESS_EQUAL;
    } 
    break;
  case FS_GREATER:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_GREATER;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_GREATER;
    } 
    break;
  case FS_GREATER_EQ:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_GREATER_EQUAL;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_GREATER_EQUAL;
    }
    break;

  default:
    ASSERTION_VIOLATION;
  }
  USER_ERROR_EXPR("invalid sort "+ firstArgSort.toString() +" for interpretation "+vstring(s_formulaSymbolNameStrings[fs]));
}

Interpretation SMTLIB2::getUnaryMinusInterpretation(TermList argSort)
{
  CALL("SMTLIB2::getUnaryMinusInterpretation");

  if(argSort == AtomicSort::intSort()){
      return Theory::INT_UNARY_MINUS;
  } else if(argSort == AtomicSort::realSort()) {
      return Theory::REAL_UNARY_MINUS;
  } else {
    USER_ERROR_EXPR("invalid sort "+ argSort.toString() +" for interpretation -");
  }
}

Interpretation SMTLIB2::getTermSymbolInterpretation(TermSymbol ts, TermList firstArgSort)
{
  CALL("SMTLIB2::getTermSymbolInterpretation");

  switch(ts) {
  case TS_MINUS:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_MINUS;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_MINUS;
    } 
    break;
  case TS_PLUS:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_PLUS;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_PLUS;
    } 
    break;
  case TS_MULTIPLY:
    if(firstArgSort == AtomicSort::intSort()){
      return Theory::INT_MULTIPLY;
    } else if(firstArgSort == AtomicSort::realSort()) {
      return Theory::REAL_MULTIPLY;
    } 
    break;

  case TS_DIVIDE:
    if (firstArgSort == AtomicSort::realSort())
      return Theory::REAL_QUOTIENT;
    break;

  case TS_DIV:
    if (firstArgSort == AtomicSort::intSort())
      return Theory::INT_QUOTIENT_E;
    break;

  default:
    ASSERTION_VIOLATION_REP(ts);
  }
    USER_ERROR_EXPR("invalid sort "+firstArgSort.toString()+" for interpretation "+vstring(s_termSymbolNameStrings[ts]));
}

void SMTLIB2::complainAboutArgShortageOrWrongSorts(const vstring& symbolClass, LExpr* exp)
{
  CALL("SMTLIB2::complainAboutArgShortageOrWrongSorts");

  USER_ERROR_EXPR("Not enough arguments or wrong sorts for "+symbolClass+" application '"+exp->toString()+"'");
}

void SMTLIB2::parseLetBegin(LExpr* exp)
{
  CALL("SMTLIB2::parseLetBegin");

  LOG2("parseLetBegin  ",exp->toString());

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the let atom
  ALWAYS(lRdr.readAtom() == LET);

  // now, there should be a list of bindings
  LExprList* bindings = lRdr.readList();

  // and the actual body term
  if (!lRdr.hasNext()) {
    complainAboutArgShortageOrWrongSorts(LET,exp);
  }
  LExpr* body = lRdr.readNext();

  // and that's it
  lRdr.acceptEOL();

  // now read the following bottom up:

  // this will later create the actual let term and kill the lookup
  _todo.push(make_pair(PO_LET_END,exp));

  // this will parse the let's body (in the context of the lookup)
  _todo.push(make_pair(PO_PARSE,body));

  // this will create the lookup when all bindings' expressions are parsed (and their sorts known)
  _todo.push(make_pair(PO_LET_PREPARE_LOOKUP,exp));

  // but we start by parsing the bound expressions
  LispListReader bindRdr(bindings);
  while (bindRdr.hasNext()) {
    LExprList* pair = bindRdr.readList();
    LispListReader pRdr(pair);

    pRdr.readAtom(); // for now ignore the identifier
    LExpr* expr = pRdr.readNext();

    _todo.push(make_pair(PO_PARSE,expr)); // just parse the expression
    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseLetPrepareLookup(LExpr* exp)
{
  CALL("SMTLIB2::parseLetPrepareLookup");
  LOG2("PO_LET_PREPARE_LOOKUP",exp->toString());

  // so we know it is let
  ASS(exp->isList());
  LispListReader lRdr(exp->list);
  ALWAYS(lRdr.readAtom() == LET);

  // with a list of bindings
  LispListReader bindRdr(lRdr.readList());

  // corresponding results have already been parsed
  ParseResult* boundExprs = _results.end();

  TermLookup* lookup = new TermLookup();

  while (bindRdr.hasNext()) {
    LExprList* pair = bindRdr.readList();
    LispListReader pRdr(pair);

    const vstring& cName = pRdr.readAtom();
    ParseResult* pr = (--boundExprs);
    TermList t;
    TermList sort = pr->asTerm(t);
    DHMap<unsigned,TermList> vs;
    if (t.isVar()) {
      if (sort.isVar()) {
        vs.insert(sort.var(),AtomicSort::superSort());
      } else {
        SortHelper::collectVariableSorts(sort.term(),vs);
      }
      ALWAYS(vs.insert(t.var(),sort));
    } else {
      SortHelper::collectVariableSorts(t.term(),vs);
    }
    TermStack args;
    TermStack varSorts;
    auto typeVars = VList::empty();
    VList::FIFO tvs(typeVars);
    // type vars are before term vars in the args list, so process them first
    iterTraits(vs.items())
      .forEach([&tvs,&args](std::pair<unsigned,TermList> kv) {
        if (kv.second != AtomicSort::superSort()) {
          return;
        }
        tvs.pushBack(kv.first);
        args.push(TermList(kv.first,false));
      });
    iterTraits(vs.items())
      .forEach([&varSorts,&args](std::pair<unsigned,TermList> kv) {
        if (kv.second == AtomicSort::superSort()) {
          return;
        }
        if (kv.second.isTerm() && kv.second.term()->ground()) {
          // only interested in parametric variables
          return;
        }
        varSorts.push(kv.second);
        args.push(TermList(kv.first,false));
      });
    SortHelper::normaliseArgSorts(typeVars,varSorts);

    TermList trm;
    if (sort == AtomicSort::boolSort()) {
      unsigned symb = env.signature->addFreshPredicate(args.size(),"sLP");
      OperatorType* type = OperatorType::getPredicateType(varSorts.size(), varSorts.begin(), args.size()-varSorts.size());
      env.signature->getPredicate(symb)->setType(type);

      Formula* atom = new AtomicFormula(Literal::create(symb,args.size(),true,false,args.begin()));
      trm = TermList(Term::createFormula(atom));
    } else {
      TermList nSort = sort;
      SortHelper::normaliseSort(typeVars,nSort);
      unsigned symb = env.signature->addFreshFunction (args.size(),"sLF");
      OperatorType* type = OperatorType::getFunctionType(varSorts.size(), varSorts.begin(), nSort, args.size()-varSorts.size());
      env.signature->getFunction(symb)->setType(type);

      trm = TermList(Term::create(symb,args.size(),args.begin()));
    }

    if (!lookup->insert(cName,make_pair(trm,sort))) {
      USER_ERROR_EXPR("Multiple bindings of symbol "+cName+" in let expression "+exp->toString());
    }
  }

  _scopes.push(lookup);
}

void SMTLIB2::parseLetEnd(LExpr* exp)
{
  CALL("SMTLIB2::parseLetEnd");
  LOG2("PO_LET_END ",exp->toString());

  // so we know it is let
  ASS(exp->isList());
  LispListReader lRdr(exp->list);
  DEBUG_CODE(const vstring& theLetAtom =)
    lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theLetAtom),TS_LET);

  // with a list of bindings
  LispListReader bindRdr(lRdr.readList());

  TermLookup* lookup = _scopes.pop();

  // there has to be the body result:
  TermList let;
  TermList letSort = _results.pop().asTerm(let);

  LOG2("LET body  ",let.toString());

  while (bindRdr.hasNext()) {
    LExprList* pair = bindRdr.readList();
    LispListReader pRdr(pair);

    const vstring& cName = pRdr.readAtom();
    TermList boundExpr;
    _results.pop().asTerm(boundExpr);

    LOG2("BOUND name  ",cName);
    LOG2("BOUND term  ",boundExpr.toString());

    SortedTerm term = lookup->get(cName);
    TermList exprTerm = term.first;
    TermList exprSort = term.second;
    ASS(exprTerm.isTerm());
    auto exprT = exprTerm.term();
    if (exprSort == AtomicSort::boolSort()) { // it has to be formula term, with atomic formula
      exprT = exprT->getSpecialData()->getFormula()->literal();
    }

    auto vars = VList::empty();
    VList::FIFO vs(vars);
    Substitution subst;
    for (unsigned i = 0; i < exprT->arity(); i++) {
      subst.bind(exprT->nthArgument(i)->var(),TermList(_nextVar,false));
      vs.pushBack(_nextVar++);
    }

    let = TermList(Term::createLet(exprT->functor(), vars, SubstHelper::apply(boundExpr,subst), let, letSort));
  }

  _results.push(ParseResult(letSort,let));

  delete lookup;
}

static const char *UNDERSCORE = "_";

bool SMTLIB2::isTermAlgebraConstructor(const vstring &name)
{
  CALL("SMTLIB2::isTermAlgebraConstructor");

  if (_declaredSymbols.find(name)) {
    DeclaredSymbol &s = _declaredSymbols.get(name);
    return (s.second==SymbolType::FUNCTION && env.signature->getTermAlgebraConstructor(s.first));
  }

  return false;
}

void SMTLIB2::parseMatchBegin(LExpr *exp)
{
  CALL("SMTLIB2::parseMatchBegin");

  LOG2("parseMatchBegin  ", exp->toString());

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the match atom
  DEBUG_CODE(const vstring &theMatchAtom =) lRdr.readAtom();
  ASS_EQ(theMatchAtom, MATCH);

  // next is the matched term
  if (!lRdr.hasNext()) {
    complainAboutArgShortageOrWrongSorts(MATCH, exp);
  }
  LExpr *matchedAtom = lRdr.readNext();

  // and the list of cases
  if (!lRdr.hasNext()) {
    complainAboutArgShortageOrWrongSorts(MATCH, exp);
  }
  LispListReader casesRdr(lRdr.readList());

  lRdr.acceptEOL();

  _todo.push(make_pair(PO_MATCH_END, exp));
  // this is the last thing we parse so that it pops
  // first when the result is created
  _todo.push(make_pair(PO_PARSE, matchedAtom));

  while (casesRdr.hasNext()) {
    LispListReader pRdr(casesRdr.readList());

    if (!pRdr.hasNext()) {
      complainAboutArgShortageOrWrongSorts(MATCH, exp);
    }
    LExpr *pattern = pRdr.readNext();
    if (!pRdr.hasNext()) {
      complainAboutArgShortageOrWrongSorts(MATCH, exp);
    }
    LExpr *body = pRdr.readNext();

    LExpr *l = new LExpr(LispParser::LIST);
    LExprList::push(body, l->list);
    LExprList::push(pattern, l->list);
    _todo.push(make_pair(PO_MATCH_CASE_END, l));
    _todo.push(make_pair(PO_MATCH_CASE_START, l));
    _todo.push(make_pair(PO_PARSE, matchedAtom));
    if (pattern->isList()) {
      LispListReader tRdr(pattern);
      DeclaredSymbol sym;
      auto fst = tRdr.readAtom();
      if (!_declaredSymbols.find(fst,sym)) {
        USER_ERROR_EXPR("Constructor symbol in match is not declared: "+fst);
      }
      if (sym.second != SymbolType::FUNCTION) {
        USER_ERROR_EXPR("Only function constructors are allowed: "+fst);
      }
      auto fn = env.signature->getFunction(sym.first);
      unsigned i = 0;
      // we need the type arguments in reverse order,
      // so we push them on a stack and pop them
      Stack<LExpr*> st;
      while (tRdr.hasNext() && i++ < fn->numTypeArguments()) {
        st.push(tRdr.readNext());
      }
      while (st.isNonEmpty()) {
        _todo.push(make_pair(PO_PARSE_SORT, st.pop()));
      }
    }
    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseMatchCaseStart(LExpr *exp)
{
  CALL("SMTLIB2::parseMatchCaseStart");

  ASS(exp->isList());
  LispListReader eRdr(exp->list);

  ASS(eRdr.hasNext());
  LExpr *pattern = eRdr.readNext();
  ASS(eRdr.hasNext());
  LExpr *body = eRdr.readNext();
  eRdr.acceptEOL();

  TermList matchedTerm;
  auto matchedTermSort = _results.pop().asTerm(matchedTerm);

  // now parse the match pattern which
  // potentially declares new variables
  TermLookup *lookup = new TermLookup;
  if (pattern->isList()) {
    LispListReader tRdr(pattern);
    auto ctorName = tRdr.readAtom();
    // whether it is a ctor we check in MATCH_END
    auto type = env.signature->getFunction(_declaredSymbols.get(ctorName).first)->fnType();
    unsigned i = 0;
    Substitution subst;
    while (tRdr.hasNext()) {
      auto arg = tRdr.readNext();
      ASS_L(i,type->arity());
      if (i < type->numTypeArguments()) {
        if (_results.isEmpty() || _results.top().isSeparator()) {
          complainAboutArgShortageOrWrongSorts("match pattern",exp);
        }
        TermList arg;
        ALWAYS(_results.pop().asTerm(arg) == AtomicSort::superSort());
        subst.bind(type->quantifiedVar(i).var(),arg);
        i++;
        continue;
      }
      if (!arg->isAtom() || isAlreadyKnownSymbol(arg->str)) {
        USER_ERROR_EXPR("Nested ctors ("+arg->toString()+") in match patterns are disallowed: '" + exp->toString() + "'");
      }
      // from the type arguments used in the matched term we instantiate the type of the other variables
      if (!lookup->insert(arg->str, make_pair(TermList(_nextVar++, false), SubstHelper::apply(type->arg(i++), subst)))) {
        USER_ERROR_EXPR("Variable '" + arg->str + "' has already been defined");
      }
    }
  }
  // non-ctor atom
  else if (!isTermAlgebraConstructor(pattern->str)) {
    if (isAlreadyKnownSymbol(pattern->str)) {
      USER_ERROR_EXPR("Constant symbol found in match pattern: '" + exp->toString() + "'");
    }
    // in case of _ nothing to add to lookup
    if (pattern->str != UNDERSCORE) {
      if (!lookup->insert(pattern->str, make_pair(TermList(_nextVar++, false), matchedTermSort))) {
        USER_ERROR_EXPR("Variable '" + pattern->str + "' has already been defined");
      }
    }
  }

  _scopes.push(lookup);
  // only parse pattern if it's not _
  if (pattern->isList() || pattern->str != UNDERSCORE) {
    _todo.push(make_pair(PO_PARSE, pattern));
  }
  _todo.push(make_pair(PO_PARSE, body));
}

void SMTLIB2::parseMatchCaseEnd(LExpr *exp)
{
  CALL("SMTLIB2::parseMatchCaseEnd");

  LExprList::destroy(exp->list);
  delete exp;
  delete _scopes.pop();
}

void SMTLIB2::parseMatchEnd(LExpr *exp)
{
  CALL("SMTLIB2::parseMatchEnd");

  LOG2("PO_MATCH_END ", exp->toString());

  ASS(exp->isList());
  LispListReader lRdr(exp->list);
  DEBUG_CODE(const vstring &theMatchAtom =) lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theMatchAtom), TS_MATCH);

  lRdr.readNext(); // the matched term
  TermList matchedTerm;
  auto matchedTermSort = _results.pop().asTerm(matchedTerm);

  LOG2("CASE matched ", matchedTerm.toString());

  vmap<unsigned, TermAlgebraConstructor *> ctorFunctors;
  TermAlgebra *ta = env.signature->getTermAlgebraOfSort(matchedTermSort);
  if (ta == nullptr) {
    USER_ERROR_EXPR("Match term '" + matchedTerm.toString() + "' is not of a term algebra type in expression '" + exp->toString() + "'");
  }
  for (unsigned int i = 0; i < ta->nConstructors(); i++) {
    ctorFunctors.insert(make_pair(ta->constructor(i)->functor(), ta->constructor(i)));
  }

  TermList varPattern;
  TermList varBody;
  bool varUsed = false;
  Stack<TermList> elements;
  elements.push(matchedTerm);
  TermList sort = AtomicSort::defaultSort();

  LispListReader cRdr(lRdr.readList());
  while (cRdr.hasNext()) {
    LispListReader pRdr(cRdr.readList());
    LExpr *pattern = pRdr.readNext();
    pRdr.readNext(); // body
    pRdr.acceptEOL();
    TermList p;
    if (pattern->isAtom() && pattern->str == UNDERSCORE) {
      p = TermList(_nextVar++, false);
    }
    else {
      ALWAYS(_results.pop().asTerm(p) == matchedTermSort);
    }
    TermList b;
    TermList currSort = _results.pop().asTerm(b);
    ASS(sort == AtomicSort::defaultSort() || sort == currSort);
    sort = currSort;

    LOG2("CASE pattern ", p.toString());
    LOG2("CASE body    ", b.toString());

    if (p.isVar()) {
      if (varUsed) {
        USER_ERROR_EXPR("Else branch cannot be used twice in match in '" + exp->toString() + "'");
      }
      varUsed = true;
      varPattern = p;
      varBody = b;
    }
    else {
      auto functor = p.term()->functor();
      if (ctorFunctors.erase(functor) != 1) {
        USER_ERROR_EXPR("Match pattern '" + p.toString() + "' is either not ctor or was listed twice in '" + exp->toString() + "'");
      }
      elements.push(p);
      elements.push(b);
    }
  }
  lRdr.acceptEOL();

  // if there is a variable pattern,
  // we add the missing ctors
  if (varUsed) {
    Stack<TermList> argTerms;
    // the number of type arguments for all ctors is the arity of the type
    unsigned numTypeArgs = env.signature->getTypeCon(sort.term()->functor())->typeConType()->arity();
    for (const auto &kv : ctorFunctors) {
      argTerms.reset();
      for (unsigned j = 0; j < kv.second->arity(); j++) {
        if (j < numTypeArgs) {
          argTerms.push(*sort.term()->nthArgument(j));
        } else {
          argTerms.push(TermList(_nextVar++, false));
        }
      }
      TermList pattern(Term::create(kv.second->functor(), argTerms.size(), argTerms.begin()));
      LOG2("CASE missing ", pattern);
      elements.push(pattern);
      if (varPattern.isVar()) {
        Substitution subst;
        subst.bind(varPattern.var(), pattern);
        varBody = SubstHelper::apply(varBody, subst);
      }
      elements.push(varBody);
    }
  }
  else if (ctorFunctors.size() > 0) {
    USER_ERROR_EXPR("Missing ctors in match expression '" + exp->toString() + "'");
  }

  auto match = TermList(Term::createMatch(sort, matchedTermSort, elements.size(), elements.begin()));
  _results.push(ParseResult(sort,match));
}

void SMTLIB2::parseQuantBegin(LExpr* exp)
{
  CALL("SMTLIB2::parseQuantBegin");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the quant atom
  DEBUG_CODE(const vstring& theQuantAtom =)
    lRdr.readAtom();
  ASS(theQuantAtom == FORALL || theQuantAtom == EXISTS);
  _todo.push(make_pair(PO_QUANT,exp));

  // there should next be a list of sorted variables
  LispListReader varRdr(lRdr.readList());

  while (varRdr.hasNext()) {
    LExprList* pair = varRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    if(!pRdr.hasNext()) {
      USER_ERROR_EXPR("No associated sort for "+vName+" in quantification "+exp->toString());
    }
    _todo.push(make_pair(PO_PARSE_SORT, pRdr.readNext()));
    if(pRdr.hasNext()) {
      USER_ERROR_EXPR("More than one sort for "+vName+" in quantification "+exp->toString());
    }

    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseQuantEnd(LExpr* exp)
{
  CALL("SMTLIB2::parseQuantEnd");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // already checked the quant atom
  lRdr.readAtom();

  // there should next be a list of sorted variables
  LispListReader varRdr(lRdr.readList());

  TermLookup* lookup = new TermLookup();

  while (varRdr.hasNext()) {
    LExprList* pair = varRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    ASS(pRdr.hasNext());
    ParseResult pr = _results.pop();
    TermList vSort;
    ALWAYS(pr.asTerm(vSort) == AtomicSort::superSort());
    // the type
    pRdr.readNext();
    ASS(!pRdr.hasNext());

    pRdr.acceptEOL();

    if (!lookup->insert(vName,make_pair(TermList(_nextVar++,false),vSort))) {
      USER_ERROR_EXPR("Multiple occurrence of variable "+vName+" in quantification "+exp->toString());
    }
  }

  if(!lRdr.hasNext())
    USER_ERROR("Missing body in quantification " + exp->toString());

  _scopes.push(lookup);

  if (!lRdr.hasNext()) {
    USER_ERROR_EXPR("Missing quantification body");
  }
  _todo.push(make_pair(PO_PARSE_APPLICATION,exp)); // will create the actual quantified formula and clear the lookup...
  _todo.push(make_pair(PO_PARSE,lRdr.readNext())); // ... from the only remaining argument, the body
  lRdr.acceptEOL();
}

void SMTLIB2::parseParametric(LExpr* exp)
{
  CALL("SMTLIB2::parseParametric");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the par atom
  lRdr.readAtom();

  TermLookup* lookup = new TermLookup();
  readTypeParameters(lRdr, lookup);
  _scopes.push(lookup);

  if (!lRdr.hasNext()) {
    USER_ERROR_EXPR("Missing quantification body");
  }
  _todo.push(make_pair(PO_PARSE_APPLICATION,exp)); // will create the actual quantified formula and clear the lookup...
  _todo.push(make_pair(PO_PARSE,lRdr.readNext())); // ... from the only remaining argument, the body
  lRdr.acceptEOL();
}

static const char* EXCLAMATION = "!";

void SMTLIB2::parseAnnotatedTerm(LExpr* exp)
{
  CALL("SMTLIB2::parseAnnotatedTerm");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the exclamation atom
  ALWAYS(lRdr.readAtom() == EXCLAMATION)

  LExpr* toParse = 0;
  if(lRdr.peekAtNext()->isAtom()){ 
    toParse = lRdr.next();
  }
  else{
    toParse = lRdr.readListExpr();
  }

  static bool annotation_warning = false; // print warning only once

  if (!annotation_warning) {
    //env.beginOutput();
    //env.out() << "% Warning: term annotations ignored!" << endl;
    //env.endOutput();
    annotation_warning = true;
  }

  // we only consider :named annotations
  if(lRdr.tryAcceptAtom(":named")){
    _todo.push(make_pair(PO_LABEL,lRdr.readNext()));
  }

  _todo.push(make_pair(PO_PARSE,toParse));

}

bool SMTLIB2::parseAsScopeLookup(const vstring& id)
{
  CALL("SMTLIB2::parseAsScopeLookup");

  Scopes::Iterator sIt(_scopes);
  while (sIt.hasNext()) {
    TermLookup* lookup = sIt.next();

    SortedTerm st;
    if (lookup->find(id,st)) {
      _results.push(ParseResult(st.second,st.first));
      return true;
    }
  }

  return false;
}

bool SMTLIB2::parseAsSortDefinition(const vstring& id,LExpr* exp)
{
  CALL("SMTLIB2::parseAsSortDefinition");
  vstring pId = id + TYPECON_POSTFIX;
  auto def = _sortDefinitions.findPtr(pId);
  if (!def) {
    return false;
  }
  TermLookup* lookup = new TermLookup();

  LispListReader argRdr(def->args);

  while (argRdr.hasNext()) {
    if (_results.isEmpty() || _results.top().isSeparator()) {
      complainAboutArgShortageOrWrongSorts("sort definition",exp);
    }
    TermList arg;
    ALWAYS(_results.pop().asTerm(arg) == AtomicSort::superSort());
    const vstring& argName = argRdr.readAtom();
    // TODO: could check if the same string names more than one argument positions
    // the following just takes the first and ignores the others
    lookup->insert(argName,make_pair(arg,AtomicSort::superSort()));
  }

  _scopes.push(lookup);

  _todo.push(make_pair(PO_POP_LOOKUP,nullptr)); //schedule lookup deletion (see above)
  _todo.push(make_pair(PO_PARSE_SORT,def->body));

  return true;
}

bool SMTLIB2::parseAsSpecConstant(const vstring& id)
{
  CALL("SMTLIB2::parseAsSpecConstant");

  if (StringUtils::isPositiveInteger(id)) {
    if (_numeralsAreReal) {
      goto real_constant; // just below
    }

    unsigned symb = TPTP::addIntegerConstant(id,_overflow,false);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(AtomicSort::intSort(),res));

    return true;
  }

  if (StringUtils::isPositiveDecimal(id)) {
    real_constant:

    unsigned symb = TPTP::addRealConstant(id,_overflow,false);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(AtomicSort::realSort(),res));

    return true;
  }

  return false;
}

bool SMTLIB2::parseAsUserDefinedSymbol(const vstring& id,LExpr* exp,bool isSort)
{
  CALL("SMTLIB2::parseAsUserDefinedSymbol");

  DeclaredSymbol sym;
  if (!_declaredSymbols.find(id+(isSort?TYPECON_POSTFIX:""),sym)) {
    return false;
  }
  ASS(sym.second != SymbolType::TYPECON || isSort);

  unsigned symbIdx = sym.first;
  Signature::Symbol* symbol = nullptr;
  OperatorType* type = nullptr;
  switch (sym.second)
  {
  case SymbolType::FUNCTION: {
    symbol = env.signature->getFunction(symbIdx);
    type = symbol->fnType();
    break;
  }
  case SymbolType::PREDICATE: {
    symbol = env.signature->getPredicate(symbIdx);
    type = symbol->predType();
    break;
  }
  case SymbolType::TYPECON: {
    symbol = env.signature->getTypeCon(symbIdx);
    type = symbol->typeConType();
    break;
  }
  }

  unsigned numTypeArgs = type->numTypeArguments();
  unsigned arity = symbol->arity();

  static Stack<TermList> args;
  args.reset();

  Substitution subst;
  for (unsigned i = 0; i < arity; i++) {
    if (_results.isEmpty() || _results.top().isSeparator()) {
      complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
    }
    TermList arg;
    auto argSort = _results.pop().asTerm(arg);
    TermList sort;
    if (i < numTypeArgs) {
      // if the term has a parametric type, the parameters
      // are checked and saved to instantiate the concrete
      // types of later (non-type) arguments
      subst.bind(type->quantifiedVar(i).var(), arg);
      sort = type->arg(i);
    } else {
      sort = SubstHelper::apply(type->arg(i), subst);
    }

    if (sort != argSort) {
      complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
    }
    args.push(arg);
  }

  switch (sym.second)
  {
  case SymbolType::FUNCTION: {
    TermList res = TermList(Term::create(symbIdx,arity,args.begin()));
    TermList sort = SortHelper::getResultSort(res.term());
    _results.push(ParseResult(sort,res));
    break;
  }
  case SymbolType::TYPECON: {
    TermList res = TermList(AtomicSort::create(symbIdx,arity,args.begin()));
    TermList sort = SortHelper::getResultSort(res.term());
    _results.push(ParseResult(sort,res));
    break;
  }
  case SymbolType::PREDICATE: {
    Formula* res = new AtomicFormula(Literal::create(symbIdx,arity,true,false,args.begin()));
    _results.push(ParseResult(res));
    break;
  }
  }

  return true;
}

static const char* BUILT_IN_SYMBOL = "built-in symbol";

bool SMTLIB2::parseAsBuiltinFormulaSymbol(const vstring& id, LExpr* exp)
{
  CALL("SMTLIB2::parseAsBuiltinFormulaSymbol");

  FormulaSymbol fs = getBuiltInFormulaSymbol(id);
  switch (fs) {
    case FS_TRUE:
      _results.push(ParseResult(Formula::trueFormula()));
      return true;
    case FS_FALSE:
      _results.push(ParseResult(Formula::falseFormula()));
      return true;
    case FS_NOT:
    {
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      Formula* argFla;
      if (!(_results.pop().asFormula(argFla))) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      Formula* res = new NegatedFormula(argFla);
      _results.push(ParseResult(res));
      return true;
    }
    case FS_AND:
    case FS_OR:
    {
      FormulaList* argLst = nullptr;

      LOG1("FS_AND and FS_OR");

      unsigned argcnt = 0;
      while (_results.isNonEmpty() && (!_results.top().isSeparator())) {
        argcnt++;
        Formula* argFla;
        if (!(_results.pop().asFormula(argFla))) {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
        }
        FormulaList::push(argFla,argLst);
      }

      if (argcnt < 1) { // TODO: officially, we might want to disallow singleton AND and OR, but they are harmless and appear in smtlib
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      Formula* res;
      if (argcnt > 1) {
        res = new JunctionFormula( (fs==FS_AND) ? AND : OR, argLst);
      } else {
        res = argLst->head();
        FormulaList::destroy(argLst);
      }
      _results.push(ParseResult(res));

      return true;
    }
    case FS_IMPLIES: // done in a right-assoc multiple-argument fashion
    case FS_XOR: // they say XOR should be left-associative, but semantically, it does not matter
    {
      Connective con = (fs==FS_IMPLIES) ? IMP : XOR;

      static Stack<Formula*> args;
      ASS(args.isEmpty());

      // put argument formulas on stack (reverses the order)
      while (_results.isNonEmpty() && (!_results.top().isSeparator())) {
        Formula* argFla;
        if (!(_results.pop().asFormula(argFla))) {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
        }
        args.push(argFla);
      }

      if (args.size() < 2) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      // the last two go first
      Formula* arg_n = args.pop();
      Formula* arg_n_1 = args.pop();
      Formula* res = new BinaryFormula(con, arg_n_1, arg_n);

      // keep on adding in a right-assoc way
      while(args.isNonEmpty()) {
        res = new BinaryFormula(con, args.pop(), res);
      }

      _results.push(ParseResult(res));

      return true;
    }
    // all the following are "chainable" and need to respect sorts
    case FS_EQ:
    case FS_LESS:
    case FS_LESS_EQ:
    case FS_GREATER:
    case FS_GREATER_EQ:
    {
      // read the first two arguments
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      auto firstParseResult = _results.pop();
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      auto secondParseResult = _results.pop();
      if (firstParseResult.sort != secondParseResult.sort)
      {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      Formula* lastConjunct;
      unsigned pred = 0;
      if (fs == FS_EQ) {
        if (firstParseResult.formula && secondParseResult.formula) {
          Formula* first;
          Formula* second;
          firstParseResult.asFormula(first);
          secondParseResult.asFormula(second);
          lastConjunct = new BinaryFormula(IFF, first, second);
        } else {
          TermList first;
          TermList second;
          firstParseResult.asTerm(first);
          secondParseResult.asTerm(second);
          lastConjunct = new AtomicFormula(Literal::createEquality(true, first, second, firstParseResult.sort));
        }
      } else {
        Interpretation intp = getFormulaSymbolInterpretation(fs,firstParseResult.sort);
        pred = env.signature->getInterpretingSymbol(intp);
        TermList first;
        TermList second;
        firstParseResult.asTerm(first);
        secondParseResult.asTerm(second);
        lastConjunct = new AtomicFormula(Literal::create2(pred,true,first,second));
      }

      FormulaList* argLst = nullptr;
      // for every other argument ... pipelining
      while (_results.isEmpty() || !_results.top().isSeparator()) {
        auto nextParseResult = _results.pop();
        if (nextParseResult.sort != firstParseResult.sort) {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
        }
        // store the old conjunct
        FormulaList::push(lastConjunct,argLst);
        // shift the arguments
        firstParseResult = secondParseResult;
        secondParseResult = nextParseResult;
        // create next conjunct
        if (fs == FS_EQ) {
          if (firstParseResult.formula && secondParseResult.formula) {
            Formula* first;
            Formula* second;
            firstParseResult.asFormula(first);
            secondParseResult.asFormula(second);
            lastConjunct = new BinaryFormula(IFF, first, second);
          } else {
            TermList first;
            TermList second;
            firstParseResult.asTerm(first);
            secondParseResult.asTerm(second);
            lastConjunct = new AtomicFormula(Literal::createEquality(true, first, second, firstParseResult.sort));
          }
        } else {
          Interpretation intp = getFormulaSymbolInterpretation(fs,firstParseResult.sort);
          pred = env.signature->getInterpretingSymbol(intp);
          TermList first;
          TermList second;
          firstParseResult.asTerm(first);
          secondParseResult.asTerm(second);
          lastConjunct = new AtomicFormula(Literal::create2(pred,true,first,second));
        }
      }
      if (argLst == nullptr) { // there were only two arguments, let's return lastConjunct
        _results.push(lastConjunct);
      } else {
        // add the last lastConjunct created (pipelining)
        FormulaList::push(lastConjunct,argLst);
        // create the actual conjunction
        Formula* res = new JunctionFormula( AND, argLst);
        _results.push(ParseResult(res));
      }

      return true;
    }
    case FS_DISTINCT:
    {
      static Stack<TermList> args;
      args.reset();

      // read the first argument and its sort
      TermList first;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList sort = _results.pop().asTerm(first);

      args.push(first);

      // put remaining arguments on stack (reverses the order, which does not matter)
      while (_results.isNonEmpty() && (!_results.top().isSeparator())) {
        TermList argTerm;
        if (_results.pop().asTerm(argTerm) != sort) {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
        }
        args.push(argTerm);
      }

      if (args.size() < 2) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      Formula* res;
      if(args.size()==2) { // if there are 2 just create a disequality
        res = new AtomicFormula(Literal::createEquality(false,args[0],args[1],sort));
      } else { // Otherwise create a formula list of disequalities
        FormulaList* diseqs = nullptr;

        for(unsigned i=0;i<args.size();i++){
          for(unsigned j=0;j<i;j++){
            Formula* new_dis = new AtomicFormula(Literal::createEquality(false,args[i],args[j],sort));
            FormulaList::push(new_dis,diseqs);
          }
        }

        res = new JunctionFormula(AND, diseqs);
      }

      _results.push(res);

      return true;
    }
    case FS_IS_INT:
    {
      TermList arg;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(arg) != AtomicSort::realSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned pred = env.signature->getInterpretingSymbol(Theory::REAL_IS_INT);
      Formula* res = new AtomicFormula(Literal::create1(pred,true,arg));

      _results.push(res);

      return true;
    }
    case FS_EXISTS:
    case FS_FORALL:
    case FS_PAR:
    {
      Formula* argFla;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          !(_results.pop().asFormula(argFla))) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      VList* qvars = VList::empty();
      SList* qsorts = SList::empty();

      TermLookup::Iterator varIt(*_scopes.top());
      while(varIt.hasNext()) {
        SortedTerm vTerm = varIt.next();
        unsigned varIdx = vTerm.first.var();
        TermList sort = vTerm.second;
        VList::push(varIdx, qvars);
        SList::push(sort,qsorts);
      }
      delete _scopes.pop();

      Formula* res = new QuantifiedFormula((fs==FS_EXISTS) ? Kernel::EXISTS : Kernel::FORALL, qvars, qsorts, argFla);

      _results.push(ParseResult(res));
      return true;
    }

    default:
      ASS_EQ(fs,FS_USER_PRED_SYMBOL);
      return false;
  }
}

bool SMTLIB2::parseAsBuiltinTermSymbol(const vstring& id, LExpr* exp)
{
  CALL("SMTLIB2::parseAsBuiltinTermSymbol");

  // try built-in term symbols
  TermSymbol ts = getBuiltInTermSymbol(id);
  switch(ts) {
    case TS_ITE:
    {
      Formula* cond;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          !(_results.pop().asFormula(cond))) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList thenBranch;
      if (_results.isEmpty() || _results.top().isSeparator()){
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList sort = _results.pop().asTerm(thenBranch);
      TermList elseBranch;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(elseBranch) != sort){
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList res = TermList(Term::createITE(cond, thenBranch, elseBranch, sort));

      _results.push(ParseResult(sort,res));
      return true;
    }
    case TS_TO_REAL:
    {
      TermList theInt;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theInt) != AtomicSort::intSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_TO_REAL);
      TermList res = TermList(Term::create1(fun,theInt));

      _results.push(ParseResult(AtomicSort::realSort(),res));
      return true;
    }
    case TS_TO_INT:
    {
      TermList theReal;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theReal) != AtomicSort::realSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::REAL_TO_INT);
      TermList res = TermList(Term::create1(fun,theReal));

      _results.push(ParseResult(AtomicSort::intSort(),res));
      return true;
    }
    case TS_SELECT:
    {
      TermList theArray;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList arraySortIdx = _results.pop().asTerm(theArray);
      if (!arraySortIdx.isArraySort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList theIndex;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theIndex) != SortHelper::getIndexSort(arraySortIdx)) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      if (SortHelper::getInnerSort(arraySortIdx)== AtomicSort::boolSort()) {
        OperatorType* predType = Theory::getArrayOperatorType(arraySortIdx,Theory::ARRAY_BOOL_SELECT);
        unsigned pred = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,predType);

        Formula* res = new AtomicFormula(Literal::create2(pred,true,theArray,theIndex));

        _results.push(ParseResult(res));
      } else {
        OperatorType* funType = Theory::getArrayOperatorType(arraySortIdx,Theory::ARRAY_SELECT);
        unsigned fun = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,funType);

        TermList res = TermList(Term::create2(fun,theArray,theIndex));

        _results.push(ParseResult(SortHelper::getInnerSort(arraySortIdx),res));
      }

      return true;
    }
    case TS_STORE:
    {
      TermList theArray;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList arraySortIdx = _results.pop().asTerm(theArray);
      if (!arraySortIdx.isArraySort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList theIndex;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theIndex) != SortHelper::getIndexSort(arraySortIdx)) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList theValue;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theValue) != SortHelper::getInnerSort(arraySortIdx)) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      OperatorType* funType = Theory::getArrayOperatorType(arraySortIdx,Theory::ARRAY_STORE);
      unsigned fun = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,funType);

      TermList args[] = {theArray, theIndex, theValue};
      TermList res = TermList(Term::Term::create(fun, 3, args));

      _results.push(ParseResult(arraySortIdx,res));

      return true;
    }
    case TS_ABS:
    {
      TermList theInt;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theInt) != AtomicSort::intSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_ABS);
      TermList res = TermList(Term::create1(fun,theInt));

      _results.push(ParseResult(AtomicSort::intSort(),res));

      return true;
    }
    case TS_MOD:
    {
      TermList int1, int2;
      if (_results.isEmpty() || _results.top().isSeparator() || _results.pop().asTerm(int1) != AtomicSort::intSort() ||
          _results.isEmpty() || _results.top().isSeparator() || _results.pop().asTerm(int2) != AtomicSort::intSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_REMAINDER_E); // TS_MOD is the always positive remainder, therefore INT_REMAINDER_E
      TermList res = TermList(Term::create2(fun,int1,int2));

      _results.push(ParseResult(AtomicSort::intSort(),res));

      return true;
    }
    case TS_MULTIPLY:
    case TS_PLUS:
    case TS_MINUS:
    case TS_DIVIDE:
    case TS_DIV:
    {
      // read the first argument
      TermList first;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      TermList sort = _results.pop().asTerm(first);

      if (_results.isEmpty() || _results.top().isSeparator()) {
        if (ts == TS_MINUS) { // unary minus
          Interpretation intp = getUnaryMinusInterpretation(sort);
          unsigned fun = env.signature->getInterpretingSymbol(intp);

          TermList res = TermList(Term::create1(fun,first));

          _results.push(ParseResult(sort,res));

          return true;
        } else {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp); // we need at least two arguments otherwise
        }
      }

      Interpretation intp = getTermSymbolInterpretation(ts,sort);
      unsigned fun = env.signature->getInterpretingSymbol(intp);

      TermList second;
      if (_results.pop().asTerm(second) != sort) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList res = TermList(Term::create2(fun,first,second));
      while (_results.isNonEmpty() && !_results.top().isSeparator()) {
        TermList another;
        if (_results.pop().asTerm(another) != sort) {
          complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
        }

        res = TermList(Term::create2(fun,res,another));
      }
      _results.push(ParseResult(sort,res));

      return true;
    }
    case TS_ARRAY:
    {
      TermList indexSort;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      ALWAYS(_results.pop().asTerm(indexSort) == AtomicSort::superSort());
      TermList innerSort;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      ALWAYS(_results.pop().asTerm(innerSort) == AtomicSort::superSort());
      _results.push(ParseResult(AtomicSort::superSort(),AtomicSort::arraySort(indexSort, innerSort)));
      return true;
    }
    case TS_BOOL:
    {
      _results.push(ParseResult(AtomicSort::superSort(),AtomicSort::boolSort()));
      return true;
    }
    case TS_INT:
    {
      _results.push(ParseResult(AtomicSort::superSort(),AtomicSort::intSort()));
      return true;
    }
    case TS_REAL:
    {
      _results.push(ParseResult(AtomicSort::superSort(),AtomicSort::realSort()));
      return true;
    }
    default:
      ASS_EQ(ts,TS_USER_FUNCTION);
      return false;
  }
}

void SMTLIB2::parseRankedFunctionApplication(LExpr* exp)
{
  CALL("SMTLIB2::parseRankedFunctionApplication");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);
  LExpr* head = lRdr.readNext();
  ASS(head->isList());
  LispListReader headRdr(head);

  headRdr.acceptAtom(UNDERSCORE);

  if(headRdr.tryAcceptAtom("divisible")){

    const vstring& numeral = headRdr.readAtom();

    if (!StringUtils::isPositiveInteger(numeral)) {
      USER_ERROR_EXPR("Expected numeral as an argument of a ranked function in "+head->toString());
    }

    unsigned divisorSymb = TPTP::addIntegerConstant(numeral,_overflow,false);
    TermList divisorTerm = TermList(Term::createConstant(divisorSymb));

    TermList arg;
    if (_results.isEmpty() || _results.top().isSeparator() ||
        _results.pop().asTerm(arg) != AtomicSort::intSort()) {
      complainAboutArgShortageOrWrongSorts("ranked function symbol",exp);
    }

    unsigned pred = env.signature->getInterpretingSymbol(Theory::INT_DIVIDES);
    env.signature->recordDividesNvalue(divisorTerm);

    Formula* res = new AtomicFormula(Literal::create2(pred,true,divisorTerm,arg));

    _results.push(ParseResult(res));
  }
  else if(headRdr.tryAcceptAtom("is")){
    // discriminator predicate for term algebras
    const vstring& consName = headRdr.readAtom();

    if (_declaredSymbols.find(consName)) {
      DeclaredSymbol& s = _declaredSymbols.get(consName);
      if (s.second==SymbolType::FUNCTION) {
        TermAlgebraConstructor* c = env.signature->getTermAlgebraConstructor(s.first);
        if (c) /* else the symbol is not a TA constructor */ {
          TermList sort = c->rangeSort();
          TermList arg;
          if (_results.isEmpty() || _results.top().isSeparator()) {
            complainAboutArgShortageOrWrongSorts("ranked function symbol",exp);
          }
          TermList argSort = _results.pop().asTerm(arg);
          if (!TermList::sameTopFunctor(argSort, sort))
          {
            complainAboutArgShortageOrWrongSorts("ranked function symbol",exp);
          }
          TermStack args(c->numTypeArguments()+1);
          for (unsigned i = 0; i < argSort.term()->arity(); i++) {
            args.push(*argSort.term()->nthArgument(i));
          }
          args.push(arg);
          Formula* res = new AtomicFormula(Literal::create(c->discriminator(),args.size(),true,false,args.begin()));
          
          _results.push(ParseResult(res));
          return;
        }
      }
    }
    USER_ERROR_EXPR("'"+consName+"' is not a datatype constructor");
  }
  else{
    USER_ERROR_EXPR("Ranked function application "+headRdr.readAtom()+" not known");
  }
  
}

SMTLIB2::ParseResult SMTLIB2::parseTermOrFormula(LExpr* body, bool isSort)
{
  CALL("SMTLIB2::parseTermOrFormula");

  ASS(_todo.isEmpty());
  ASS(_results.isEmpty());

  _todo.push(make_pair(isSort?PO_PARSE_SORT:PO_PARSE,body));

  while (_todo.isNonEmpty()) {
    /*
    cout << "Results:" << endl;
    for (unsigned i = 0; i < results.size(); i++) {
      cout << results[i].toString() << endl;
    }
    cout << "---" << endl;
    */

    pair<ParseOperation,LExpr*> cur = _todo.pop();
    ParseOperation op = cur.first;
    LExpr* exp = cur.second;

    switch (op) {
      case PO_PARSE: {
        if (exp->isList()) {
          LispListReader lRdr(exp->list);

          // schedule arity check
          _results.push(ParseResult()); // separator into results
          _todo.push(make_pair(PO_CHECK_ARITY,exp)); // check as a todo (exp for error reporting)

          // special treatment of some tokens
          LExpr* fst = lRdr.readNext();
          if (fst->isAtom()) {
            vstring& id = fst->str;

            if (id == FORALL || id == EXISTS) {
              parseQuantBegin(exp);
              continue;
            }

            if (id == PAR) {
              parseParametric(exp);
              continue;
            }

            if (id == LET) {
              parseLetBegin(exp);
              continue;
            }

            if (id == MATCH) {
              parseMatchBegin(exp);
              continue;
            }

            if (id == EXCLAMATION) {
              parseAnnotatedTerm(exp);
              continue;
            }

            if (id == UNDERSCORE) {
              USER_ERROR_EXPR("Indexed identifiers in general term position are not supported: "+exp->toString());

              // we only support indexed identifiers as functors applied to something (see just below)
            }
          } else {
            // this has to be an UNDERSCORE, otherwise we error later when we PO_PARSE_APPLICATION
          }

          // this handles the general function-to-arguments application:

          _todo.push(make_pair(PO_PARSE_APPLICATION,exp));
          DeclaredSymbol sym;
          unsigned numTypeArgs = 0;
          if (fst->isAtom() && _declaredSymbols.find(fst->str,sym)) {
            ASS(sym.second != SymbolType::TYPECON);
            numTypeArgs = (sym.second == SymbolType::FUNCTION
              ? env.signature->getFunction(sym.first)->fnType()
              : env.signature->getPredicate(sym.first)->predType())
              ->numTypeArguments();
          }
          // and all the other arguments too
          unsigned i = 0;
          while (lRdr.hasNext()) {
            auto op = i++ < numTypeArgs ? PO_PARSE_SORT : PO_PARSE;
            _todo.push(make_pair(op,lRdr.next()));
          }

          continue;
        }

        // INTENTIONAL FALL-THROUGH FOR ATOMS
      }
      case PO_PARSE_APPLICATION: { // the arguments have already been parsed
        vstring id;
        if (exp->isAtom()) { // the fall-through case
          id = exp->str;
        } else {
          ASS(exp->isList());
          LispListReader lRdr(exp->list);

          LExpr* head = lRdr.readNext();

          if (head->isList()) {
            parseRankedFunctionApplication(exp);
            continue;
          }
          ASS(head->isAtom());
          id = head->str;
        }

        if (parseAsScopeLookup(id)) {
          continue;
        }

        if (parseAsSpecConstant(id)) {
          continue;
        }

        if (parseAsUserDefinedSymbol(id,exp,false/*isSort*/)) {
          continue;
        }

        if (parseAsBuiltinFormulaSymbol(id,exp)) {
          continue;
        }

        if (parseAsBuiltinTermSymbol(id,exp)) {
          continue;
        }

        USER_ERROR_EXPR("Unrecognized term identifier '"+id+"'");
      }
      case PO_PARSE_SORT: {
        if (exp->isList()) {
          LispListReader lRdr(exp->list);
          lRdr.readNext(); // the head

          // schedule arity check
          _results.push(ParseResult()); // separator into results
          _todo.push(make_pair(PO_CHECK_ARITY,exp)); // check as a todo (exp for error reporting)
          _todo.push(make_pair(PO_PARSE_SORT_APPLICATION,exp));
          while (lRdr.hasNext()) {
            _todo.push(make_pair(PO_PARSE_SORT,lRdr.next()));
          }

          continue;
        }
      }
      case PO_PARSE_SORT_APPLICATION: { // the arguments have already been parsed
        vstring id;
        if (exp->isAtom()) { // the fall-through case
          id = exp->str;
        } else {
          ASS(exp->isList());
          LispListReader lRdr(exp->list);

          LExpr* head = lRdr.readNext();
          ASS(head->isAtom());
          id = head->str;
        }

        if (parseAsScopeLookup(id)) {
          continue;
        }

        if (parseAsSortDefinition(id,exp)) {
          continue;
        }

        if (parseAsUserDefinedSymbol(id,exp,true/*isSort*/)) {
          continue;
        }

        if (parseAsBuiltinTermSymbol(id,exp)) {
          continue;
        }

        USER_ERROR_EXPR("Unrecognized term identifier '"+id+"'");
      }
      case PO_CHECK_ARITY: {
        LOG1("PO_CHECK_ARITY");

        ASS_GE(_results.size(),2);
        ParseResult true_result = _results.pop();
        ParseResult separator   = _results.pop();

        if (true_result.isSeparator() || !separator.isSeparator()) {
          USER_ERROR_EXPR("Too many arguments in '"+exp->toString()+"'");
        }
        _results.push(true_result);

        continue;
      }
      case PO_LABEL: {
        ASS_GE(_results.size(),1);
        ParseResult res =  _results.pop();
        vstring label = exp->toString();
        res.setLabel(label);
        _results.push(res);
        continue;
      }
      case PO_LET_PREPARE_LOOKUP:
        parseLetPrepareLookup(exp);
        continue;
      case PO_LET_END:
        parseLetEnd(exp);
        continue;
      case PO_MATCH_CASE_START: {
        parseMatchCaseStart(exp);
        continue;
      }
      case PO_MATCH_CASE_END: {
        parseMatchCaseEnd(exp);
        continue;
      }
      case PO_MATCH_END: {
        parseMatchEnd(exp);
        continue;
      }
      case PO_QUANT: {
        parseQuantEnd(exp);
        continue;
      }
      case PO_POP_LOOKUP: {
        delete _scopes.pop();
        continue;
      }
      default: {
        ASSERTION_VIOLATION;
      }
    }
  }

  if (_results.size() == 1) {
    return _results.pop();
  } else {
    USER_ERROR_EXPR("Malformed term expression "+body->toString());
  }
}

void SMTLIB2::readAssert(LExpr* body)
{
  CALL("SMTLIB2::readAssert");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));
  UnitList::push(fu, _formulas);
}

void SMTLIB2::readAssertNot(LExpr* body)
{
  CALL("SMTLIB2::readAssert");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::CONJECTURE));
  fu = new FormulaUnit(new NegatedFormula(fla),
                       FormulaTransformation(InferenceRule::NEGATED_CONJECTURE, fu));
  UnitList::push(fu, _formulas);
}

void SMTLIB2::readAssertTheory(LExpr* body)
{
  CALL("SMTLIB2::readAssertTheory");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* theoryAxiom;
  if (!res.asFormula(theoryAxiom)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(theoryAxiom, Inference(TheoryAxiom(InferenceRule::EXTERNAL_THEORY_AXIOM)));
  UnitList::push(fu, _formulas);
}

void SMTLIB2::colorSymbol(const vstring& name, Color color)
{
  CALL("SMTLIB2::colorSymbol");

  if (!_declaredSymbols.find(name)) {
    USER_ERROR_EXPR("'"+name+"' is not a user symbol");
  }
  DeclaredSymbol& s = _declaredSymbols.get(name);

  env.colorUsed = true;

  Signature::Symbol* sym = nullptr;
  switch (s.second)
  {
  case SymbolType::FUNCTION: {
    sym = env.signature->getFunction(s.first);
    break;
  }
  case SymbolType::PREDICATE: {
    sym = env.signature->getPredicate(s.first);
    break;
  }
  case SymbolType::TYPECON: {
    sym = env.signature->getTypeCon(s.first);
    break;
  }
  }

  sym->addColor(color);
}

}

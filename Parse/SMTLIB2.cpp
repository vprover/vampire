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

#include <map>

#include "Lib/Environment.hpp"
#include "Lib/NameArray.hpp"
#include "Lib/StringUtils.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"

#include "Shell/AnswerLiteralManager.hpp"
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

#define READER(exp) ErrorThrowingLispListReader(exp, _topLevelExpr)

namespace Parse {

using namespace std;

static const char* PAR = "par";

SMTLIB2::SMTLIB2(UnitList::FIFO formulaBuffer)
: _logicSet(false),
  _logic(SMTLIBLogic::UNDEFINED),
  _numeralsAreReal(false),
  _formulas(formulaBuffer),
  _topLevelExpr(nullptr)
{
}

void SMTLIB2::parse(istream& str)
{
  LispLexer lex(str);
  LispParser lpar(lex);
  LExpr* expr = lpar.parse();
  if (!expr->isList()) {
    USER_ERROR("Input file is not a list");
  }
  readBenchmark(expr);
}

void SMTLIB2::readBenchmark(LExpr* bench)
{
  auto bRdr = READER(bench);

  bool afterCheckSat = false;

  // iteration over benchmark top level entries
  while(bRdr.hasNext()) {
    _topLevelExpr = bRdr.readExpr();
    _nextVar = _globalSortParamLookup.size();

    ASS(_lookups.isEmpty());

    LOG2("readBenchmark ",_topLevelExpr->toString(true));

    auto ibRdr = READER(_topLevelExpr);

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

      auto name = ibRdr.readAtom();
      auto arity = ibRdr.readAtom();
      readDeclareSort(name,arity);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-sort-parameter")) {

      auto name = ibRdr.readAtom();
      // // We strictly disallow shadowing, as opposed to the standard
      if (isAlreadyKnownSort(name)) {
        USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort parameter: "+name);
      }
      ASS_EQ(_globalSortParamLookup.size(),_nextVar);
      ALWAYS(_globalSortParamLookup.insert(name, Binding {TermList::var(_nextVar++), AtomicSort::superSort()}));
      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-sort")) {

      auto name = ibRdr.readAtom();
      auto args = ibRdr.readList();
      auto body = ibRdr.readExpr();
      readDefineSort(name,args,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-fun")) {

      auto name = ibRdr.readAtom();
      auto iSorts = ibRdr.readList();
      auto oSort = ibRdr.readExpr();
      readDeclareFun(name,iSorts,oSort);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-datatype")) {

      auto sort = ibRdr.readAtom();
      auto datatype = ibRdr.readList();
      readDeclareDatatype(sort, datatype);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-datatypes")) {
  
      auto sorts = ibRdr.readList();
      auto datatypes = ibRdr.readList();
      readDeclareDatatypes(sorts, datatypes, false);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-codatatypes")) {
  
      auto sorts = ibRdr.readList();
      auto datatypes = ibRdr.readList();
      readDeclareDatatypes(sorts, datatypes, true);

      ibRdr.acceptEOL();

      continue;
    }
    
    if (ibRdr.tryAcceptAtom("declare-const")) {

      auto name = ibRdr.readAtom();
      auto oSort = ibRdr.readExpr();
      LExpr iArgs(LispParser::LIST); // dummy list to avoid passing null below
      readDeclareFun(name,&iArgs,oSort);

      ibRdr.acceptEOL();

      continue;
    }

    bool recursive = false;
    if (ibRdr.tryAcceptAtom("define-fun") || (recursive = ibRdr.tryAcceptAtom("define-fun-rec"))) {

      auto name = ibRdr.readAtom();
      auto iArgs = ibRdr.readList();
      auto oSort = ibRdr.readExpr();
      auto body = ibRdr.readExpr();
      readDefineFun(name,iArgs,oSort,body,recursive);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-funs-rec")) {

      auto declarations = ibRdr.readList();
      auto definitions = ibRdr.readList();
      // TODO make this work with sort parameters
      readDefineFunsRec(declarations, definitions);

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert")) {

      auto body = ibRdr.readExpr();
      readAssert(body);
      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-claim")) {

      auto body = ibRdr.readExpr();
      readAssertClaim(body);
      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-not")) {

      auto body = ibRdr.readExpr();
      readAssertNot(body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-synth")) {

      auto forall = ibRdr.readList();
      auto exist = ibRdr.readList();
      auto body = ibRdr.readExpr();
      readAssertSynth(forall, exist, body);

      ibRdr.acceptEOL();

      continue;
    }

    // not an official SMTLIB command
    if (ibRdr.tryAcceptAtom("color-symbol")) {

      auto symbol = ibRdr.readAtom();

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
      if (ibRdr.tryAcceptAtom(":uncomputable")) {
        auto uRdr = READER(ibRdr.readList());
        while (uRdr.hasNext()) {
          markSymbolUncomputable(uRdr.readAtom());
        }
        ibRdr.acceptEOL();
        continue;
      }
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
      auto ibRdr = READER(bRdr.readExpr());
      
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
        std::cout << "% Warning: check-sat is not the last entry. Skipping the rest!" << endl;
      }
      break;
    }
  }
}

//  ----------------------------------------------------------------------

#define X(N) #N,
const char * SMTLIB2::s_smtlibLogicNameStrings[] = {
  SMTLIBLogic_X
};
#undef X

SMTLIBLogic SMTLIB2::getLogicFromString(const std::string& str)
{
  static NameArray smtlibLogicNames(s_smtlibLogicNameStrings, sizeof(s_smtlibLogicNameStrings)/sizeof(char*));
  int res = smtlibLogicNames.tryToFind(str.c_str());
  if(res==-1) {
    return SMTLIBLogic::UNDEFINED;
  }
  return static_cast<SMTLIBLogic>(res);
}

void SMTLIB2::readLogic(const std::string& logicStr)
{
  _logic = getLogicFromString(logicStr);
  _logicSet = true;

  switch (_logic) {
  case SMTLIBLogic::ALL:
  case SMTLIBLogic::ALIA:
  case SMTLIBLogic::ANIA:
  case SMTLIBLogic::AUFDTLIA:
  case SMTLIBLogic::AUFDTLIRA:
  case SMTLIBLogic::AUFDTNIRA:
  case SMTLIBLogic::AUFLIA:
  case SMTLIBLogic::AUFNIA:
  case SMTLIBLogic::AUFLIRA:
  case SMTLIBLogic::AUFNIRA:
  case SMTLIBLogic::LIA:
  case SMTLIBLogic::NIA:
  case SMTLIBLogic::QF_ALIA:
  case SMTLIBLogic::QF_ANIA:
  case SMTLIBLogic::QF_AUFLIA:
  case SMTLIBLogic::QF_AUFNIA:
  case SMTLIBLogic::QF_AX:
  case SMTLIBLogic::QF_IDL:
  case SMTLIBLogic::QF_LIA:
  case SMTLIBLogic::QF_LIRA:
  case SMTLIBLogic::QF_NIA:
  case SMTLIBLogic::QF_NIRA:
  case SMTLIBLogic::QF_UF:
  case SMTLIBLogic::QF_UFIDL:
  case SMTLIBLogic::QF_UFLIA:
  case SMTLIBLogic::QF_UFNIA:
  case SMTLIBLogic::UF:
  case SMTLIBLogic::UFDT:
  case SMTLIBLogic::UFDTLIA:
  case SMTLIBLogic::UFDTLIRA:
  case SMTLIBLogic::UFDTNIA:
  case SMTLIBLogic::UFDTNIRA:
  case SMTLIBLogic::UFIDL:
  case SMTLIBLogic::UFLIA:
  case SMTLIBLogic::UFNIA:
    break;

  // pure real arithmetic theories treat decimals as Real constants
  case SMTLIBLogic::LRA:
  case SMTLIBLogic::NRA:
  case SMTLIBLogic::QF_LRA:
  case SMTLIBLogic::QF_NRA:
  case SMTLIBLogic::QF_RDL:
  case SMTLIBLogic::QF_UFLRA:
  case SMTLIBLogic::QF_UFNRA:
  case SMTLIBLogic::UFLRA:
    _numeralsAreReal = true;
    break;

  // we don't support bit vectors
  case SMTLIBLogic::BV:
  case SMTLIBLogic::QF_ABV:
  case SMTLIBLogic::QF_AUFBV:
  case SMTLIBLogic::QF_BV:
  case SMTLIBLogic::QF_UFBV:
  case SMTLIBLogic::UFBV:
    USER_ERROR_EXPR("unsupported logic "+logicStr);
  case SMTLIBLogic::UNDEFINED:
    if (env.options->ignoreUnrecognizedLogic()) {
      break;
    } else {
      USER_ERROR_EXPR("unrecognized logic " + logicStr + " ( use `--ignore_unrecognized_logic on` if you want vampire to try proof search anyways)");
    }
  }

}

//  ----------------------------------------------------------------------

void SMTLIB2::readDeclareSort(const std::string& name, const std::string& arity)
{
  std::string pName = name;
  if (isAlreadyKnownSort(pName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  if (not StringUtils::isPositiveInteger(arity)) {
    USER_ERROR_EXPR("Unrecognized declared sort arity: "+arity);
  }

  unsigned val;
  if (!Int::stringToUnsignedInt(arity, val)) {
    USER_ERROR_EXPR("Couldn't convert sort arity: "+arity);
  }

  declareTypeCon(pName, val);
}

void SMTLIB2::readDefineSort(const std::string& name, LExpr* args, LExpr* body)
{
  std::string pName = name;
  if (isAlreadyKnownSort(pName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  _lookups.emplace();
  // sort definitions cannot contain global sort
  // parameters, so we use normalized variables
  unsigned var = 0;
  auto argRdr = READER(args);
  while (argRdr.hasNext()) {
    tryInsertIntoCurrentLookup(argRdr.readAtom(), TermList::var(var++), AtomicSort::superSort());
  }
  ALWAYS(_sortDefinitions.insert(pName, { var, parseSort(body) }));
  _lookups.pop();
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

TermStack SMTLIB2::normalizeFunctionSorts(TermStack& argSorts, TermList& resSort)
{
  DHSet<TermList> varsSeen;
  for (auto sort : argSorts) {
    varsSeen.loadFromIterator(VariableIterator(sort));
  }
  varsSeen.loadFromIterator(VariableIterator(resSort));

  TermStack vars;
  vars.loadFromIterator(varsSeen.iter());

  SortHelper::normaliseArgSorts(vars, argSorts);
  SortHelper::normaliseSort(vars, resSort);

  return vars;
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
    "true",
    "xor"
};

SMTLIB2::FormulaSymbol SMTLIB2::getBuiltInFormulaSymbol(const std::string& str)
{
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
static const char* AS = "as";

const char * SMTLIB2::s_termSymbolNameStrings[] = {
    "*",
    "+",
    "-",
    "/",
    "abs",
    AS,
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

SMTLIB2::TermSymbol SMTLIB2::getBuiltInTermSymbol(const std::string& str)
{
  static NameArray termSymbolNames(s_termSymbolNameStrings, sizeof(s_termSymbolNameStrings)/sizeof(char*));
  ASS_EQ(termSymbolNames.length, TS_USER_FUNCTION);

  int resInt = termSymbolNames.tryToFind(str.c_str());
  if(resInt==-1) {
    return TS_USER_FUNCTION;
  }
  return static_cast<TermSymbol>(resInt);
}

const char *SMTLIB2::s_typeSymbolNameStrings[] = {
    "Array",
    "Bool",
    "Int",
    "Real",
};

SMTLIB2::TypeSymbol SMTLIB2::getBuiltInTypeSymbol(const std::string& str)
{
  static NameArray typeSymbolNames(s_typeSymbolNameStrings, sizeof(s_typeSymbolNameStrings)/sizeof(char*));
  ASS_EQ(typeSymbolNames.length, TS_USER_TYPE);

  int resInt = typeSymbolNames.tryToFind(str.c_str());
  if(resInt==-1) {
    return TS_USER_TYPE;
  }
  return static_cast<TypeSymbol>(resInt);
}



bool SMTLIB2::isAlreadyKnownFunction(const std::string& name)
{
  if (getBuiltInFormulaSymbol(name) != FS_USER_PRED_SYMBOL) {
    return true;
  }

  if (getBuiltInTermSymbol(name) != TS_USER_FUNCTION) {
    return true;
  }

  if(_declaredSymbols.find(name)) {
    return true;
  }

  return false;
}

bool SMTLIB2::isAlreadyKnownSort(const std::string& name)
{
  if (getBuiltInTypeSymbol(name) != TS_USER_TYPE) {
    return true;
  }

  if(_declaredSorts.find(name)) {
    return true;
  }

  // We strictly disallow shadowing, as opposed to the standard
  if (_globalSortParamLookup.find(name)) {
    return true;
  }

  return false;
}


void SMTLIB2::readDeclareFun(const std::string& name, LExpr* iSorts, LExpr* oSort)
{
  if (isAlreadyKnownFunction(name)) {
    USER_ERROR_EXPR("Redeclaring function symbol: "+name);
  }

  TermList rangeSort = parseSort(oSort);

  auto isRdr = READER(iSorts);

  static TermStack argSorts;
  argSorts.reset();

  while (isRdr.hasNext()) {
    argSorts.push(parseSort(isRdr.readExpr()));
  }

  auto taArity = normalizeFunctionSorts(argSorts, rangeSort).size();

  declareFunctionOrPredicate(name,rangeSort,argSorts,taArity);
}

SMTLIB2::DeclaredSymbol SMTLIB2::declareFunctionOrPredicate(const std::string& name, TermList rangeSort, const TermStack& argSorts, unsigned taArity)
{
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
      symNum = TPTP::addUninterpretedConstant(name,added);
    }

    sym = env.signature->getFunction(symNum);

    type = OperatorType::getFunctionType(argSorts.size(), argSorts.begin(), rangeSort, taArity);

    LOG1("declareFunctionOrPredicate-Function");
  }

  ASS(added);
  sym->setType(type);

  DeclaredSymbol res = make_pair(symNum,!type->isFunctionType());

  LOG2("declareFunctionOrPredicate -name ",name);
  LOG2("declareFunctionOrPredicate -symNum ",symNum);
  LOG2("declareFunctionOrPredicate -type ",type->toString());

  ALWAYS(_declaredSymbols.insert(name,res));

  return res;
}

unsigned SMTLIB2::declareTypeCon(const std::string& name, unsigned arity)
{
  bool added = false;
  auto symNum = env.signature->addTypeCon(name, arity, added);
  ASS(added);

  auto type = OperatorType::getTypeConType(arity);
  env.signature->getTypeCon(symNum)->setType(type);

  LOG2("declareTypeCon -name ",name);
  LOG2("declareTypeCon -symNum ",symNum);
  LOG2("declareTypeCon -type ",type->toString());

  ALWAYS(_declaredSorts.insert(name, symNum));
  return symNum;
}

//  ----------------------------------------------------------------------

void SMTLIB2::readDefineFun(const std::string& name, LExpr* iArgs, LExpr* oSort, LExpr* body, bool recursive)
{
  if (isAlreadyKnownFunction(name)) {
    USER_ERROR_EXPR("Redeclaring function symbol: "+name);
  }

  TermList rangeSort = parseSort(oSort);

  _lookups.emplace();

  static TermStack argSorts;
  argSorts.reset();

  static TermStack termArgs;
  termArgs.reset();

  auto iaRdr = READER(iArgs);
  while (iaRdr.hasNext()) {
    auto pRdr = READER(iaRdr.readList());

    auto vName = pRdr.readAtom();
    TermList vSort = parseSort(pRdr.readExpr());

    pRdr.acceptEOL();

    TermList arg = TermList::var(_nextVar++);
    termArgs.push(arg);

    tryInsertIntoCurrentLookup(vName, arg, vSort);

    argSorts.push(vSort);
  }

  auto nRangeSort = rangeSort;
  auto typeVars = normalizeFunctionSorts(argSorts, nRangeSort);

  DeclaredSymbol fun;
  if (recursive) {
    fun = declareFunctionOrPredicate(name, nRangeSort, argSorts, typeVars.size());
  }

  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  _lookups.pop();

  TermList rhs;
  if (res.asTerm(rhs) != rangeSort) {
    USER_ERROR_EXPR("Defined function body "+body->toString()+" has different sort than declared "+oSort->toString());
  }

  if (!recursive) {
    fun = declareFunctionOrPredicate(name, nRangeSort, argSorts, typeVars.size());
  }

  unsigned symbIdx = fun.first;
  bool isTrueFun = !fun.second;

  TermStack args = typeVars;
  args.loadFromIterator(TermStack::BottomFirstIterator(termArgs));

  Literal* lit;
  Signature::Symbol* sym;
  if (isTrueFun) {
    sym = env.signature->getFunction(symbIdx);

    TermList lhs(Term::create(symbIdx,args.size(),args.begin()));
    auto p = env.signature->getFnDef(symbIdx);
    auto defArgs = typeVars;
    defArgs.push(lhs);
    defArgs.push(rhs);
    lit = Literal::create(p,defArgs.size(),true,defArgs.begin());
  } else {
    sym = env.signature->getPredicate(symbIdx);

    auto p = env.signature->getBoolDef(symbIdx);
    TermList lhs(Term::createFormula(new AtomicFormula(Literal::create(p,args.size(),true,args.begin()))));
    lit = Literal::createEquality(true, lhs, rhs, rangeSort);
  }
  Formula* fla = new AtomicFormula(lit);

  // Mark original symbol protected to avoid
  // erroneous unused symbol elimination later.
  // TODO find a better way to do this
  sym->markProtected();

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));

  _formulas.pushBack(fu);
}

void SMTLIB2::readDefineFunsRec(LExpr* declsExpr, LExpr* defsExpr)
{
  struct Declaration {
    DeclaredSymbol sym;
    Lookup lookup;
    TermList rangeSort;
    TermStack args;
  };
  Stack<Declaration> declarations;

  // first, declare all symbols
  auto declsRdr = READER(declsExpr);
  while (declsRdr.hasNext()) {
    Declaration decl;
    auto declRdr = READER(declsRdr.readList());
    auto name = declRdr.readAtom();
    if (isAlreadyKnownFunction(name)) {
      USER_ERROR_EXPR("Redeclaring function symbol: "+name);
    }
    auto iArgs = declRdr.readList();

    static TermStack argSorts;
    argSorts.reset();

    auto iaRdr = READER(iArgs);
    while (iaRdr.hasNext()) {
      auto pRdr = READER(iaRdr.readList());

      auto vName = pRdr.readAtom();
      TermList vSort = parseSort(pRdr.readExpr());

      pRdr.acceptEOL();

      // the vars need not be fresh across multiple definition, but it does not hurt
      TermList arg = TermList::var(_nextVar++);
      decl.args.push(arg);

      if (!decl.lookup.insert(vName, Binding {arg, vSort})) {
        USER_ERROR_EXPR("Multiple occurrence of variable "+vName+" in the definition of function "+name);
      }

      argSorts.push(vSort);
    }
    decl.rangeSort = parseSort(declRdr.readExpr());
    decl.sym = declareFunctionOrPredicate(name, decl.rangeSort, argSorts, /*taArity=*/ 0);

    declarations.push(std::move(decl));
  }

  // then, read all definitions
  auto defsRdr = READER(defsExpr);
  for (auto &decl : declarations) {
    auto def = defsRdr.readExpr();
    _lookups.push(std::move(decl.lookup));
    ParseResult res = parseTermOrFormula(def,false/*isSort*/);

    TermList rhs;
    if (res.asTerm(rhs) != decl.rangeSort) {
      USER_ERROR_EXPR("Defined function body "+def->toString()+" has different sort than declared "+decl.rangeSort.toString());
    }

    unsigned symbIdx = decl.sym.first;
    bool isTrueFun = !decl.sym.second;

    Literal* lit;
    Signature::Symbol* sym;
    if (isTrueFun) {
      sym = env.signature->getFunction(symbIdx);

      TermList lhs(Term::create(symbIdx,decl.args.size(),decl.args.begin()));
      auto p = env.signature->getFnDef(symbIdx);
      TermStack defArgs; // no type arguments (yet) in this case
      defArgs.push(lhs);
      defArgs.push(rhs);
      lit = Literal::create(p,defArgs.size(),true,defArgs.begin());
    } else {
      sym = env.signature->getPredicate(symbIdx);

      auto p = env.signature->getBoolDef(symbIdx);
      TermList lhs(Term::createFormula(new AtomicFormula(Literal::create(p,decl.args.size(),true,decl.args.begin()))));
      lit = Literal::createEquality(true, lhs, rhs, decl.rangeSort);
    }
    Formula* fla = new AtomicFormula(lit);

    // Mark original symbol protected to avoid
    // erroneous unused symbol elimination later.
    // TODO find a better way to do this
    sym->markProtected();

    FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));
    _formulas.pushBack(fu);

    _lookups.pop();
  }
  defsRdr.acceptEOL();
}

void SMTLIB2::readTypeParameters(ErrorThrowingLispListReader& rdr, TermStack& ts)
{
  auto parRdr = READER(rdr.readList());
  while (parRdr.hasNext()) {
    auto sortVar = TermList::var(_nextVar++);
    tryInsertIntoCurrentLookup(parRdr.readAtom(), sortVar, AtomicSort::superSort());
    ts.push(sortVar);
  }
}

void SMTLIB2::readDeclareDatatype(string name, LExpr *datatype)
{
  // first declare the sort
  std::string dtypeName = name;
  if (isAlreadyKnownSort(dtypeName)) {
    USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol as datatype: " + dtypeName);
  }
  auto dtypeRdr = READER(datatype);
  _lookups.emplace();
  TermStack parSorts;
  if (dtypeRdr.tryAcceptAtom(PAR)) {
    readTypeParameters(dtypeRdr, parSorts);
    auto rest = dtypeRdr.readList();
    dtypeRdr.acceptEOL();
    dtypeRdr = READER(rest);
  }
  auto srt = declareTypeCon(dtypeName,parSorts.size());

  TermList taSort(AtomicSort::create(srt,parSorts.size(),parSorts.begin()));

  // Due to global sort variables, the parsed variables
  // are not necessary normalized, so we normalize them
  Renaming r;
  r.normalizeVariables(taSort);
  taSort = r.apply(taSort);

  Stack<TermAlgebraConstructor *> constructors;
  TermStack argSorts;
  Stack<std::string> destructorNames;

  while (dtypeRdr.hasNext()) {
    argSorts.reset();
    destructorNames.reset();
    // read each constructor declaration
    auto constrRdr = READER(dtypeRdr.readList());
    auto ctorName = constrRdr.readAtom();

    while (constrRdr.hasNext()) {
      auto argRdr = READER(constrRdr.readList());
      destructorNames.push(argRdr.readAtom());
      argSorts.push(r.apply(parseSort(argRdr.readExpr())));
      argRdr.acceptEOL();
    }
    constructors.push(buildTermAlgebraConstructor(ctorName, taSort, destructorNames, argSorts));
  }
  _lookups.pop();

  ASS(!env.signature->isTermAlgebraSort(taSort));
  auto ta = new TermAlgebra(taSort, constructors.size(), constructors.begin(), false);

  if (ta->emptyDomain()) {
    USER_ERROR_EXPR("Datatype " + dtypeName + " defines an empty sort");
  }

  env.signature->addTermAlgebra(ta);
}

void SMTLIB2::readDeclareDatatypes(LExpr* sorts, LExpr* datatypes, bool codatatype)
{
  // first declare all the sorts, and then only the constructors, in
  // order to allow mutually recursive datatype definitions
  auto dtypesNamesRdr = READER(sorts);
  Stack<unsigned> dtypeFns;
  while (dtypesNamesRdr.hasNext()) {
    auto dtypeNRdr = READER(dtypesNamesRdr.readList());

    auto dtypeName = dtypeNRdr.readAtom();
    if (isAlreadyKnownSort(dtypeName)) {
      USER_ERROR_EXPR("Redeclaring built-in, declared or defined sort symbol as datatype: "+dtypeName);
    }
    unsigned arity;
    if (!Int::stringToUnsignedInt(dtypeNRdr.readAtom(),arity)) {
      USER_ERROR_EXPR("datatype arity not given");
    }
    dtypeFns.push(declareTypeCon(dtypeName,arity));
  }

  Stack<TermAlgebraConstructor*> constructors;
  TermStack argSorts;
  Stack<string> destructorNames;

  auto dtypesDefsRdr = READER(datatypes);
  Stack<unsigned>::BottomFirstIterator dtypeFnIter(dtypeFns);
  while(dtypeFnIter.hasNext()) {
    constructors.reset();

    auto fn = dtypeFnIter.next();
    auto sym = env.signature->getTypeCon(fn);

    LOG4("reading datatype ",sym->name()," of type ",sym->typeConType()->toString());

    _lookups.emplace();
    TermStack parSorts;
    auto dtypeRdr = READER(dtypesDefsRdr.readList());
    if (dtypeRdr.tryAcceptAtom(PAR)) {
      readTypeParameters(dtypeRdr, parSorts);
      auto rest = dtypeRdr.readList();
      dtypeRdr.acceptEOL();
      dtypeRdr = READER(rest);
    }
    if (parSorts.size() != sym->arity()) {
      USER_ERROR_EXPR("'par' block for datatype "+sym->name()+" should define "+Int::toString(sym->arity())+" arguments");
    }

    TermList taSort(AtomicSort::create(fn,parSorts.size(),parSorts.begin()));

    // Due to global sort variables, the parsed variables
    // are not necessary normalized, so we normalize them
    Renaming r;
    r.normalizeVariables(taSort);
    taSort = r.apply(taSort);
  
    while (dtypeRdr.hasNext()) {
      argSorts.reset();
      destructorNames.reset();
      // read each constructor declaration
      std::string constrName;
      auto constr = dtypeRdr.readExpr();
      if (constr->isAtom()) {
        // atom, constructor of arity 0
        constrName = constr->str;
      } else {
        ASS(constr->isList());
        auto constrRdr = READER(constr);
        constrName = constrRdr.readAtom();

        while (constrRdr.hasNext()) {
          auto arg = constrRdr.readList();
          auto argRdr = READER(arg);
          destructorNames.push(argRdr.readAtom());
          argSorts.push(r.apply(parseSort(argRdr.readExpr())));
          argRdr.acceptEOL();
        }
      }
      constructors.push(buildTermAlgebraConstructor(constrName, taSort, destructorNames, argSorts));
    }
    _lookups.pop();

    ASS(!env.signature->isTermAlgebraSort(taSort));
    TermAlgebra* ta = new TermAlgebra(taSort, constructors.size(), constructors.begin(), codatatype);

    if (ta->emptyDomain()) {
      USER_ERROR_EXPR("Datatype " + taSort.toString() + " defines an empty sort");
    }

    env.signature->addTermAlgebra(ta);
  }
}

TermAlgebraConstructor* SMTLIB2::buildTermAlgebraConstructor(std::string constrName, TermList taSort,
                                                             Stack<std::string> destructorNames, TermStack argSorts) {
  if (isAlreadyKnownFunction(constrName)) {
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

  ALWAYS(_declaredSymbols.insert(constrName, make_pair(functor, false)));

  Lib::Array<unsigned> destructorFunctors(arity);
  for (unsigned i = 0; i < arity; i++) {
    std::string destructorName = destructorNames[i];
    TermList destructorSort = argSorts[i];

    if (isAlreadyKnownFunction(destructorName)) {
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

    ALWAYS(_declaredSymbols.insert(destructorName, make_pair(destructorFunctor, isPredicate)));

    destructorFunctors[i] = destructorFunctor;
  }

  return new TermAlgebraConstructor(functor, destructorFunctors);
}

bool SMTLIB2::ParseResult::asFormula(Formula*& resFrm)
{
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

std::string SMTLIB2::ParseResult::toString()
{
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
  USER_ERROR_EXPR("invalid sort "+ firstArgSort.toString() +" for interpretation "+std::string(s_formulaSymbolNameStrings[fs]));
}

Interpretation SMTLIB2::getUnaryMinusInterpretation(TermList argSort)
{
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
    USER_ERROR_EXPR("invalid sort "+firstArgSort.toString()+" for interpretation "+std::string(s_termSymbolNameStrings[ts]));
}

void SMTLIB2::tryInsertIntoCurrentLookup(std::string name, TermList term, TermList sort)
{
  auto &lookup = _lookups.top();
  Binding binding {term, sort};
  if (!lookup.insert(name, binding)) {
    USER_ERROR_EXPR("Identifier '" + name + "' has already been defined in current lookup");
  }
}

void SMTLIB2::complainAboutArgShortageOrWrongSorts(const std::string& symbolClass, LExpr* exp)
{
  USER_ERROR("Not enough arguments or wrong sorts at " + exp->getPosition() + "\n" + _topLevelExpr->highlightSubexpression(exp));
}

void SMTLIB2::parseLetBegin(LExpr* exp)
{
  LOG2("parseLetBegin  ",exp->toString());

  auto lRdr = READER(exp);

  // the let atom
  ALWAYS(lRdr.tryAcceptAtom(LET));

  // now, there should be a list of bindings
  auto bindings = lRdr.readList();
  // and the actual body term
  auto body = lRdr.readExpr();
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
  auto bindRdr = READER(bindings);
  while (bindRdr.hasNext()) {
    auto pRdr = READER(bindRdr.readList());
    pRdr.readAtom(); // for now ignore the identifier
    _todo.push(make_pair(PO_PARSE,pRdr.readExpr())); // just parse the expression
    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseLetPrepareLookup(LExpr* exp)
{
  LOG2("PO_LET_PREPARE_LOOKUP",exp->toString());

  // so we know it is let
  auto lRdr = READER(exp);
  ALWAYS(lRdr.readAtom() == LET);

  // with a list of bindings
  auto bindRdr = READER(lRdr.readList());

  // corresponding results have already been parsed
  ParseResult* boundExprs = _results.end();

  _lookups.emplace();

  while (bindRdr.hasNext()) {
    auto pRdr = READER(bindRdr.readList());

    const std::string& cName = pRdr.readAtom();
    ParseResult* pr = (--boundExprs);
    TermList t;
    TermList sort = pr->asTerm(t);

    // If we have a binding (S,T) with a variable T, we just
    // replace S with T while parsing, to avoid issues later
    // from expecting T to be a term.
    if (t.isVar()) {
      tryInsertIntoCurrentLookup(cName, t, sort);
      continue;
    }

    ASS(t.isTerm());
    DHMap<unsigned,TermList> vs;
    SortHelper::collectVariableSorts(t.term(),vs);
    TermStack args;
    TermStack varSorts;
    VList::FIFO typeVars;
    // type vars are before term vars in the args list, so process them first
    iterTraits(vs.items())
      .forEach([&typeVars,&args](std::pair<unsigned,TermList> kv) {
        if (kv.second != AtomicSort::superSort()) {
          return;
        }
        typeVars.pushBack(kv.first);
        args.push(TermList::var(kv.first));
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
        args.push(TermList::var(kv.first));
      });
    SortHelper::normaliseArgSorts(typeVars.list(),varSorts);

    TermList trm;
    if (sort == AtomicSort::boolSort()) {
      unsigned symb = env.signature->addFreshPredicate(args.size(),"sLP");
      OperatorType* type = OperatorType::getPredicateType(varSorts.size(), varSorts.begin(), args.size()-varSorts.size());
      env.signature->getPredicate(symb)->setType(type);

      Formula* atom = new AtomicFormula(Literal::create(symb,args.size(),true,args.begin()));
      trm = TermList(Term::createFormula(atom));
    } else {
      TermList nSort = sort;
      SortHelper::normaliseSort(typeVars.list(),nSort);
      unsigned symb = env.signature->addFreshFunction (args.size(),"sLF");
      OperatorType* type = OperatorType::getFunctionType(varSorts.size(), varSorts.begin(), nSort, args.size()-varSorts.size());
      env.signature->getFunction(symb)->setType(type);

      trm = TermList(Term::create(symb,args.size(),args.begin()));
    }

    tryInsertIntoCurrentLookup(cName, trm, sort);
    VList::destroy(typeVars.list());
  }
}

void SMTLIB2::parseLetEnd(LExpr* exp)
{
  LOG2("PO_LET_END ",exp->toString());

  // so we know it is let
  auto lRdr = READER(exp);
  DEBUG_CODE(const std::string& theLetAtom =) lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theLetAtom),TS_LET);

  // with a list of bindings
  auto bindRdr = READER(lRdr.readList());

  const auto& lookup = _lookups.top();

  // there has to be the body result:
  TermList let;
  TermList letSort = _results.pop().asTerm(let);

  LOG2("LET body  ",let.toString());

  while (bindRdr.hasNext()) {
    auto pRdr = READER(bindRdr.readList());

    const std::string& cName = pRdr.readAtom();
    TermList boundExpr;
    _results.pop().asTerm(boundExpr);

    LOG2("BOUND name  ",cName);
    LOG2("BOUND term  ",boundExpr.toString());

    auto [exprTerm, exprSort] = lookup.get(cName);

    // We have already substituted bound variables during parsing.
    // See `parseLetPrepareLookup`.
    if (exprTerm.isVar()) {
      ASS(boundExpr.isVar());
      continue;
    }

    ASS(exprTerm.isTerm());
    auto exprT = exprTerm.term();
    if (exprSort == AtomicSort::boolSort()) { // it has to be formula term, with atomic formula
      exprT = exprT->getSpecialData()->getFormula()->literal();
    }

    VList::FIFO vars;
    Substitution subst;
    for (unsigned i = 0; i < exprT->arity(); i++) {
      subst.bindUnbound(exprT->nthArgument(i)->var(),TermList::var(_nextVar));
      vars.pushBack(_nextVar++);
    }

    auto varList = vars.list();
    auto args = TermStack::fromIterator(iterTraits(varList->iter()).map(unsignedToVarFn));
    auto binder = Formula::createDefinition(Term::create(exprT->functor(), args), SubstHelper::apply(boundExpr,subst), varList);
    let = TermList(Term::createLet(binder, let, letSort));
  }

  _results.push(ParseResult(letSort,let));
  _lookups.pop();
}

static const char *UNDERSCORE = "_";

bool SMTLIB2::isTermAlgebraConstructor(const std::string &name)
{
  if (_declaredSymbols.find(name)) {
    DeclaredSymbol &s = _declaredSymbols.get(name);
    return (!s.second && env.signature->getTermAlgebraConstructor(s.first));
  }

  return false;
}

void SMTLIB2::parseMatchBegin(LExpr *exp)
{
  LOG2("parseMatchBegin  ", exp->toString());

  auto lRdr = READER(exp);

  // the match atom
  ALWAYS(lRdr.tryAcceptAtom(MATCH));

  // next is the matched term
  auto matchedAtom = lRdr.readExpr();

  // and the list of cases
  auto casesRdr = READER(lRdr.readList());

  lRdr.acceptEOL();

  _todo.push(make_pair(PO_MATCH_END, exp));
  // this is the last thing we parse so that it pops
  // first when the result is created
  _todo.push(make_pair(PO_PARSE, matchedAtom));

  while (casesRdr.hasNext()) {
    auto caseExp = casesRdr.readExpr();

    _todo.push({ PO_POP_LOOKUP, nullptr });
    _todo.push({ PO_MATCH_CASE, caseExp });
    _todo.push({ PO_PARSE, matchedAtom });
  }
}

void SMTLIB2::parseMatchCase(LExpr *exp)
{
  LOG2("parseMatchCase  ", exp->toString());

  auto eRdr = READER(exp);
  auto pattern = eRdr.readExpr();
  auto body = eRdr.readExpr();
  eRdr.acceptEOL();

  TermList matchedTerm;
  auto matchedTermSort = _results.pop().asTerm(matchedTerm);
  ASS(matchedTermSort.isTerm());

  // We will parse the body
  _todo.push(make_pair(PO_PARSE, body));

  // now parse the match pattern which
  // potentially declares new variables
  _lookups.emplace();
  if (pattern->isAtom()) {
    if (pattern->str == UNDERSCORE) {
      _results.push(ParseResult(matchedTermSort, TermList::var(_nextVar++)));
      return;
    }
    if (!isTermAlgebraConstructor(pattern->str)) {
      // If the symbol is not a ctor, we optimistically assume
      // that it is a fresh variable possibly shadowing symbols
      TermList var = TermList::var(_nextVar++);
      tryInsertIntoCurrentLookup(pattern->str, var, matchedTermSort);
      _results.push(ParseResult(matchedTermSort, var));
      return;
    }
    auto fn = _declaredSymbols.get(pattern->str).first;
    auto type = env.signature->getFunction(fn)->fnType();
    TermStack patternArgs;
    for (unsigned i = 0; i < type->arity(); i++) {
      ASS_L(i, type->numTypeArguments());
      patternArgs.push(*matchedTermSort.term()->nthArgument(i));
    }
    _results.push(ParseResult(matchedTermSort, TermList(Term::create(fn, patternArgs))));
    return;
  }

  auto tRdr = READER(pattern);
  auto ctorName = tRdr.readAtom();
  if (!isTermAlgebraConstructor(ctorName)) {
    USER_ERROR_EXPR("Unrecognized term algebra constructor "+ctorName+" in match pattern");
  }
  auto fn = _declaredSymbols.get(ctorName).first;
  auto type = env.signature->getFunction(fn)->fnType();

  Substitution subst;
  TermStack patternArgs;
  for (unsigned i = 0; i < type->arity(); i++) {
    if (i < type->numTypeArguments()) {
      auto typeArg = *matchedTermSort.term()->nthArgument(i);
      subst.bindUnbound(type->quantifiedVar(i).var(),typeArg);
      patternArgs.push(typeArg);
      continue;
    }
    auto argExp = tRdr.readExpr();
    if (!argExp->isAtom() || isAlreadyKnownFunction(argExp->str)) {
      USER_ERROR_EXPR("Nested ctors ("+argExp->toString()+") in match patterns are disallowed: '" + exp->toString() + "'");
    }
    auto var = TermList::var(_nextVar++);
    patternArgs.push(var);
    if (argExp->str != UNDERSCORE) {
      // from the type arguments used in the matched term we instantiate the type of the other variables
      tryInsertIntoCurrentLookup(argExp->str, var, SubstHelper::apply(type->arg(i), subst));
    }
  }
  _results.push(ParseResult(matchedTermSort, TermList(Term::create(fn, patternArgs))));
}

void SMTLIB2::parseMatchEnd(LExpr *exp)
{
  LOG2("PO_MATCH_END ", exp->toString());

  auto lRdr = READER(exp);
  DEBUG_CODE(const std::string &theMatchAtom =) lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theMatchAtom), TS_MATCH);

  lRdr.readExpr(); // the matched term
  TermList matchedTerm;
  auto matchedTermSort = _results.pop().asTerm(matchedTerm);

  LOG2("CASE matched ", matchedTerm.toString());

  std::map<unsigned, TermAlgebraConstructor *> ctorFunctors;
  TermAlgebra *ta = env.signature->getTermAlgebraOfSort(matchedTermSort);
  if (ta == nullptr) {
    USER_ERROR_EXPR("Match term '" + matchedTerm.toString() + "' is not of a term algebra type in expression '" + exp->toString() + "'");
  }
  for (unsigned int i = 0; i < ta->nConstructors(); i++) {
    ctorFunctors.insert({ ta->constructor(i)->functor(), ta->constructor(i) });
  }

  TermList varPattern;
  TermList varBody;

  // This holds the arguments to the $match
  TermStack matchArgs;
  matchArgs.push(matchedTerm);
  TermList sort = AtomicSort::defaultSort();

  auto cRdr = READER(lRdr.readList());
  while (cRdr.hasNext()) {
    cRdr.readList();
    TermList body;
    TermList currSort = _results.pop().asTerm(body);
    ASS(sort == AtomicSort::defaultSort() || sort == currSort);
    sort = currSort;
    TermList pattern;
    ALWAYS(_results.pop().asTerm(pattern) == matchedTermSort);

    LOG2("CASE pattern ", pattern);
    LOG2("CASE body    ", body);

    if (pattern.isVar()) {
      if (varPattern.isNonEmpty()) {
        USER_ERROR_EXPR("Else branch cannot be used twice in match in '" + exp->toString() + "'");
      }
      varPattern = pattern;
      varBody = body;
    }
    else {
      auto functor = pattern.term()->functor();
      if (ctorFunctors.erase(functor) != 1) {
        USER_ERROR_EXPR("Match pattern '" + pattern.toString() + "' is either not ctor or was listed twice in '" + exp->toString() + "'");
      }
      matchArgs.push(pattern);
      matchArgs.push(body);
    }
  }
  lRdr.acceptEOL();

  // if there is a variable pattern, we add the missing ctors
  if (varPattern.isNonEmpty()) {
    TermStack argTerms;
    // the number of type arguments for all ctors is the arity of the type
    unsigned numTypeArgs = matchedTermSort.term()->arity();
    for (const auto &kv : ctorFunctors) {
      argTerms.reset();
      for (unsigned j = 0; j < kv.second->arity(); j++) {
        if (j < numTypeArgs) {
          argTerms.push(*matchedTermSort.term()->nthArgument(j));
        } else {
          argTerms.push(TermList::var(_nextVar++));
        }
      }
      TermList pattern(Term::create(kv.second->functor(), argTerms.size(), argTerms.begin()));
      LOG2("CASE missing ", pattern);
      ASS(varPattern.isVar());
      Substitution subst;
      subst.bindUnbound(varPattern.var(), pattern);
      matchArgs.push(pattern);
      matchArgs.push(SubstHelper::apply(varBody, subst));
    }
  }
  else if (ctorFunctors.size() > 0) {
    USER_ERROR_EXPR("Missing ctors in match expression '" + exp->toString() + "'");
  }

  auto match = TermList(Term::createMatch(sort, matchedTermSort, matchArgs.size(), matchArgs.begin()));
  _results.push(ParseResult(sort,match));
}

void SMTLIB2::parseQuantBegin(LExpr* exp)
{
  auto lRdr = READER(exp);

  // the quant atom
  DEBUG_CODE(const std::string& theQuantAtom =) lRdr.readAtom();
  ASS(theQuantAtom == FORALL || theQuantAtom == EXISTS);
  _todo.push(make_pair(PO_QUANT,exp));

  // there should next be a list of sorted variables
  auto varRdr = READER(lRdr.readList());
  while (varRdr.hasNext()) {
    auto pRdr = READER(varRdr.readList());

    pRdr.readAtom(); // name
    _todo.push(make_pair(PO_PARSE_SORT, pRdr.readExpr()));
    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseQuantEnd(LExpr* exp)
{
  auto lRdr = READER(exp);

  lRdr.readAtom(); // already checked the quant atom

  // there should next be a list of sorted variables
  auto varRdr = READER(lRdr.readList());

  _lookups.emplace();
  while (varRdr.hasNext()) {
    auto pRdr = READER(varRdr.readList());

    auto vName = pRdr.readAtom();
    pRdr.readExpr(); // the type
    pRdr.acceptEOL();
  
    ParseResult pr = _results.pop();
    TermList vSort;
    ALWAYS(pr.asTerm(vSort) == AtomicSort::superSort());
    tryInsertIntoCurrentLookup(vName, TermList::var(_nextVar++), vSort);
  }

  _todo.push(make_pair(PO_PARSE_APPLICATION,exp)); // will create the actual quantified formula and clear the lookup...
  _todo.push(make_pair(PO_PARSE,lRdr.readExpr())); // ... from the only remaining argument, the body
  lRdr.acceptEOL();
}

static const char* EXCLAMATION = "!";

void SMTLIB2::parseAnnotatedTerm(LExpr* exp)
{
  auto lRdr = READER(exp);

  // the exclamation atom
  ALWAYS(lRdr.tryAcceptAtom(EXCLAMATION));

  auto toParse = lRdr.readExpr();

  // we only consider :named annotations
  if(lRdr.tryAcceptAtom(":named")){
    _todo.push(make_pair(PO_LABEL,lRdr.readExpr()));
  }

  _todo.push(make_pair(PO_PARSE,toParse));
}

bool SMTLIB2::parseAsScopeLookup(const std::string& id)
{
  Binding bound;
  Lookups::ConstRefIterator lIt(_lookups);
  while (lIt.hasNext()) {
    if (lIt.next().find(id, bound)) {
      _results.push(ParseResult(bound.sort, bound.term));
      return true;
    }
  }
  if (_globalSortParamLookup.find(id, bound)) {
    _results.push(ParseResult(bound.sort, bound.term));
    return true;
  }

  return false;
}

bool SMTLIB2::parseAsSortDefinition(const std::string& id, LExpr* exp)
{
  std::string pId = id;
  auto def = _sortDefinitions.findPtr(pId);
  if (!def) {
    return false;
  }
  Substitution subst;
  for (unsigned i = 0; i < def->first; i++) {
    if (_results.isEmpty() || _results.top().isSeparator()) {
      complainAboutArgShortageOrWrongSorts("sort definition",exp);
    }
    TermList arg;
    ALWAYS(_results.pop().asTerm(arg) == AtomicSort::superSort());
    subst.bindUnbound(i, arg);
  }
  _results.push(ParseResult(AtomicSort::superSort(), SubstHelper::apply(def->second, subst)));
  return true;
}

bool SMTLIB2::parseAsSpecConstant(const std::string& id)
{
  if (StringUtils::isPositiveInteger(id)) {
    if (_numeralsAreReal) {
      goto real_constant; // just below
    }

    unsigned symb = TPTP::addNumeralConstant<IntegerConstantType>(id);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(AtomicSort::intSort(),res));

    return true;
  }

  if (StringUtils::isPositiveDecimal(id)) {
    real_constant:

    unsigned symb = TPTP::addNumeralConstant<RealConstantType>(id);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(AtomicSort::realSort(),res));

    return true;
  }

  return false;
}

bool SMTLIB2::parseAsUserDefinedSymbol(const std::string& id,LExpr* exp,bool isSort)
{
  DeclaredSymbol sym;
  if(!isSort && !_declaredSymbols.find(id,sym))
    return false;
  if(isSort && !_declaredSorts.find(id,sym.first))
    return false;

  unsigned symbIdx = sym.first;
  bool isPred = sym.second;
  Signature::Symbol* symbol = nullptr;
  OperatorType* type = nullptr;
  if(isSort) {
    symbol = env.signature->getTypeCon(symbIdx);
    type = symbol->typeConType();
  } else if(isPred) {
    symbol = env.signature->getPredicate(symbIdx);
    type = symbol->predType();
  } else {
    symbol = env.signature->getFunction(symbIdx);
    type = symbol->fnType();
  }

  unsigned numTypeArgs = type->numTypeArguments();
  unsigned arity = symbol->arity();

  TermStack termArgs;
  Substitution subst;
  for (unsigned i = numTypeArgs; i < arity; i++) {
    if (_results.isEmpty() || _results.top().isSeparator()) {
      complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
    }
    TermList arg;
    auto argSort = _results.pop().asTerm(arg);
    // Sort matching does not work well, but our sorts
    // are not dependent anyways, so just check equals
    if (isSort) {
      if (type->arg(i)!=argSort) {
        complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
      }
    } else {
      if (!MatchingUtils::matchTerms(type->arg(i), argSort, subst)) {
        complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
      }
    }
    termArgs.push(arg);
  }

  // Try to handle 'as' expression, which is required
  // to diambiguate the result sort, see below.
  // TODO: try to remove this ugly hack.
  if (_todo.isNonEmpty()) {
    auto [op,exp] = _todo.top();
    if (op == PO_AS_END) {
      _todo.pop();
      ASS(!isSort);
      TermList resSort;
      DEBUG_CODE(auto sort =) _results.pop().asTerm(resSort);
      ASS_EQ(sort, AtomicSort::superSort());
      if (!MatchingUtils::matchTerms(type->result(), resSort, subst)) {
        complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
      }
    }
  }

  TermStack args;
  for (unsigned i = 0; i < numTypeArgs; i++) {
    auto typeVar = type->quantifiedVar(i).var();
    TermList typeVarS;
    // We require terms to have unambiguous sorts, except for ctor
    // terms in 'match' blocks which are disambiguated by the sort
    // of the matched term. We collect type variable instantiations
    // from the arguments recursively, which by assumption already have
    // unambiguous sorts. If any variable remains free after this, it
    // means the result sort contains some free variable, and the user
    // must enclose it in an (as <term> <sort>) block.
    // Note that the 'as' is handled just above.
    if (!subst.findBinding(typeVar, typeVarS)) {
      USER_ERROR_EXPR("User defined term "+exp->toString()+" has ambiguous sort, use (as "+exp->toString()+" <sort>) block to disambiguate");
    }
    args.push(typeVarS);
  }
  args.loadFromIterator(TermStack::BottomFirstIterator(termArgs));

  if(isSort) {
    TermList res = TermList(AtomicSort::create(symbIdx,arity,args.begin()));
    TermList sort = SortHelper::getResultSort(res.term());
    _results.push(ParseResult(sort,res));
  } else if(isPred) {
    Formula* res = new AtomicFormula(Literal::create(symbIdx,arity,true,args.begin()));
    _results.push(ParseResult(res));
  } else {
    TermList res = TermList(Term::create(symbIdx,arity,args.begin()));
    TermList sort = SortHelper::getResultSort(res.term());
    _results.push(ParseResult(sort,res));
  }

  return true;
}

static const char* BUILT_IN_SYMBOL = "built-in symbol";

bool SMTLIB2::parseAsBuiltinFormulaSymbol(const std::string& id, LExpr* exp)
{
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
          Literal *l = Literal::createEquality(true, first, second, firstParseResult.sort);
          lastConjunct = new AtomicFormula(l, first != l->termArg(0));
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
            Literal *l = Literal::createEquality(true, first, second, firstParseResult.sort);
            lastConjunct = new AtomicFormula(l, first != l->termArg(0));
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
    {
      Formula* argFla;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          !(_results.pop().asFormula(argFla))) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      VList::FIFO qvars;
      SList::FIFO qsorts;

      for(Binding binding : _lookups.top().bindings) {
        unsigned varIdx = binding.term.var();
        qvars.pushBack(varIdx);
        qsorts.pushBack(binding.sort);
      }
      _lookups.pop();

      Formula* res = new QuantifiedFormula((fs==FS_EXISTS) ? Kernel::EXISTS : Kernel::FORALL, qvars.list(), qsorts.list(), argFla);

      _results.push(ParseResult(res));
      return true;
    }

    default:
      ASS_EQ(fs,FS_USER_PRED_SYMBOL);
      return false;
  }
}

bool SMTLIB2::parseAsBuiltinTermSymbol(const std::string& id, LExpr* exp)
{
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
      TermList res = TermList(Term::create(fun, 3, args));

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
    default:
      ASS_EQ(ts,TS_USER_FUNCTION);
      break;
  }

  // try built-in type symbols
  TypeSymbol tts = getBuiltInTypeSymbol(id);
  switch(tts) {
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
      ASS_EQ(tts,TS_USER_TYPE);
      break;
  }

  return false;
}

void SMTLIB2::parseRankedFunctionApplication(LExpr* exp)
{
  auto lRdr = READER(exp);
  auto head = lRdr.readList();
  auto headRdr = READER(head);

  if (!headRdr.tryAcceptAtom(UNDERSCORE)) {
    USER_ERROR("Compound functor expected to be a rankend function (starting with '_'). Instead read: "+head->toString());
  }

  if(headRdr.tryAcceptAtom("divisible")){

    const std::string& numeral = headRdr.readAtom();

    if (!StringUtils::isPositiveInteger(numeral)) {
      USER_ERROR_EXPR("Expected numeral as an argument of a ranked function in "+head->toString());
    }

    unsigned divisorSymb = TPTP::addNumeralConstant<IntegerConstantType>(numeral);
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
    const std::string& consName = headRdr.readAtom();

    if (_declaredSymbols.find(consName)) {
      DeclaredSymbol& s = _declaredSymbols.get(consName);
      if (!s.second) {
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
          Formula* res = new AtomicFormula(Literal::create(c->discriminator(),args.size(),true,args.begin()));

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

    auto [op,exp] = _todo.pop();

    switch (op) {
      case PO_PARSE: {
        if (exp->isList()) {
          auto lRdr = READER(exp);

          // schedule arity check
          _results.push(ParseResult()); // separator into results
          _todo.push(make_pair(PO_CHECK_ARITY,exp)); // check as a todo (exp for error reporting)

          // special treatment of some tokens
          auto fst = lRdr.readExpr();
          if (fst->isAtom()) {
            std::string& id = fst->str;

            if (id == FORALL || id == EXISTS) {
              parseQuantBegin(exp);
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

            if (id == AS) {
              _todo.push({ PO_AS_END, exp });
              _todo.push({ PO_PARSE, lRdr.readExpr() });
              _todo.push({ PO_PARSE_SORT, lRdr.readExpr() });
              lRdr.acceptEOL();
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
          // and all the other arguments too
          while (lRdr.hasNext()) {
            _todo.push(make_pair(PO_PARSE,lRdr.readExpr()));
          }

          continue;
        }

        // INTENTIONAL FALL-THROUGH FOR ATOMS
      }
      case PO_PARSE_APPLICATION: { // the arguments have already been parsed
        std::string id;
        if (exp->isAtom()) { // the fall-through case
          id = exp->str;
        } else {
          ASS(exp->isList());
          auto lRdr = READER(exp);
          auto head = lRdr.readExpr();

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

        if (parseAsUserDefinedSymbol(id,exp,false/*isSort*/)) {
          continue;
        }

        if (parseAsSpecConstant(id)) {
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
          auto lRdr = READER(exp);
          lRdr.readExpr(); // the head

          // schedule arity check
          _results.push(ParseResult()); // separator into results
          _todo.push(make_pair(PO_CHECK_ARITY,exp)); // check as a todo (exp for error reporting)
          _todo.push(make_pair(PO_PARSE_SORT_APPLICATION,exp));
          while (lRdr.hasNext()) {
            _todo.push(make_pair(PO_PARSE_SORT,lRdr.readExpr()));
          }

          continue;
        }
      }
      case PO_PARSE_SORT_APPLICATION: { // the arguments have already been parsed
        std::string id;
        if (exp->isAtom()) { // the fall-through case
          id = exp->str;
        } else {
          auto lRdr = READER(exp);
          id = lRdr.readAtom();
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
        std::string label = exp->toString();
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
      case PO_MATCH_CASE: {
        parseMatchCase(exp);
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
        _lookups.pop();
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
  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));
  _formulas.pushBack(fu);
}

void SMTLIB2::readAssertClaim(LExpr* body)
{
  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  static unsigned claim_id = 0;

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));
  _formulas.pushBack(TPTP::processClaimFormula(fu,fla,"claim"+Int::toString(claim_id++)));
}

void SMTLIB2::readAssertNot(LExpr* body)
{
  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::CONJECTURE));
  fu = new FormulaUnit(new NegatedFormula(fla),
                       FormulaClauseTransformation(InferenceRule::NEGATED_CONJECTURE, fu));
  _formulas.pushBack(fu);
}

void SMTLIB2::readAssertSynth(LExpr* forall, LExpr* exist, LExpr* body)
{
  _lookups.emplace();

  if (env.options->questionAnswering() != Options::QuestionAnsweringMode::SYNTHESIS) {
    std::cout << "% WARNING: Found an assert-synth command but synthesis is not enabled. Consider running with '-qa synthesis'." << endl;
  }

  auto parseVarList = [this](LExpr* lexp) {
    auto vars = VList::empty();
    auto sorts = SList::empty();
    auto rdr = READER(lexp);
    while (rdr.hasNext()) {
      auto pRdr = READER(rdr.readList());
      auto name = pRdr.readAtom();
      auto var = TermList::var(_nextVar++);
      auto sort = parseSort(pRdr.readExpr());
      tryInsertIntoCurrentLookup(name, var, sort);
      VList::push(var.var(), vars);
      SList::push(sort, sorts);
    }
    return make_pair(vars, sorts);
  };

  auto [fvars, fsorts] = parseVarList(forall);
  auto [evars, esorts] = parseVarList(exist);
  ParseResult res = parseTermOrFormula(body,false/*isSort*/);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR_EXPR("Asserted expression of non-boolean sort "+body->toString());
  }
  _lookups.pop();

  fla = new QuantifiedFormula(Connective::EXISTS, evars, esorts, fla);
  fla = new QuantifiedFormula(Connective::FORALL, fvars, fsorts, fla);
  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::CONJECTURE));
  fu = new FormulaUnit(new NegatedFormula(fla),
                       FormulaClauseTransformation(InferenceRule::NEGATED_CONJECTURE, fu));
  _formulas.pushBack(fu);
}

Signature::Symbol* SMTLIB2::getSymbol(DeclaredSymbol& s) {
  return s.second
    ? env.signature->getPredicate(s.first)
    : env.signature->getFunction(s.first);
}

void SMTLIB2::colorSymbol(const std::string& name, Color color)
{
  if (!_declaredSymbols.find(name)) {
    USER_ERROR_EXPR("'"+name+"' is not a user symbol");
  }
  DeclaredSymbol& s = _declaredSymbols.get(name);

  env.colorUsed = true;

  Signature::Symbol* sym = getSymbol(s);
  sym->addColor(color);
}

void SMTLIB2::markSymbolUncomputable(const std::string& name)
{
  if (!_declaredSymbols.find(name)) {
    USER_ERROR("'"+name+"' is not a user symbol");
  }
  DeclaredSymbol& f = _declaredSymbols.get(name);
  if (env.options->questionAnswering() != Options::QuestionAnsweringMode::SYNTHESIS) {
    std::cout << "% WARNING: Found the :uncomputable option but synthesis is not enabled. Consider running with '-qa synthesis'." << endl;
  } else {
    static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->addDeclaredSymbolAnnotatedAsUncomputable(f);
  }
}

}

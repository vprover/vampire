
/*
 * File SMTLIB2.cpp.
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

namespace Parse {

SMTLIB2::SMTLIB2(const Options& opts)
: _logicSet(false),
  _logic(SMT_UNDEFINED),
  _numeralsAreReal(false),
  _formulas(nullptr)
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

  // iteration over benchmark top level entries
  while(bRdr.hasNext()){
    LExpr* lexp = bRdr.next();

    LOG2("readBenchmark ",lexp->toString(true));

    LispListReader ibRdr(lexp);

    if (ibRdr.tryAcceptAtom("set-logic")) {
      if (_logicSet) {
        USER_ERROR("set-logic can appear only once in a problem");
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
        USER_ERROR("Unspecified arity while declaring sort: "+name);
      }

      readDeclareSort(name,arity);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-sort")) {
      vstring name = ibRdr.readAtom();
      LExprList* args = ibRdr.readList();
      LExpr* body = ibRdr.readNext();

      readDefineSort(name,args,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("declare-fun")) {
      vstring name = ibRdr.readAtom();
      LExprList* iSorts = ibRdr.readList();
      LExpr* oSort = ibRdr.readNext();

      readDeclareFun(name,iSorts,oSort);

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
      LExpr* oSort = ibRdr.readNext();

      readDeclareFun(name,nullptr,oSort);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-fun")) {
      vstring name = ibRdr.readAtom();
      LExprList* iArgs = ibRdr.readList();
      LExpr* oSort = ibRdr.readNext();
      LExpr* body = ibRdr.readNext();

      readDefineFun(name,iArgs,oSort,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("define-fun-rec")) {
      vstring name = ibRdr.readAtom();
      LExprList* iArgs = ibRdr.readList();
      LExpr* oSort = ibRdr.readNext();
      LExpr* body = ibRdr.readNext();

      readDefineFunRec(name,iArgs,oSort,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert")) {
      readAssert(ibRdr.readNext());

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert-not")) {
      readAssertNot(ibRdr.readNext());

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
        USER_ERROR("'"+ibRdr.readAtom()+"' is not a color keyword");
      }

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("check-sat")) {
      if (bRdr.hasNext()) {
        LispListReader exitRdr(bRdr.readList());
        if (!exitRdr.tryAcceptAtom("exit")) {
          if(env.options->mode()!=Options::Mode::SPIDER) {
            env.beginOutput();
            env.out() << "% Warning: check-sat is not the last entry. Skipping the rest!" << endl;
            env.endOutput();
          }
        }
      }
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

    USER_ERROR("unrecognized entry "+ibRdr.readAtom());
  }
}

//  ----------------------------------------------------------------------

const char * SMTLIB2::s_smtlibLogicNameStrings[] = {
    "ALIA",
    "ALL",
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
    USER_ERROR("unsupported logic "+logicStr);
  default:
    USER_ERROR("unrecognized logic "+logicStr);
  }

}

//  ----------------------------------------------------------------------

const char * SMTLIB2::s_builtInSortNameStrings[] = {
    "Array",
    "Bool",
    "Int",
    "Real"
};

SMTLIB2::BuiltInSorts SMTLIB2::getBuiltInSortFromString(const vstring& str)
{
  CALL("SMTLIB::getBuiltInSortFromString");

  static NameArray builtInSortNames(s_builtInSortNameStrings, sizeof(s_builtInSortNameStrings)/sizeof(char*));
  ASS_EQ(builtInSortNames.length, BS_INVALID);

  int res = builtInSortNames.tryToFind(str.c_str());
  if(res==-1) {
    return BS_INVALID;
  }
  return static_cast<BuiltInSorts>(res);
}

bool SMTLIB2::isAlreadyKnownSortSymbol(const vstring& name)
{
  CALL("SMTLIB::isAlreadyKnownSortSymbol");

  if (getBuiltInSortFromString(name) != BS_INVALID) {
    return true;
  }

  if (_declaredSorts.find(name)) {
    return true;
  }

  if (_sortDefinitions.find(name)) {
    return true;
  }

  return false;
}

void SMTLIB2::readDeclareSort(const vstring& name, const vstring& arity)
{
  CALL("SMTLIB2::readDeclareSort");

  if (isAlreadyKnownSortSymbol(name)) {
    USER_ERROR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  if (not StringUtils::isPositiveInteger(arity)) {
    USER_ERROR("Unrecognized declared sort arity: "+arity);
  }

  unsigned val;
  if (!Int::stringToUnsignedInt(arity, val)) {
    USER_ERROR("Couldn't convert sort arity: "+arity);
  }

  ALWAYS(_declaredSorts.insert(name,val));
}

void SMTLIB2::readDefineSort(const vstring& name, LExprList* args, LExpr* body)
{
  CALL("SMTLIB2::readDefineSort");

  if (isAlreadyKnownSortSymbol(name)) {
    USER_ERROR("Redeclaring built-in, declared or defined sort symbol: "+name);
  }

  // here we could check the definition for well-formed-ness
  // current solution: crash only later, at application site

  ALWAYS(_sortDefinitions.insert(name,SortDefinition(args,body)));
}

//  ----------------------------------------------------------------------

/**
 * SMTLIB sort expression turned into vampire sort id.
 *
 * Taking into account built-in sorts, declared sorts and sort definitions.
 */
unsigned SMTLIB2::declareSort(LExpr* sExpr)
{
  CALL("SMTLIB2::declareSort");

  enum SortParseOperation {
    SPO_PARSE,
    SPO_POP_LOOKUP,
    SPO_CHECK_ARITY
  };
  static Stack<pair<SortParseOperation,LExpr*> > todo;
  ASS(todo.isEmpty());

  ASS_EQ(Sorts::SRT_DEFAULT,0); // there is no default sort in smtlib, so we can use 0 as a results separator
  static const int SEPARATOR = 0;
  static Stack<unsigned> results;
  ASS(results.isEmpty());

  // evaluation contexts for the expansion of sort definitions
  typedef DHMap<vstring,unsigned> SortLookup;
  static Stack<SortLookup*> lookups;
  ASS(lookups.isEmpty());

  // to store defined sort's identifier when expanding its definition
  // (for preventing circular non-sense)
  static Stack<vstring> forbidden;
  ASS(forbidden.isEmpty());

  todo.push(make_pair(SPO_PARSE,sExpr));

  while (todo.isNonEmpty()) {
    pair<SortParseOperation,LExpr*> cur = todo.pop();
    SortParseOperation op = cur.first;

    if (op == SPO_POP_LOOKUP) {
      delete lookups.pop();
      forbidden.pop();
      continue;
    }

    if (op == SPO_CHECK_ARITY) {
      if (results.size() < 2) {
        goto malformed;
      }
      unsigned true_result = results.pop();
      unsigned separator   = results.pop();

      if (true_result == SEPARATOR || separator != SEPARATOR) {
        goto malformed;
      }
      results.push(true_result);

      continue;
    }

    ASS_EQ(op,SPO_PARSE);
    LExpr* exp = cur.second;

    if (exp->isList()) {
      LExprList::Iterator lIt(exp->list);

      todo.push(make_pair(SPO_CHECK_ARITY,nullptr));
      results.push(SEPARATOR);

      while (lIt.hasNext()) {
        todo.push(make_pair(SPO_PARSE,lIt.next()));
      }
    } else {
      ASS(exp->isAtom());
      vstring& id = exp->str;

      // try (top) context lookup
      if (lookups.isNonEmpty()) {
        SortLookup* lookup = lookups.top();
        unsigned res;
        if (lookup->find(id,res)) {
          results.push(res);
          continue;
        }
      }

      {
        for (unsigned i = 0; i < forbidden.size(); i++) {
          if (id == forbidden[i]) {
            USER_ERROR("Expanding circular sort definition "+ id);
          }
        }
      }

      // try declared sorts
      unsigned arity;
      if (_declaredSorts.find(id,arity)) {
        // building an arbitrary but unique sort string
        // TODO: this may not be good enough for a tptp-compliant output!
        vstring sortName = id + "(";
        while (arity--) {
          if (results.isEmpty() || results.top() == SEPARATOR) {
            goto malformed;
          }
          sortName += Int::toString(results.pop());
          if (arity) {
            sortName += ",";
          }
        }
        sortName += ")";

        unsigned newSort = env.sorts->addSort(sortName,false);
        results.push(newSort);

        continue;
      }

      // try defined sorts
      SortDefinition def;
      if (_sortDefinitions.find(id,def)) {
        SortLookup* lookup = new SortLookup();

        LispListReader argRdr(def.args);

        while (argRdr.hasNext()) {
          if (results.isEmpty() || results.top() == SEPARATOR) {
            goto malformed;
          }
          unsigned argSort = results.pop();
          const vstring& argName = argRdr.readAtom();
          // TODO: could check if the same string names more than one argument positions
          // the following just takes the first and ignores the others
          lookup->insert(argName,argSort);
        }

        lookups.push(lookup);
        forbidden.push(id);

        todo.push(make_pair(SPO_POP_LOOKUP,nullptr)); //schedule lookup deletion (see above)
        todo.push(make_pair(SPO_PARSE,def.body));

        continue;
      }

      // try built-ins
      BuiltInSorts bs = getBuiltInSortFromString(id);
      switch (bs) {
        case BS_BOOL:
          results.push(Sorts::SRT_BOOL);
          continue;
        case BS_INT:
          results.push(Sorts::SRT_INTEGER);
          continue;
        case BS_REAL:
          results.push(Sorts::SRT_REAL);
          continue;
        case BS_ARRAY:
          if (results.size() < 2) {
            goto malformed;
          } else {
            unsigned indexSort = results.pop();
            unsigned innerSort = results.pop();
            if (indexSort == SEPARATOR || innerSort == SEPARATOR) {
              goto malformed;
            }
            results.push(env.sorts->addArraySort(indexSort,innerSort));
            continue;
          }

        default:
          ASS_EQ(bs,BS_INVALID);
      }

      USER_ERROR("Unrecognized sort identifier "+id);
    }
  }

  if (results.size() == 1) {
    return results.pop();
  } else {
    malformed:
    USER_ERROR("Malformed type expression "+sExpr->toString());
  }
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

bool SMTLIB2::isAlreadyKnownFunctionSymbol(const vstring& name)
{
  CALL("SMTLIB2::isAlreadyKnownFunctionSymbol");

  if (getBuiltInFormulaSymbol(name) != FS_USER_PRED_SYMBOL) {
    return true;
  }

  if (getBuiltInTermSymbol(name) != TS_USER_FUNCTION) {
    return true;
  }

  if (_declaredFunctions.find(name)) {
    return true;
  }

  return false;
}

bool SMTLIB2::isTermAlgebraConstructor(const vstring& name)
{
  CALL("SMTLIB2::isTermAlgebraConstructor");

  if (_declaredFunctions.find(name)) {
    DeclaredFunction& f = _declaredFunctions.get(name);
    return (f.second && env.signature->getTermAlgebraConstructor(f.first));
  }

  return false;
}

void SMTLIB2::readDeclareFun(const vstring& name, LExprList* iSorts, LExpr* oSort)
{
  CALL("SMTLIB2::readDeclareFun");

  if (isAlreadyKnownFunctionSymbol(name)) {
    USER_ERROR("Redeclaring function symbol: "+name);
  }

  unsigned rangeSort = declareSort(oSort);

  LispListReader isRdr(iSorts);

  static Stack<unsigned> argSorts;
  argSorts.reset();

  while (isRdr.hasNext()) {
    argSorts.push(declareSort(isRdr.next()));
  }

  declareFunctionOrPredicate(name,rangeSort,argSorts);
}

SMTLIB2::DeclaredFunction SMTLIB2::declareFunctionOrPredicate(const vstring& name, signed rangeSort, const Stack<unsigned>& argSorts)
{
  CALL("SMTLIB2::declareFunctionOrPredicate");

  bool added;
  unsigned symNum;
  Signature::Symbol* sym;
  OperatorType* type;

  if (rangeSort == Sorts::SRT_BOOL) { // predicate
    symNum = env.signature->addPredicate(name, argSorts.size(), added);

    sym = env.signature->getPredicate(symNum);

    type = OperatorType::getPredicateType(argSorts.size(),argSorts.begin());

    LOG1("declareFunctionOrPredicate-Predicate");
  } else { // proper function
    if (argSorts.size() > 0) {
      symNum = env.signature->addFunction(name, argSorts.size(), added);
    } else {
      symNum = TPTP::addUninterpretedConstant(name,_overflow,added);
    }

    sym = env.signature->getFunction(symNum);

    type = OperatorType::getFunctionType(argSorts.size(), argSorts.begin(), rangeSort);

    LOG1("declareFunctionOrPredicate-Function");
  }

  ASS(added);
  sym->setType(type);

  DeclaredFunction res = make_pair(symNum,type->isFunctionType());

  LOG2("declareFunctionOrPredicate -name ",name);
  LOG2("declareFunctionOrPredicate -symNum ",symNum);

  ALWAYS(_declaredFunctions.insert(name,res));

  return res;
}

//  ----------------------------------------------------------------------

void SMTLIB2::readDefineFun(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body)
{
  CALL("SMTLIB2::readDefineFun");

  if (isAlreadyKnownFunctionSymbol(name)) {
    USER_ERROR("Redeclaring function symbol: "+name);
  }

  unsigned rangeSort = declareSort(oSort);

  _nextVar = 0;
  ASS(_scopes.isEmpty());
  TermLookup* lookup = new TermLookup();

  static Stack<unsigned> argSorts;
  argSorts.reset();

  static Stack<TermList> args;
  args.reset();

  LispListReader iaRdr(iArgs);
  while (iaRdr.hasNext()) {
    LExprList* pair = iaRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    unsigned vSort = declareSort(pRdr.readNext());

    pRdr.acceptEOL();

    TermList arg = TermList(_nextVar++, false);
    args.push(arg);

    if (!lookup->insert(vName,make_pair(arg,vSort))) {
      USER_ERROR("Multiple occurrence of variable "+vName+" in the definition of function "+name);
    }

    argSorts.push(vSort);
  }

  _scopes.push(lookup);

  ParseResult res = parseTermOrFormula(body);

  delete _scopes.pop();

  TermList rhs;
  if (res.asTerm(rhs) != rangeSort) {
    USER_ERROR("Defined function body "+body->toString()+" has different sort than declared "+oSort->toString());
  }

  // Only after parsing, so that the definition cannot be recursive
  DeclaredFunction fun = declareFunctionOrPredicate(name,rangeSort,argSorts);

  unsigned symbIdx = fun.first;
  bool isTrueFun = fun.second;

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

void SMTLIB2::readDefineFunRec(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body)
{
  CALL("SMTLIB2::readDefineFunRec");

  if (isAlreadyKnownFunctionSymbol(name)) {
    USER_ERROR("Redeclaring function symbol: "+name);
  }

  unsigned rangeSort = declareSort(oSort);

  _nextVar = 0;
  ASS(_scopes.isEmpty());
  TermLookup* lookup = new TermLookup();

  static Stack<unsigned> argSorts;
  argSorts.reset();

  static Stack<TermList> args;
  args.reset();

  LispListReader iaRdr(iArgs);
  while (iaRdr.hasNext()) {
    LExprList* pair = iaRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    unsigned vSort = declareSort(pRdr.readNext());

    pRdr.acceptEOL();

    TermList arg = TermList(_nextVar++, false);
    args.push(arg);

    if (!lookup->insert(vName,make_pair(arg,vSort))) {
      USER_ERROR("Multiple occurrence of variable "+vName+" in the definition of function "+name);
    }

    argSorts.push(vSort);
  }

  _scopes.push(lookup);

  // Declare before parsing, since it's a recursive function
  DeclaredFunction fun = declareFunctionOrPredicate(name,rangeSort,argSorts);

  ParseResult res = parseTermOrFormula(body);

  delete _scopes.pop();

  TermList rhs;
  if (res.asTerm(rhs) != rangeSort) {
    USER_ERROR("Defined function body "+body->toString()+" has different sort than declared "+oSort->toString());
  }

  unsigned symbIdx = fun.first;
  bool isTrueFun = fun.second;

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

void SMTLIB2::readDeclareDatatypes(LExprList* sorts, LExprList* datatypes, bool codatatype)
{
  CALL("SMTLIB2::readDeclareDatatypes");
  
  if(LExprList::length(sorts) != LExprList::length(datatypes)){
    USER_ERROR("declare-datatype(s) declaration mismatch between declared datatypes and definitions");
  }

  // first declare all the sorts, and then only the constructors, in
  // order to allow mutually recursive datatypes definitions
  LispListReader dtypesNamesRdr(sorts);
  Stack<vstring> dtypeNames;
  while (dtypesNamesRdr.hasNext()) {
    LispListReader dtypeNRdr(dtypesNamesRdr.readList());

    const vstring& dtypeName = dtypeNRdr.readAtom();
    const vstring& dtypeSize = dtypeNRdr.readAtom();
    unsigned arity;
    if(!Int::stringToUnsignedInt(dtypeSize,arity)){ USER_ERROR("datatype arity not given"); }
    if(arity>0){ USER_ERROR("unsupported parametric datatype declaration"); }
    if (isAlreadyKnownSortSymbol(dtypeName)) {
      USER_ERROR("Redeclaring built-in, declared or defined sort symbol as datatype: "+dtypeName);
    }

    ALWAYS(_declaredSorts.insert(dtypeName, 0));
    bool added;
    unsigned srt = env.sorts->addSort(dtypeName + "()", added,false);
    ASS(added);
    (void)srt; // to get rid of compiler warning when logging is off
    // TODO: is it really OK we normally don't need the sort?
    LOG2("reading datatype "+dtypeName+" as sort ",srt);
    dtypeNames.push(dtypeName+"()");
  }

  Stack<TermAlgebraConstructor*> constructors;
  Stack<unsigned> argSorts;
  Stack<vstring> destructorNames;

  LispListReader dtypesDefsRdr(datatypes);
  Stack<vstring>::BottomFirstIterator dtypeNameIter(dtypeNames);
  while(dtypesDefsRdr.hasNext()) {
    ASS(dtypeNameIter.hasNext());
    constructors.reset();
    const vstring& taName = dtypeNameIter.next(); 
    bool added;
    unsigned taSort = env.sorts->addSort(taName, added, false);
    ASS(!added);

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
          argSorts.push(declareSort(argRdr.next()));
          if (argRdr.hasNext()) {
            USER_ERROR("Bad constructor argument:" + arg->toString());
          }
        }
      }
      constructors.push(buildTermAlgebraConstructor(constrName, taSort, destructorNames, argSorts));
    }

    ASS(!env.signature->isTermAlgebraSort(taSort));
    TermAlgebra* ta = new TermAlgebra(taSort, constructors.size(), constructors.begin(), codatatype);

    if (ta->emptyDomain()) {
      USER_ERROR("Datatype " + taName + " defines an empty sort");
    }

    env.signature->addTermAlgebra(ta);
  }
}

TermAlgebraConstructor* SMTLIB2::buildTermAlgebraConstructor(vstring constrName, unsigned taSort,
                                                             Stack<vstring> destructorNames, Stack<unsigned> argSorts) {
  CALL("SMTLIB2::buildTermAlgebraConstructor");

  if (isAlreadyKnownFunctionSymbol(constrName)) {
    USER_ERROR("Redeclaring function symbol: " + constrName);
  }

  unsigned arity = (unsigned)argSorts.size();

  bool added;
  unsigned functor = env.signature->addFunction(constrName, arity, added);
  ASS(added);

  OperatorType* constructorType = OperatorType::getFunctionType(arity, argSorts.begin(), taSort);
  env.signature->getFunction(functor)->setType(constructorType);
  env.signature->getFunction(functor)->markTermAlgebraCons();

  LOG1("build constructor "+constrName+": "+constructorType->toString());

  ALWAYS(_declaredFunctions.insert(constrName, make_pair(functor, true)));

  Lib::Array<unsigned> destructorFunctors(arity);
  for (unsigned i = 0; i < arity; i++) {
    vstring destructorName = destructorNames[i];
    unsigned destructorSort = argSorts[i];

    if (isAlreadyKnownFunctionSymbol(destructorName)) {
      USER_ERROR("Redeclaring function symbol: " + destructorName);
    }

    bool isPredicate = destructorSort == Sorts::SRT_BOOL;
    bool added;
    unsigned destructorFunctor = isPredicate ? env.signature->addPredicate(destructorName, 1, added)
                                             : env.signature->addFunction(destructorName,  1, added);
    ASS(added);

    OperatorType* destructorType = isPredicate ? OperatorType::getPredicateType(1, &taSort)
                                           : OperatorType::getFunctionType(1, &taSort, destructorSort);

    LOG1("build destructor "+destructorName+": "+destructorType->toString());

    if (isPredicate) {
      env.signature->getPredicate(destructorFunctor)->setType(destructorType);
    } else {
      env.signature->getFunction(destructorFunctor)->setType(destructorType);
    }

    ALWAYS(_declaredFunctions.insert(destructorName, make_pair(destructorFunctor, !isPredicate)));

    destructorFunctors[i] = destructorFunctor;
  }

  return new TermAlgebraConstructor(functor, destructorFunctors);
}

bool SMTLIB2::ParseResult::asFormula(Formula*& resFrm)
{
  CALL("SMTLIB2::ParseResult::asFormula");

  if (formula) {
    ASS_EQ(sort, Sorts::SRT_BOOL);
    resFrm = frm;

    LOG2("asFormula formula ",resFrm->toString());
    return true;
  }

  if (sort == Sorts::SRT_BOOL) {
    // can we unwrap instead of wrapping back and forth?
    if (trm.isTerm()) {
      Term* t = trm.term();
      if (t->isFormula()) {
        resFrm = t->getSpecialData()->getFormula();

        // t->destroy(); -- we cannot -- it can be accessed more than once

        LOG2("asFormula unwrap ",trm.toString());

        return true;
      }
    }

    LOG2("asFormula wrap ",trm.toString());

    resFrm = new BoolTermFormula(trm);
    return true;
  }

  return false;
}

unsigned SMTLIB2::ParseResult::asTerm(TermList& resTrm)
{
  CALL("SMTLIB2::ParseResult::asTerm");

  if (formula) {
    ASS_EQ(sort, Sorts::SRT_BOOL);

    LOG2("asTerm wrap ",frm->toString());

    resTrm = TermList(Term::createFormula(frm));

    LOG2("asTerm sort ",sort);
    return Sorts::SRT_BOOL;
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
    return "formula of sort "+Int::toString(sort)+": "+frm->toString();
  }
  return "term of sort "+Int::toString(sort)+": "+trm.toString();
}

Interpretation SMTLIB2::getFormulaSymbolInterpretation(FormulaSymbol fs, unsigned firstArgSort)
{
  CALL("SMTLIB2::getFormulaSymbolInterpretation");

  switch(fs) {
  case FS_LESS:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
  return Theory::INT_LESS;
    case Sorts::SRT_REAL:
  return Theory::REAL_LESS;
    default:
      break;
    }
    break;
  case FS_LESS_EQ:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
  return Theory::INT_LESS_EQUAL;
    case Sorts::SRT_REAL:
      return Theory::REAL_LESS_EQUAL;
    default:
      break;
    }
    break;
  case FS_GREATER:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
      return Theory::INT_GREATER;
    case Sorts::SRT_REAL:
      return Theory::REAL_GREATER;
    default:
      break;
    }
    break;
  case FS_GREATER_EQ:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
      return Theory::INT_GREATER_EQUAL;
    case Sorts::SRT_REAL:
      return Theory::REAL_GREATER_EQUAL;
    default:
      break;
    }
    break;

  default:
    ASSERTION_VIOLATION;
  }
  USER_ERROR("invalid sort "+env.sorts->sortName(firstArgSort)+" for interpretation "+vstring(s_formulaSymbolNameStrings[fs]));
}

Interpretation SMTLIB2::getUnaryMinusInterpretation(unsigned argSort)
{
  CALL("SMTLIB2::getUnaryMinusInterpretation");

  switch(argSort) {
    case Sorts::SRT_INTEGER:
      return Theory::INT_UNARY_MINUS;
    case Sorts::SRT_REAL:
      return Theory::REAL_UNARY_MINUS;
    default:
      USER_ERROR("invalid sort "+env.sorts->sortName(argSort)+" for interpretation -");
  }
}

Interpretation SMTLIB2::getTermSymbolInterpretation(TermSymbol ts, unsigned firstArgSort)
{
  CALL("SMTLIB2::getTermSymbolInterpretation");

  switch(ts) {
  case TS_MINUS:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
  return Theory::INT_MINUS;
    case Sorts::SRT_REAL:
  return Theory::REAL_MINUS;
    default:
      break;
    }
    break;
  case TS_PLUS:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
  return Theory::INT_PLUS;
    case Sorts::SRT_REAL:
      return Theory::REAL_PLUS;
    default:
      break;
    }
    break;
  case TS_MULTIPLY:
    switch(firstArgSort) {
    case Sorts::SRT_INTEGER:
      return Theory::INT_MULTIPLY;
    case Sorts::SRT_REAL:
      return Theory::REAL_MULTIPLY;
    default:
      break;
    }
    break;

  case TS_DIVIDE:
    if (firstArgSort == Sorts::SRT_REAL)
      return Theory::REAL_QUOTIENT;
    break;

  case TS_DIV:
    if (firstArgSort == Sorts::SRT_INTEGER)
      return Theory::INT_QUOTIENT_E;
    break;

  default:
    ASSERTION_VIOLATION_REP(ts);
  }
    USER_ERROR("invalid sort "+env.sorts->sortName(firstArgSort)+" for interpretation "+vstring(s_termSymbolNameStrings[ts]));
}

void SMTLIB2::complainAboutArgShortageOrWrongSorts(const vstring& symbolClass, LExpr* exp)
{
  CALL("SMTLIB2::complainAboutArgShortageOrWrongSorts");

  USER_ERROR("Not enough arguments or wrong sorts for "+symbolClass+" application "+exp->toString());
}

void SMTLIB2::parseLetBegin(LExpr* exp)
{
  CALL("SMTLIB2::parseLetBegin");

  LOG2("parseLetBegin  ",exp->toString());

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the let atom
  const vstring& theLetAtom = lRdr.readAtom();
  ASS_EQ(theLetAtom,LET);

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
  const vstring& theLetAtom = lRdr.readAtom();
  ASS_EQ(theLetAtom,LET);

  // with a list of bindings
  LispListReader bindRdr(lRdr.readList());

  // corresponding results have already been parsed
  ParseResult* boundExprs = _results.end();

  TermLookup* lookup = new TermLookup();

  while (bindRdr.hasNext()) {
    LExprList* pair = bindRdr.readList();
    LispListReader pRdr(pair);

    const vstring& cName = pRdr.readAtom();
    unsigned sort = (--boundExprs)->sort; // the should be big enough (

    TermList trm;
    if (sort == Sorts::SRT_BOOL) {
      unsigned symb = env.signature->addFreshPredicate(0,"sLP");
      OperatorType* type = OperatorType::getPredicateType(0, nullptr);
      env.signature->getPredicate(symb)->setType(type);

      Formula* atom = new AtomicFormula(Literal::create(symb,0,true,false,nullptr));
      trm = TermList(Term::createFormula(atom));
    } else {
      unsigned symb = env.signature->addFreshFunction (0,"sLF");
      OperatorType* type = OperatorType::getFunctionType(0, nullptr, sort);
      env.signature->getFunction(symb)->setType(type);

      trm = TermList(Term::createConstant(symb));
    }

    if (!lookup->insert(cName,make_pair(trm,sort))) {
      USER_ERROR("Multiple bindings of symbol "+cName+" in let expression "+exp->toString());
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
  const vstring& theLetAtom = lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theLetAtom),TS_LET);

  // with a list of bindings
  LispListReader bindRdr(lRdr.readList());

  TermLookup* lookup = _scopes.pop();

  // there has to be the body result:
  TermList let;
  unsigned letSort = _results.pop().asTerm(let);

  LOG2("LET body  ",let.toString());

  while (bindRdr.hasNext()) {
    LExprList* pair = bindRdr.readList();
    LispListReader pRdr(pair);

    const vstring& cName = pRdr.readAtom();
    TermList boundExpr;
    _results.pop().asTerm(boundExpr);

    LOG2("BOUND name  ",cName);
    LOG2("BOUND term  ",boundExpr.toString());

    SortedTerm term;
    ALWAYS(lookup->find(cName,term));
    TermList exprTerm = term.first;
    unsigned exprSort = term.second;

    unsigned symbol = 0;
    if (exprSort == Sorts::SRT_BOOL) { // it has to be formula term, with atomic formula
      symbol = exprTerm.term()->getSpecialData()->getFormula()->literal()->functor();
    } else {
      symbol = exprTerm.term()->functor();
    }

    let = TermList(Term::createLet(symbol, nullptr, boundExpr, let, letSort));
  }

  _results.push(ParseResult(letSort,let));

  delete lookup;
}

static const char* UNDERSCORE = "_";

void SMTLIB2::parseMatchBegin(LExpr* exp)
{
  CALL("SMTLIB2::parseMatchBegin");

  LOG2("parseMatchBegin  ",exp->toString());

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the match atom
  const vstring& theMatchAtom = lRdr.readAtom();
  ASS_EQ(theMatchAtom,MATCH);

  // now, there should be an argument
  if (!lRdr.hasNext()) {
    complainAboutArgShortageOrWrongSorts(MATCH,exp);
  }
  vstring argName = lRdr.readAtom();

  // and the list of cases
  if (!lRdr.hasNext()) {
    complainAboutArgShortageOrWrongSorts(MATCH,exp);
  }
  LispListReader casesRdr(lRdr.readList());

  // and that's it
  lRdr.acceptEOL();

  // now read the following bottom up:

  // this will later create the actual match term and kill the lookup
  _todo.push(make_pair(PO_MATCH_END,exp));

  // but we start by asserting the match argument
  TermLookup* lookup = _scopes.pop();
  SortedTerm argTerm;
  if (!lookup->find(argName,argTerm)) {
    complainAboutArgShortageOrWrongSorts(MATCH,exp);
  }
  // we then parse all cases
  while (casesRdr.hasNext()) {
    LExprList* pair = casesRdr.readList();
    LispListReader pRdr(pair);

    LExpr* pattern = pRdr.readNext();
    
    TermLookup* innerLookup = lookup;
    parseMatchPattern(pattern, argTerm.second, innerLookup);
    LExpr* body = pRdr.readNext();

    _scopes.push(innerLookup);
    _todo.push(make_pair(PO_PARSE,pattern));
    _todo.push(make_pair(PO_PARSE,body));
    pRdr.acceptEOL();
  }
}

void SMTLIB2::parseMatchPattern(LExpr* exp, unsigned int sort, TermLookup* lookup)
{
  CALL("SMTLIB2::parseMatchPattern");

  if (exp->isList()) {
    LispListReader tRdr(exp);
    const vstring& consName = tRdr.readAtom();

    if (isTermAlgebraConstructor(consName)) {
      auto fn = env.signature->getFunction(_declaredFunctions.get(consName).first);
      //TODO: improve error messages here
      if (fn->fnType()->result() != sort) {
        complainAboutArgShortageOrWrongSorts(MATCH,exp);
      }
      unsigned argcnt = 0;
      while (tRdr.hasNext()) {
        auto arg = tRdr.readNext();
        parseMatchPattern(arg, fn->fnType()->arg(argcnt), lookup);
        argcnt++;
      }
      if (argcnt != fn->fnType()->arity()) {
        complainAboutArgShortageOrWrongSorts(MATCH,exp);
      }
      return;
    }
    USER_ERROR("'"+consName+"' is not a datatype constructor");
  // base constructor or variable
  } else {
    vstring& id = exp->str;

    if (isTermAlgebraConstructor(id)) {
      auto fn = env.signature->getFunction(_declaredFunctions.get(id).first);
      //TODO: improve error messages here
      if (fn->fnType()->result() != sort || fn->fnType()->arity() != 0) {
        complainAboutArgShortageOrWrongSorts(MATCH,exp);
      }
    } else if (id == UNDERSCORE) {
      // nothing to do here
    } else {
      TermList arg = TermList(_nextVar++, false);

      if (!lookup->insert(id, make_pair(arg, sort))) {
        USER_ERROR("Multiple occurrence of variable "+id+" in match expression");
      }
    }
  }
}

void SMTLIB2::parseMatchEnd(LExpr* exp)
{
  CALL("SMTLIB2::parseMatchEnd");
  LOG2("PO_MATCH_END ",exp->toString());

  // so we know it is let
  ASS(exp->isList());
  LispListReader lRdr(exp->list);
  const vstring& theMatchAtom = lRdr.readAtom();
  ASS_EQ(getBuiltInTermSymbol(theMatchAtom),TS_MATCH);

  vstring argName = lRdr.readAtom();
  LispListReader casesRdr(lRdr.readList());

  TermLookup* lookup = _scopes.pop();

  std::vector<TermList> results;
  while (casesRdr.hasNext()) {
    // there has to be the body result:
    TermList pattern;
    unsigned patternSort = _results.pop().asTerm(pattern);
    TermList body;
    unsigned bodySort = _results.pop().asTerm(body);

    LExprList* pair = casesRdr.readList();
    LispListReader pRdr(pair);

    LOG2("CASE pattern ",pattern.toString());
    LOG2("CASE body    ",body.toString());

    ALWAYS(lookup->find(argName));
    auto arg = lookup->get(argName);
    TermList argTerm = TermList(arg.second, false);
    ASS_EQ(patternSort, arg.second);

    DArray<TermList> elements(3);
    elements[0] = argTerm;
    elements[1] = pattern;
    elements[2] = body;
    DArray<unsigned> sorts(3);
    sorts[0] = arg.second;
    sorts[1] = patternSort;
    sorts[2] = bodySort;
 
    auto caseTuple = TermList(Term::createTuple(3, sorts.begin(), elements.begin()));
    results.push_back(caseTuple);
  }

  ASS(!results.empty());
  // auto sort = results[0].term()->

  // _results.push(ParseResult(letSort,let));

  delete lookup;
}

void SMTLIB2::parseQuantBegin(LExpr* exp)
{
  CALL("SMTLIB2::parseQuantBegin");

  ASS(exp->isList());
  LispListReader lRdr(exp->list);

  // the quant atom
  const vstring& theQuantAtom = lRdr.readAtom();
  ASS(theQuantAtom == FORALL || theQuantAtom == EXISTS);

  // there should next be a list of sorted variables
  LispListReader varRdr(lRdr.readList());

  TermLookup* lookup = new TermLookup();

  while (varRdr.hasNext()) {
    LExprList* pair = varRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    unsigned vSort = declareSort(pRdr.readNext());

    pRdr.acceptEOL();

    if (!lookup->insert(vName,make_pair(TermList(_nextVar++,false),vSort))) {
      USER_ERROR("Multiple occurrence of variable "+vName+" in quantification "+exp->toString());
    }
  }

  _scopes.push(lookup);

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
  const vstring& theExclAtom = lRdr.readAtom();
  ASS_EQ(theExclAtom,EXCLAMATION);

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

  // we ignore the rest in lRdr (no matter the number of remaining arguments and their structure)

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

bool SMTLIB2::parseAsSpecConstant(const vstring& id)
{
  CALL("SMTLIB2::parseAsSpecConstant");

  if (StringUtils::isPositiveInteger(id)) {
    if (_numeralsAreReal) {
      goto real_constant; // just below
    }

    unsigned symb = TPTP::addIntegerConstant(id,_overflow,false);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(Sorts::SRT_INTEGER,res));

    return true;
  }

  if (StringUtils::isPositiveDecimal(id)) {
    real_constant:

    unsigned symb = TPTP::addRealConstant(id,_overflow,false);
    TermList res = TermList(Term::createConstant(symb));
    _results.push(ParseResult(Sorts::SRT_REAL,res));

    return true;
  }

  return false;
}

bool SMTLIB2::parseAsUserDefinedSymbol(const vstring& id,LExpr* exp)
{
  CALL("SMTLIB2::parseAsUserDefinedSymbol");

  DeclaredFunction fun;
  if (!_declaredFunctions.find(id,fun)) {
    return false;
  }

  unsigned symbIdx = fun.first;
  bool isTrueFun = fun.second;

  Signature::Symbol* symbol = isTrueFun ? env.signature->getFunction(symbIdx)
                                        : env.signature->getPredicate(symbIdx);
  OperatorType* type = isTrueFun ? symbol->fnType() : symbol->predType();

  unsigned arity = symbol->arity();

  static Stack<TermList> args;
  args.reset();

  LOG2("DeclaredFunction of arity ",arity);

  for (unsigned i = 0; i < arity; i++) {
    unsigned sort = type->arg(i);

    TermList arg;
    if (_results.isEmpty() || _results.top().isSeparator() ||
        _results.pop().asTerm(arg) != sort) {
      complainAboutArgShortageOrWrongSorts("user defined symbol",exp);
    }

    args.push(arg);
  }

  if (isTrueFun) {
    unsigned sort = symbol->fnType()->result();
    TermList res = TermList(Term::create(symbIdx,arity,args.begin()));
    _results.push(ParseResult(sort,res));
  } else {
    Formula* res = new AtomicFormula(Literal::create(symbIdx,arity,true,false,args.begin()));
    _results.push(ParseResult(res));
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
      unsigned sort = _results.pop().asTerm(first);

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
          _results.pop().asTerm(arg) != Sorts::SRT_REAL) {
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

      Formula::VarList* qvars = nullptr;
      Formula::SortList* qsorts = nullptr;

      TermLookup::Iterator varIt(*_scopes.top());
      while(varIt.hasNext()) {
        SortedTerm vTerm = varIt.next();
        unsigned varIdx = vTerm.first.var();
        unsigned sort = vTerm.second;
        Formula::VarList::push(varIdx, qvars);
        Formula::SortList::push(sort,qsorts);
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
      unsigned sort = _results.pop().asTerm(thenBranch);
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
          _results.pop().asTerm(theInt) != Sorts::SRT_INTEGER) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_TO_REAL);
      TermList res = TermList(Term::create1(fun,theInt));

      _results.push(ParseResult(Sorts::SRT_REAL,res));
      return true;
    }
    case TS_TO_INT:
    {
      TermList theReal;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theReal) != Sorts::SRT_REAL) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::REAL_TO_INT);
      TermList res = TermList(Term::create1(fun,theReal));

      _results.push(ParseResult(Sorts::SRT_INTEGER,res));
      return true;
    }
    case TS_SELECT:
    {
      TermList theArray;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      unsigned arraySortIdx = _results.pop().asTerm(theArray);
      if (!env.sorts->isOfStructuredSort(arraySortIdx,Sorts::StructuredSort::ARRAY)) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      Sorts::ArraySort* arraySort = env.sorts->getArraySort(arraySortIdx);

      TermList theIndex;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theIndex) != arraySort->getIndexSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      if (arraySort->getInnerSort() == Sorts::SRT_BOOL) {
        OperatorType* predType = Theory::getArrayOperatorType(arraySortIdx,Theory::ARRAY_BOOL_SELECT);
        unsigned pred = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,predType);

        Formula* res = new AtomicFormula(Literal::create2(pred,true,theArray,theIndex));

        _results.push(ParseResult(res));
      } else {
        OperatorType* funType = Theory::getArrayOperatorType(arraySortIdx,Theory::ARRAY_SELECT);
        unsigned fun = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,funType);

        TermList res = TermList(Term::create2(fun,theArray,theIndex));

        _results.push(ParseResult(arraySort->getInnerSort(),res));
      }

      return true;
    }
    case TS_STORE:
    {
      TermList theArray;
      if (_results.isEmpty() || _results.top().isSeparator()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      unsigned arraySortIdx = _results.pop().asTerm(theArray);
      if (!env.sorts->isOfStructuredSort(arraySortIdx,Sorts::StructuredSort::ARRAY)) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }
      Sorts::ArraySort* arraySort = env.sorts->getArraySort(arraySortIdx);

      TermList theIndex;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theIndex) != arraySort->getIndexSort()) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      TermList theValue;
      if (_results.isEmpty() || _results.top().isSeparator() ||
          _results.pop().asTerm(theValue) != arraySort->getInnerSort()) {
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
          _results.pop().asTerm(theInt) != Sorts::SRT_INTEGER) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_ABS);
      TermList res = TermList(Term::create1(fun,theInt));

      _results.push(ParseResult(Sorts::SRT_INTEGER,res));

      return true;
    }
    case TS_MOD:
    {
      TermList int1, int2;
      if (_results.isEmpty() || _results.top().isSeparator() || _results.pop().asTerm(int1) != Sorts::SRT_INTEGER ||
          _results.isEmpty() || _results.top().isSeparator() || _results.pop().asTerm(int2) != Sorts::SRT_INTEGER) {
        complainAboutArgShortageOrWrongSorts(BUILT_IN_SYMBOL,exp);
      }

      unsigned fun = env.signature->getInterpretingSymbol(Theory::INT_REMAINDER_E); // TS_MOD is the always positive remainder, therefore INT_REMAINDER_E
      TermList res = TermList(Term::create2(fun,int1,int2));

      _results.push(ParseResult(Sorts::SRT_INTEGER,res));

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
      unsigned sort = _results.pop().asTerm(first);

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
      USER_ERROR("Expected numeral as an argument of a ranked function in "+head->toString());
    }

    unsigned divisorSymb = TPTP::addIntegerConstant(numeral,_overflow,false);
    TermList divisorTerm = TermList(Term::createConstant(divisorSymb));

    TermList arg;
    if (_results.isEmpty() || _results.top().isSeparator() ||
        _results.pop().asTerm(arg) != Sorts::SRT_INTEGER) {
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

    if (_declaredFunctions.find(consName)) {
      DeclaredFunction& f = _declaredFunctions.get(consName);
      if (f.second) {
        TermAlgebraConstructor* c = env.signature->getTermAlgebraConstructor(f.first);
        if (c) /* else the symbol is not a TA constructor */ {

          unsigned sort = env.signature->getFunction(f.first)->fnType()->result();
          if (!c->hasDiscriminator()) {
            // add discriminator predicate
            bool added;
            unsigned pred = env.signature->addPredicate(c->discriminatorName(), 1, added);
            ASS(added);
            OperatorType* type = OperatorType::getPredicateType({ sort });
            env.signature->getPredicate(pred)->setType(type);
            c->addDiscriminator(pred);
            // this predicate is not declare for the parser as it has a reserved name
          }
          TermList arg;
          if (_results.isEmpty() || _results.top().isSeparator() ||
              _results.pop().asTerm(arg) != sort) {
            complainAboutArgShortageOrWrongSorts("ranked function symbol",exp);
          }
          Formula* res = new AtomicFormula(Literal::create1(c->discriminator(),true,arg));
          
          _results.push(ParseResult(res));
          return;
        }
      }
    }
    USER_ERROR("'"+consName+"' is not a datatype constructor");    
  }
  else{
    USER_ERROR("Ranked function application "+headRdr.readAtom()+" not known");
  }
  
}

SMTLIB2::ParseResult SMTLIB2::parseTermOrFormula(LExpr* body)
{
  CALL("SMTLIB2::parseTermOrFormula");

  ASS(_todo.isEmpty());
  ASS(_results.isEmpty());

  _todo.push(make_pair(PO_PARSE,body));

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
              USER_ERROR("Indexed identifiers in general term position are not supported: "+exp->toString());

              // we only support indexed identifiers as functors applied to something (see just below)
            }
          } else {
            // this has to be an UNDERSCORE, otherwise we error later when we PO_PARSE_APPLICATION
          }

          // this handles the general function-to-arguments application:

          _todo.push(make_pair(PO_PARSE_APPLICATION,exp));
          // and all the other arguments too
          while (lRdr.hasNext()) {
            _todo.push(make_pair(PO_PARSE,lRdr.next()));
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

        if (parseAsUserDefinedSymbol(id,exp)) {
          continue;
        }

        if (parseAsBuiltinFormulaSymbol(id,exp)) {
          continue;
        }

        if (parseAsBuiltinTermSymbol(id,exp)) {
          continue;
        }

        USER_ERROR("Unrecognized term identifier "+id);
      }
      case PO_CHECK_ARITY: {
        LOG1("PO_CHECK_ARITY");

        ASS_GE(_results.size(),2);
        ParseResult true_result = _results.pop();
        ParseResult separator   = _results.pop();

        if (true_result.isSeparator() || !separator.isSeparator()) {
          USER_ERROR("Too many arguments in "+exp->toString());
        }
        _results.push(true_result);

        continue;
      }
      case PO_LET_PREPARE_LOOKUP:
        parseLetPrepareLookup(exp);
        continue;
      case PO_LET_END:
        parseLetEnd(exp);
        continue;
      case PO_MATCH_END: {
        parseMatchEnd(exp);
        continue;
      }
    }
  }

  if (_results.size() == 1) {
    return _results.pop();
  } else {
    USER_ERROR("Malformed term expression "+body->toString());
  }
}

void SMTLIB2::readAssert(LExpr* body)
{
  CALL("SMTLIB2::readAssert");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  ParseResult res = parseTermOrFormula(body);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::ASSUMPTION));
  UnitList::push(fu, _formulas);
}

void SMTLIB2::readAssertNot(LExpr* body)
{
  CALL("SMTLIB2::readAssert");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  ParseResult res = parseTermOrFormula(body);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, FromInput(UnitInputType::CONJECTURE));
  fu = new FormulaUnit(new NegatedFormula(fla),
                       FormulaTransformation(InferenceRule::NEGATED_CONJECTURE, fu));
  UnitList::push(fu, _formulas);
}

void SMTLIB2::colorSymbol(const vstring& name, Color color)
{
  CALL("SMTLIB2::colorSymbol");

  if (!_declaredFunctions.find(name)) {
    USER_ERROR("'"+name+"' is not a user symbol");
  }
  DeclaredFunction& f = _declaredFunctions.get(name);

  env.colorUsed = true;
  
  Signature::Symbol* sym = f.second
    ? env.signature->getFunction(f.first)
    : env.signature->getPredicate(f.first);

  sym->addColor(color);
}

}

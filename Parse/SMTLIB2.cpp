/**
 * @file SMTLIB.cpp
 * Implements class SMTLIB.
 */

#include <climits>
#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/NameArray.hpp"
#include "Lib/StringUtils.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Shell/LispLexer.hpp"
#include "Shell/Options.hpp"

#include "SMTLIB2.hpp"

namespace Parse {

SMTLIB2::SMTLIB2(const Options& opts)
: _logicSet(false),
  _logic(LO_INVALID),
  _decimalsAreReal(false)
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
  LExprList::Iterator ite(bench);

  // iteration over benchmark top level entries
  while(ite.hasNext()){
    LExpr* lexp = ite.next();

    cout << lexp->toString(true) << endl;

    LispListReader ibRdr(lexp);

    if (ibRdr.tryAcceptAtom("set-logic")) {
      if (_logicSet) {
        USER_ERROR("set-logic can appear only once in a problem");
      }
      readLogic(ibRdr.readAtom());
      _logicSet = true;
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
      vstring arity = ibRdr.readAtom();

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

    if (ibRdr.tryAcceptAtom("define-fun")) {
      vstring name = ibRdr.readAtom();
      LExprList* iArgs = ibRdr.readList();
      LExpr* oSort = ibRdr.readNext();
      LExpr* body = ibRdr.readNext();

      readDefineFun(name,iArgs,oSort,body);

      ibRdr.acceptEOL();

      continue;
    }

    if (ibRdr.tryAcceptAtom("assert")) {
      readAssert(ibRdr.readNext());

      ibRdr.acceptEOL();

      continue;
    }

    USER_ERROR("unrecognized entry "+ibRdr.readAtom());
  }
}

//  ----------------------------------------------------------------------

const char * SMTLIB2::s_smtlibLogicNameStrings[] = {
    "ALIA",
    "AUFLIA",
    "AUFLIRA",
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
    "UFIDL",
    "UFLIA",
    "UFLRA",
    "UFNIA"
};

SMTLIB2::SmtlibLogic SMTLIB2::getLogic(const vstring& str)
{
  CALL("SMTLIB2::getLogic");

  static NameArray smtlibLogicNames(s_smtlibLogicNameStrings, sizeof(s_smtlibLogicNameStrings)/sizeof(char*));
  ASS_EQ(smtlibLogicNames.length, LO_INVALID);

  int res = smtlibLogicNames.tryToFind(str.c_str());
  if(res==-1) {
    return LO_INVALID;
  }
  return static_cast<SmtlibLogic>(res);
}

void SMTLIB2::readLogic(const vstring& logicStr)
{
  CALL("SMTLIB2::checkLogic");

  _logicName = logicStr;
  _logic = getLogic(_logicName);

  switch (_logic) {
  case LO_ALIA:
  case LO_AUFLIA:
  case LO_AUFLIRA:
  case LO_AUFNIRA:
  case LO_LIA:
  case LO_NIA:
  case LO_QF_ALIA:
  case LO_QF_ANIA:
  case LO_QF_AUFLIA:
  case LO_QF_AUFNIA:
  case LO_QF_AX:
  case LO_QF_IDL:
  case LO_QF_LIA:
  case LO_QF_LIRA:
  case LO_QF_NIA:
  case LO_QF_NIRA:
  case LO_QF_UF:
  case LO_QF_UFIDL:
  case LO_QF_UFLIA:
  case LO_QF_UFNIA:
  case LO_UF:
  case LO_UFIDL:
  case LO_UFLIA:
  case LO_UFNIA:
    break;

  // pure real arithmetic theories treat decimals as Real constants
  case LO_LRA:
  case LO_NRA:
  case LO_QF_LRA:
  case LO_QF_NRA:
  case LO_QF_RDL:
  case LO_QF_UFLRA:
  case LO_QF_UFNRA:
  case LO_UFLRA:
    _decimalsAreReal = true;
    break;

  // we don't support bit vectors
  case LO_BV:
  case LO_QF_ABV:
  case LO_QF_AUFBV:
  case LO_QF_BV:
  case LO_QF_UFBV:
  case LO_UFBV:
    USER_ERROR("unsupported logic "+_logicName);
  default:
    USER_ERROR("unrecognized logic "+_logicName);
  }

}

//  ----------------------------------------------------------------------

const char * SMTLIB2::s_builtInSortNameStrings[] = {
    "Array",
    "Bool",
    "Int",
    "Real"
};

SMTLIB2::BuiltInSorts SMTLIB2::getBuiltInSort(const vstring& str)
{
  CALL("SMTLIB::getBuiltInSort");

  static NameArray builtInSortNames(s_builtInSortNameStrings, sizeof(s_builtInSortNameStrings)/sizeof(char*));
  ASS_EQ(builtInSortNames.length, BS_INVALID);

  int res = builtInSortNames.tryToFind(str.c_str());
  if(res==-1) {
    return BS_INVALID;
  }
  return static_cast<BuiltInSorts>(res);
}

bool SMTLIB2::isSortSymbol(const vstring& name)
{
  CALL("SMTLIB::isSortSymbol");

  if (getBuiltInSort(name) != BS_INVALID) {
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

  if (isSortSymbol(name)) {
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

  if (isSortSymbol(name)) {
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

  ASS_EQ(Sorts::SRT_DEFAULT,0); // there is no default sort in smtlib, so we can use 0 as a separtor results
  static const int SEPARATOR = 0;
  static Stack<unsigned> results;
  ASS(results.isEmpty());

  // evaluation contexts for the expansion of sort definitions
  typedef DHMap<vstring,unsigned> SortLookup;
  static Stack<SortLookup*> lookups;
  ASS(lookups.isEmpty());

  todo.push(make_pair(SPO_PARSE,sExpr));

  while (todo.isNonEmpty()) {
    pair<SortParseOperation,LExpr*> cur = todo.pop();
    SortParseOperation op = cur.first;

    if (op == SPO_POP_LOOKUP) {
      delete lookups.pop();
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

      // try built-ins
      BuiltInSorts bs = getBuiltInSort(id);
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
          // try other options ...
      }

      // try declared sorts
      unsigned arity;
      if (_declaredSorts.find(id,arity)) {
        // building an arbitrary but unique sort string
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

        unsigned newSort = env.sorts->addSort(sortName);
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

        todo.push(make_pair(SPO_POP_LOOKUP,nullptr)); // mark the lookup insertion (see above)
        todo.push(make_pair(SPO_PARSE,def.body));

        continue;
      }

      // must be evaluating defined sort body
      if (lookups.isEmpty()) {
        goto malformed;
      }
      SortLookup* lookup = lookups.top();
      unsigned res;
      if (!lookup->find(id,res)) {
        USER_ERROR("Unrecognized sort identifier "+id);
      }
      results.push(res);
    }
  }

  if (results.size() == 1) {
    return results.pop();
  } else {
    malformed:
    USER_ERROR("Malformed type expression "+sExpr->toString());
  }
}

const char * SMTLIB2::s_formulaSymbolNameStrings[] = {
    "<",
    "<=",
    "=",
    "=>",
    ">",
    ">=",
    "and",
    "distinct",
    "exists",
    "false",
    "forall",
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

const char * SMTLIB2::s_termSymbolNameStrings[] = {
    "*",
    "+",
    "-",
    "/",
    "abs",
    "div",
    "ite",
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

bool SMTLIB2::isFunctionSymbol(const vstring& name)
{
  CALL("SMTLIB2::isFunctionSymbol");

  if (getBuiltInFormulaSymbol(name) != FS_USER_PRED_SYMBOL) {
    return true;
  }

  if (getBuiltInTermSymbol(name) != TS_USER_FUNCTION) {
    return true;
  }

  if (_declaredFunctions.find(name)) {
    return true;
  }

  if (_functionDefinitions.find(name)) {
    return true;
  }

  return false;
}

void SMTLIB2::readDeclareFun(const vstring& name, LExprList* iSorts, LExpr* oSort)
{
  CALL("SMTLIB2::readDeclareFun");

  if (isFunctionSymbol(name)) {
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

void SMTLIB2::declareFunctionOrPredicate(const vstring& name, signed rangeSort, const Stack<unsigned>& argSorts)
{
  CALL("SMTLIB2::declareFunctionOrPredicate");

  bool added;
  unsigned symNum;
  Signature::Symbol* sym;
  BaseType* type;

  if (rangeSort == Sorts::SRT_BOOL) { // predicate
    symNum = env.signature->addPredicate(name, argSorts.size(), added);

    sym = env.signature->getPredicate(symNum);

    type = new PredicateType(argSorts.size(),argSorts.begin());
  } else { // proper function
    symNum = env.signature->addFunction(name, argSorts.size(), added);

    sym = env.signature->getFunction(symNum);

    type = new FunctionType(argSorts.size(), argSorts.begin(), rangeSort);
  }

  ASS(added);
  sym->setType(type);

  ALWAYS(_declaredFunctions.insert(name,std::make_pair(symNum,type->isFunctionType())));
}

//  ----------------------------------------------------------------------

void SMTLIB2::readDefineFun(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body)
{
  CALL("SMTLIB2::readDefineFun");

  if (isFunctionSymbol(name)) {
    USER_ERROR("Redeclaring function symbol: "+name);
  }

  unsigned rangeSort = declareSort(oSort);

  _nextVar = 0;
  ASS(_scopes.isEmpty());
  TermLookup* lookup = new TermLookup();

  static Stack<unsigned> argSorts;
  argSorts.reset();

  LispListReader iaRdr(iArgs);
  while (iaRdr.hasNext()) {
    LExprList* pair = iaRdr.readList();
    LispListReader pRdr(pair);

    vstring vName = pRdr.readAtom();
    unsigned vSort = declareSort(pRdr.readNext());

    if (!lookup->insert(vName,make_pair(TermList(_nextVar++,false),vSort))) {
      USER_ERROR("Multiple occurrence of variable "+vName+" in the definition of function "+name);
    }

    argSorts.push(vSort);
  }

  declareFunctionOrPredicate(name,rangeSort,argSorts);

  // parseTermOrFormula(body);

  // TODO: take the results and finish constructing the whole definition

  // check it's output sort (we are either defining a function or a predicate)

}

bool SMTLIB2::asFormula(ParseResult pr, Formula*& frm)
{
  CALL("SMTLIB2::asFormula");

  if (pr.formula) {
    ASS_EQ(pr.sort, BS_BOOL);
    frm = pr.frm;
    return true;
  }

  if (pr.sort == BS_BOOL) {
    frm = new BoolTermFormula(pr.trm);
    return true;
  }

  return false;
}

SMTLIB2::ParseResult SMTLIB2::parseTermOrFormula(LExpr* body)
{
  CALL("SMTLIB2::parseTermOrFormula");

  enum ParseOperation {
    PO_PARSE,
    PO_CHECK_ARITY
  };
  static Stack<pair<ParseOperation,LExpr*> > todo;
  ASS(todo.isEmpty());

  static Stack<ParseResult> results;
  ASS(results.isEmpty());

  todo.push(make_pair(PO_PARSE,body));

  while (todo.isNonEmpty()) {
    pair<ParseOperation,LExpr*> cur = todo.pop();
    ParseOperation op = cur.first;

    if (op == PO_CHECK_ARITY) {
      if (results.size() < 2) {
        goto malformed;
      }
      ParseResult true_result = results.pop();
      ParseResult separator   = results.pop();

      if (true_result.isSeparator() || !separator.isSeparator()) {
        goto malformed;
      }
      results.push(true_result);

      continue;
    }

    ASS_EQ(op,PO_PARSE);
    LExpr* exp = cur.second;

    if (exp->isList()) {
      LExprList::Iterator lIt(exp->list);

      todo.push(make_pair(PO_CHECK_ARITY,nullptr));
      results.push(ParseResult());

      while (lIt.hasNext()) {
        todo.push(make_pair(PO_PARSE,lIt.next()));
      }
    } else {
      ASS(exp->isAtom());
      vstring& id = exp->str;

      // try built-in formula symbols
      FormulaSymbol fs = getBuiltInFormulaSymbol(id);
      switch (fs) {
        case FS_TRUE:
          results.push(ParseResult(Formula::trueFormula()));
          continue;
        case FS_FALSE:
          results.push(ParseResult(Formula::falseFormula()));
          continue;
        case FS_NOT:
        {
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          Formula* argFla;
          if (!(asFormula(results.pop(),argFla))) {
            goto malformed;
          }
          Formula* res = new NegatedFormula(argFla);
          results.push(ParseResult(res));
          continue;
        }
        case FS_AND:
        case FS_OR:
        {
          FormulaList* argLst = 0;

          unsigned argcnt = 0;
          while (results.isNonEmpty() && (!results.top().isSeparator())) {
            argcnt++;
            Formula* argFla;
            if (!(asFormula(results.pop(),argFla))) {
              goto malformed;
            }
            FormulaList::push(argFla,argLst);
          }

          if (argcnt < 2) {
            goto malformed;
          }

          Formula* res = new JunctionFormula( (fs==FS_AND) ? AND : OR, argLst);
          results.push(ParseResult(res));

          continue;
        }
        case FS_IMPLIES: // done in a right-assoc multiple-argument fassion
        case FS_XOR: // they say XOR should be left-associative, but semantically, it does not matter
        {



          continue;
        }
        default:
          ASS_EQ(fs,FS_USER_PRED_SYMBOL);
          // try other options ...
      }


      /*
    FS_LESS,
    FS_LESS_EQ,
    FS_GREATER,
    FS_GREATER_EQ,
    FS_EQ,

    FS_DISTINCT,

    FS_EXISTS,
    FS_FORALL,

    FS_IS_INT,

      */





    }
  }

  if (results.size() == 1) {
    return results.pop();
  } else {
    malformed:
    USER_ERROR("Malformed term expression "+body->toString());
  }
}

void SMTLIB2::readAssert(LExpr* body)
{
  CALL("SMTLIB2::readAssert");

  _nextVar = 0;
  ASS(_scopes.isEmpty());

  parseTermOrFormula(body);

  // needs to be of sort bool

  // make sure it is a vampire formula (and not bool term) and store it
}

}

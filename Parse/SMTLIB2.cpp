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

#undef LOGGING
#define LOGGING 0

#if LOGGING
#define LOG1(arg) cout << arg << endl;
#define LOG2(a1,a2) cout << a1 << a2 << endl;
#define LOG3(a1,a2,a3) cout << a1 << a2 << a3 << endl;
#else
#define LOG1(arg)
#define LOG2(a1,a2)
#define LOG3(a1,a2,a3)
#endif

namespace Parse {

SMTLIB2::SMTLIB2(const Options& opts)
: _logicSet(false),
  _logic(LO_INVALID),
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

    if (ibRdr.tryAcceptAtom("check-sat")) {
      if (bRdr.hasNext()) {
        LispListReader exitRdr(bRdr.readList());
        if (!exitRdr.tryAcceptAtom("exit")) {
          if(env.options->mode()!=Options::Mode::SPIDER) {
            env.beginOutput();
            env.out() << "Warning: check-sat is not the last entry. Skipping the rest!" << endl;
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
    _numeralsAreReal = true;
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

  ASS_EQ(Sorts::SRT_DEFAULT,0); // there is no default sort in smtlib, so we can use 0 as a results separator
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
    "let",
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

SMTLIB2::DeclaredFunction SMTLIB2::declareFunctionOrPredicate(const vstring& name, signed rangeSort, const Stack<unsigned>& argSorts)
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

    LOG1("declareFunctionOrPredicate-Predicate");
  } else { // proper function
    symNum = env.signature->addFunction(name, argSorts.size(), added);

    sym = env.signature->getFunction(symNum);

    type = new FunctionType(argSorts.size(), argSorts.begin(), rangeSort);

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

  if (isFunctionSymbol(name)) {
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

    TermList arg = TermList(_nextVar++,false);
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

  FormulaUnit* fu = new FormulaUnit(fla, new Inference(Inference::INPUT), Unit::AXIOM);

  UnitList::push(fu, _formulas);
}

bool SMTLIB2::ParseResult::asFormula(Formula*& resFrm)
{
  CALL("SMTLIB2::ParseResult::asFormula");

  if (formula) {
    ASS_EQ(sort, BS_BOOL);
    resFrm = frm;

    LOG2("asFormula formula ",resFrm->toString());
    return true;
  }

  if (sort == BS_BOOL) {
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
    ASS_EQ(sort, BS_BOOL);

    LOG2("asTerm wrap ",frm->toString());

    resTrm = TermList(Term::createFormula(frm));
    return BS_BOOL;
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
      return Theory::REAL_DIVIDE;
    break;

  case TS_DIV:
    if (firstArgSort == Sorts::SRT_INTEGER)
      return Theory::INT_DIVIDE;
    break;

  default:
    ASSERTION_VIOLATION_REP(ts);
  }
    USER_ERROR("invalid sort "+env.sorts->sortName(firstArgSort)+" for interpretation "+vstring(s_termSymbolNameStrings[ts]));
}


SMTLIB2::ParseResult SMTLIB2::parseTermOrFormula(LExpr* body)
{
  CALL("SMTLIB2::parseTermOrFormula");

  enum ParseOperation {
    PO_PARSE,              // takes LExpr*
    PO_CHECK_ARITY,        // takes 0
    PO_LET_PREPARE_LOOKUP, // takes LExpr* (the whole let expression again, why not)
    PO_LET_END             // takes LExpr* (the whole let expression again, why not)
  };
  static Stack<pair<ParseOperation,LExpr*> > todo;
  ASS(todo.isEmpty());

  static Stack<ParseResult> results;
  ASS(results.isEmpty());

  todo.push(make_pair(PO_PARSE,body));

  while (todo.isNonEmpty()) {
    /*
    cout << "Results:" << endl;
    for (unsigned i = 0; i < results.size(); i++) {
      cout << results[i].toString() << endl;
    }
    cout << "---" << endl;
    */

    pair<ParseOperation,LExpr*> cur = todo.pop();
    ParseOperation op = cur.first;

    if (op == PO_CHECK_ARITY) {
      LOG1("PO_CHECK_ARITY");

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

    LExpr* exp = cur.second;

    if (op == PO_LET_PREPARE_LOOKUP) { // this is the second moment of processing let
      LOG2("PO_LET_PREPARE_LOOKUP",exp->toString());

      // so we know it is let
      ASS(exp->isList());
      LispListReader lRdr(exp->list);
      ASS_EQ(getBuiltInTermSymbol(lRdr.readAtom()),TS_LET);

      // with a list of bindings
      LispListReader bindRdr(lRdr.readList());

      // corresponding results have already been parsed
      ParseResult* boundExprs = results.end();

      TermLookup* lookup = new TermLookup();

      while (bindRdr.hasNext()) {
        LExprList* pair = bindRdr.readList();
        LispListReader pRdr(pair);

        const vstring& cName = pRdr.readAtom();
        unsigned sort = (--boundExprs)->sort; // the should be big enough (

        TermList trm;
        if (sort == Sorts::SRT_BOOL) {
          unsigned symb = env.signature->addFreshPredicate(0,"sLP");
          PredicateType* type = new PredicateType(0, nullptr);
          env.signature->getPredicate(symb)->setType(type);

          Formula* atom = new AtomicFormula(Literal::create(symb,0,true,false,nullptr));
          trm = TermList(Term::createFormula(atom));
        } else {
          unsigned symb = env.signature->addFreshFunction (0,"sLF");
          FunctionType* type = new FunctionType(0, nullptr, sort);
          env.signature->getFunction(symb)->setType(type);

          trm = TermList(Term::createConstant(symb));
        }

        if (!lookup->insert(cName,make_pair(trm,sort))) {
          USER_ERROR("Multiple bindings of symbol "+cName+" in let expression "+exp->toString());
        }
      }

      _scopes.push(lookup);

      continue;
    }

    if (op == PO_LET_END) {
      LOG2("PO_LET_END ",exp->toString());

      // so we know it is let
      ASS(exp->isList());
      LispListReader lRdr(exp->list);
      ASS_EQ(getBuiltInTermSymbol(lRdr.readAtom()),TS_LET);

      // with a list of bindings
      LispListReader bindRdr(lRdr.readList());

      TermLookup* lookup = _scopes.pop();

      // there has to be the body result:
      TermList let;
      unsigned letSort = results.pop().asTerm(let);

      LOG2("LET body  ",let.toString());

      while (bindRdr.hasNext()) {
        LExprList* pair = bindRdr.readList();
        LispListReader pRdr(pair);

        const vstring& cName = pRdr.readAtom();
        TermList boundExpr;
        results.pop().asTerm(boundExpr);

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

        let = TermList(Term::createLet(symbol, nullptr, boundExpr, let));
      }

      results.push(ParseResult(letSort,let));

      delete lookup;

      continue;
    }

    ASS_EQ(op,PO_PARSE);

    LOG2("PO_PARSE ",exp->toString());

    if (exp->isList()) {
      LispListReader lRdr(exp->list);

      results.push(ParseResult()); // separator into results
      todo.push(make_pair(PO_CHECK_ARITY,nullptr)); // check as a todo

      // special treatment of some tokens
      LExpr* fst = lRdr.readNext();
      if (fst->isAtom()) {
        vstring& id = fst->str;

        FormulaSymbol fs = getBuiltInFormulaSymbol(id);
        TermSymbol ts = getBuiltInTermSymbol(id);
        if (fs == FS_FORALL || fs == FS_EXISTS) {
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

          todo.push(make_pair(PO_PARSE,fst)); // will create the quantified formula and clear the lookup...
          todo.push(make_pair(PO_PARSE,lRdr.readNext())); // ... from the only remaining argument
          lRdr.acceptEOL();

          continue;
        }

        if (ts == TS_LET) {
          // now, there should be a list of bindings
          LExprList* bindings = lRdr.readList();

          // and the actual body term
          LExpr* body = lRdr.readListExpr();

          // and that's it
          lRdr.acceptEOL();

          // now read the following bottom up:

          // this will later create the actual let term and kill the lookup
          todo.push(make_pair(PO_LET_END,exp));

          // this will parse the let's body (in the context of the lookup)
          todo.push(make_pair(PO_PARSE,body));

          // this will create the lookup when all bindings' expressions are parsed (and their sorts known)
          todo.push(make_pair(PO_LET_PREPARE_LOOKUP,exp));

          // but we start by parsing the bound expressions (first mainly to learn theirs sorts)
          LispListReader bindRdr(bindings);
          while (bindRdr.hasNext()) {
            LExprList* pair = bindRdr.readList();
            LispListReader pRdr(pair);

            pRdr.readAtom(); // for now ignore the identifier
            LExpr* expr = pRdr.readNext();

            todo.push(make_pair(PO_PARSE,expr)); // just parse the expression
            pRdr.acceptEOL();
          }

          continue;
        }
      } else {
        // TODO: indexed identifiers (i.e. divisible)
        goto malformed;
      }

      // this handles the default function-to-arguments application:

      // the first still need to be later processed
      todo.push(make_pair(PO_PARSE,fst));
      // and all the other arguments too
      while (lRdr.hasNext()) {
        todo.push(make_pair(PO_PARSE,lRdr.next()));
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
          if (!(results.pop().asFormula(argFla))) {
            goto malformed;
          }
          Formula* res = new NegatedFormula(argFla);
          results.push(ParseResult(res));
          continue;
        }
        case FS_AND:
        case FS_OR:
        {
          FormulaList* argLst = nullptr;

          LOG1("FS_AND and FS_OR");

          unsigned argcnt = 0;
          while (results.isNonEmpty() && (!results.top().isSeparator())) {
            argcnt++;
            Formula* argFla;
            if (!(results.pop().asFormula(argFla))) {
              goto malformed;
            }
            FormulaList::push(argFla,argLst);
          }

          if (argcnt < 1) { // TODO: officially, we might want to disallow singleton AND and OR, but they are harmless and appear in smtlib
            goto malformed;
          }

          Formula* res;
          if (argcnt > 1) {
            res = new JunctionFormula( (fs==FS_AND) ? AND : OR, argLst);
          } else {
            res = argLst->head();
            argLst->destroy();
          }
          results.push(ParseResult(res));

          continue;
        }
        case FS_IMPLIES: // done in a right-assoc multiple-argument fashion
        case FS_XOR: // they say XOR should be left-associative, but semantically, it does not matter
        {
          Connective con = (fs==FS_IMPLIES) ? IMP : XOR;

          static Stack<Formula*> args;
          ASS(args.isEmpty());

          // put argument formulas on stack (reverses the order)
          while (results.isNonEmpty() && (!results.top().isSeparator())) {
            Formula* argFla;
            if (!(results.pop().asFormula(argFla))) {
              goto malformed;
            }
            args.push(argFla);
          }

          if (args.size() < 2) {
            goto malformed;
          }

          // the last two go first
          Formula* arg_n = args.pop();
          Formula* arg_n_1 = args.pop();
          Formula* res = new BinaryFormula(con, arg_n_1, arg_n);

          // keep on adding in a right-assoc way
          while(args.isNonEmpty()) {
            res = new BinaryFormula(con, args.pop(), res);
          }

          results.push(ParseResult(res));

          continue;
        }
        // all the following are "chainable" and need to respect sorts
        case FS_EQ:
        case FS_LESS:
        case FS_LESS_EQ:
        case FS_GREATER:
        case FS_GREATER_EQ:
        {
          // read the first two arguments
          TermList first;
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          unsigned sort = results.pop().asTerm(first);
          TermList second;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(second) != sort) { // has the same sort as first
            goto malformed;
          }

          Formula* lastConjunct;
          unsigned pred = 0;
          if (fs == FS_EQ) {
            lastConjunct = new AtomicFormula(Literal::createEquality(true, first, second, sort));
          } else {
            Interpretation intp = getFormulaSymbolInterpretation(fs,sort);
            pred = Theory::instance()->getPredNum(intp);
            lastConjunct = new AtomicFormula(Literal::create2(pred,true,first,second));
          }

          FormulaList* argLst = nullptr;
          // for every other argument ... pipelining
          while (results.isEmpty() || !results.top().isSeparator()) {
            TermList next;
            if (results.pop().asTerm(next) != sort) {
              goto malformed;
            }
            // store the old conjunct
            FormulaList::push(lastConjunct,argLst);
            // shift the arguments
            first = second;
            second = next;
            // create next conjunct
            if (fs == FS_EQ) {
              lastConjunct = new AtomicFormula(Literal::createEquality(true, first, second, sort));
            } else {
              lastConjunct = new AtomicFormula(Literal::create2(pred,true,first,second));
            }
          }
          if (argLst == nullptr) { // there were only two arguments, let's return lastConjunct
            results.push(lastConjunct);
          } else {
            // add the last lastConjunct created (pipelining)
            FormulaList::push(lastConjunct,argLst);
            // create the actual conjunction
            Formula* res = new JunctionFormula( AND, argLst);
            results.push(ParseResult(res));
          }

          continue;
        }
        case FS_DISTINCT:
        {
          static Stack<TermList> args;
          args.reset();

          // read the first argument and its sort
          TermList first;
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          unsigned sort = results.pop().asTerm(first);

          args.push(first);

          // put remaining arguments on stack (reverses the order, which does not matter)
          while (results.isNonEmpty() && (!results.top().isSeparator())) {
            TermList argTerm;
            if (results.pop().asTerm(argTerm) != sort) {
              goto malformed;
            }
            args.push(argTerm);
          }

          if (args.size() < 2) {
            goto malformed;
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

          results.push(res);

          continue;
        }
        case FS_IS_INT:
        {
          TermList arg;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(arg) != Sorts::SRT_REAL) {
            goto malformed;
          }

          unsigned pred = Theory::instance()->getPredNum(Theory::REAL_IS_INT);
          Formula* res = new AtomicFormula(Literal::create1(pred,true,arg));

          results.push(res);

          continue;
        }
        case FS_EXISTS:
        case FS_FORALL:
        {
          Formula* argFla;
          if (results.isEmpty() || results.top().isSeparator() ||
              !(results.pop().asFormula(argFla))) {
            goto malformed;
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

          Formula* res = new QuantifiedFormula((fs==FS_EXISTS) ? EXISTS : FORALL, qvars, qsorts, argFla);

          results.push(ParseResult(res));
          continue;
        }

        default:
          ASS_EQ(fs,FS_USER_PRED_SYMBOL);
          // try other options ...
      }

      // try built-in term symbols
      TermSymbol ts = getBuiltInTermSymbol(id);
      switch(ts) {
        case TS_ITE:
        {
          Formula* cond;
          if (results.isEmpty() || results.top().isSeparator() ||
              !(results.pop().asFormula(cond))) {
            goto malformed;
          }
          TermList thenBranch;
          if (results.isEmpty() || results.top().isSeparator()){
            goto malformed;
          }
          unsigned sort = results.pop().asTerm(thenBranch);
          TermList elseBranch;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(elseBranch) != sort){
            goto malformed;
          }

          TermList res = TermList(Term::createITE(cond, thenBranch, elseBranch));

          results.push(ParseResult(sort,res));
          continue;
        }
        case TS_TO_REAL:
        {
          TermList theInt;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theInt) != Sorts::SRT_INTEGER) {
            goto malformed;
          }

          unsigned fun = Theory::instance()->getFnNum(Theory::INT_TO_REAL);
          TermList res = TermList(Term::create1(fun,theInt));

          results.push(ParseResult(Sorts::SRT_REAL,res));
          continue;
        }
        case TS_TO_INT:
        {
          TermList theReal;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theReal) != Sorts::SRT_REAL) {
            goto malformed;
          }

          unsigned fun = Theory::instance()->getFnNum(Theory::REAL_TO_INT);
          TermList res = TermList(Term::create1(fun,theReal));

          results.push(ParseResult(Sorts::SRT_INTEGER,res));
          continue;
        }
        case TS_SELECT:
        {
          TermList theArray;
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          unsigned arraySortIdx = results.pop().asTerm(theArray);
          if (!env.sorts->hasStructuredSort(arraySortIdx,Sorts::StructuredSort::ARRAY)) {
            goto malformed;
          }
          Sorts::ArraySort* arraySort = env.sorts->getArraySort(arraySortIdx);

          TermList theIndex;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theIndex) != arraySort->getIndexSort()) {
            goto malformed;
          }

          if (arraySort->getInnerSort() == Sorts::SRT_BOOL) {
            unsigned pred = Theory::instance()->getSymbolForStructuredSort(arraySortIdx,Theory::StructuredSortInterpretation::ARRAY_BOOL_SELECT);

            Formula* res = new AtomicFormula(Literal::create2(pred,true,theArray,theIndex));

            results.push(ParseResult(res));
          } else {
            unsigned fun = Theory::instance()->getSymbolForStructuredSort(arraySortIdx,Theory::StructuredSortInterpretation::ARRAY_SELECT);
            TermList res = TermList(Term::create2(fun,theArray,theIndex));

            results.push(ParseResult(arraySort->getInnerSort(),res));
          }

          continue;
        }
        case TS_STORE:
        {
          TermList theArray;
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          unsigned arraySortIdx = results.pop().asTerm(theArray);
          if (!env.sorts->hasStructuredSort(arraySortIdx,Sorts::StructuredSort::ARRAY)) {
            goto malformed;
          }
          Sorts::ArraySort* arraySort = env.sorts->getArraySort(arraySortIdx);

          TermList theIndex;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theIndex) != arraySort->getIndexSort()) {
            goto malformed;
          }

          TermList theValue;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theValue) != arraySort->getInnerSort()) {
            goto malformed;
          }

          unsigned fun = Theory::instance()->getSymbolForStructuredSort(arraySortIdx,Theory::StructuredSortInterpretation::ARRAY_STORE);

          TermList args[] = {theArray, theIndex, theValue};
          TermList res = TermList(Term::Term::create(fun, 3, args));

          results.push(ParseResult(arraySortIdx,res));

          continue;
        }
        case TS_ABS:
        {
          TermList theInt;
          if (results.isEmpty() || results.top().isSeparator() ||
              results.pop().asTerm(theInt) != Sorts::SRT_INTEGER) {
            goto malformed;
          }

          unsigned fun = Theory::instance()->getFnNum(Theory::INT_ABS);
          TermList res = TermList(Term::create1(fun,theInt));

          results.push(ParseResult(Sorts::SRT_INTEGER,res));

          continue;
        }
        case TS_MOD:
        {
          TermList int1, int2;
          if (results.isEmpty() || results.top().isSeparator() || results.pop().asTerm(int1) != Sorts::SRT_INTEGER ||
              results.isEmpty() || results.top().isSeparator() || results.pop().asTerm(int2) != Sorts::SRT_INTEGER) {
            goto malformed;
          }

          unsigned fun = Theory::instance()->getFnNum(Theory::INT_MODULO);
          TermList res = TermList(Term::create2(fun,int1,int2));

          results.push(ParseResult(Sorts::SRT_INTEGER,res));

          continue;
        }
        case TS_MULTIPLY:
        case TS_PLUS:
        case TS_MINUS:
        case TS_DIVIDE:
        case TS_DIV:
        {
          // read the first argument
          TermList first;
          if (results.isEmpty() || results.top().isSeparator()) {
            goto malformed;
          }
          unsigned sort = results.pop().asTerm(first);

          if (results.isEmpty() || results.top().isSeparator()) {
            if (ts == TS_MINUS) { // unary minus
              Interpretation intp = getUnaryMinusInterpretation(sort);
              unsigned fun = Theory::instance()->getFnNum(intp);

              TermList res = TermList(Term::create1(fun,first));

              results.push(ParseResult(sort,res));
            } else {
              goto malformed; // we need at least two arguments otherwise
            }
          }

          Interpretation intp = getTermSymbolInterpretation(ts,sort);
          unsigned fun = Theory::instance()->getFnNum(intp);

          TermList second;
          if (results.pop().asTerm(second) != sort) {
            goto malformed;
          }

          TermList res = TermList(Term::create2(fun,first,second));
          while (results.isNonEmpty() && !results.top().isSeparator()) {
            TermList another;
            if (results.pop().asTerm(another) != sort) {
              goto malformed;
            }

            res = TermList(Term::create2(fun,res,another));
          }
          results.push(ParseResult(sort,res));

          continue;
        }
        default:
          ASS_EQ(ts,TS_USER_FUNCTION);
          // try other options ... (TS_LET was handled above)
      }

      // variables from _scopes
      {
        bool found = false;
        Scopes::Iterator sIt(_scopes);
        while (sIt.hasNext()) {
          TermLookup* lookup = sIt.next();

          SortedTerm st;
          if (lookup->find(id,st)) {
            results.push(ParseResult(st.second,st.first));
            found = true;
            break;
          }
        }

        if (found) {
          continue;
        }
      }

      // used defined symbols:
      {
        DeclaredFunction fun;
        if (_declaredFunctions.find(id,fun)) {
          unsigned symbIdx = fun.first;
          bool isTrueFun = fun.second;

          Signature::Symbol* symbol = isTrueFun ? env.signature->getFunction(symbIdx) : env.signature->getPredicate(symbIdx);
          BaseType* type = isTrueFun ? static_cast<BaseType*>(symbol->fnType()) : static_cast<BaseType*>(symbol->predType());

          unsigned arity = symbol->arity();

          static Stack<TermList> args;
          args.reset();

          LOG2("DeclaredFunction of arity ",arity);

          for (unsigned i = 0; i < arity; i++) {
            unsigned sort = type->arg(i);

            TermList arg;
            if (results.isEmpty() || results.top().isSeparator() ||
                results.pop().asTerm(arg) != sort) {
              goto malformed;
            }

            args.push(arg);
          }

          if (isTrueFun) {
            unsigned sort = symbol->fnType()->result();
            TermList res = TermList(Term::create(symbIdx,arity,args.begin()));
            results.push(ParseResult(sort,res));
          } else {
            Formula* res = new AtomicFormula(Literal::create(symbIdx,arity,true,false,args.begin()));
            results.push(ParseResult(res));
          }

          continue;
        }
      }

      // numerals:

      if (StringUtils::isPositiveInteger(id)) {
        if (_numeralsAreReal) {
          goto real_constant; // just below
        }

        unsigned symb;
        try {
          symb = env.signature->addIntegerConstant(id,false);
        } catch (Kernel::ArithmeticException&) {
          USER_ERROR("Cannot represent integer "+id);
        }

        TermList res = TermList(Term::createConstant(symb));
        results.push(ParseResult(Sorts::SRT_INTEGER,res));

        continue;
      }

      if(StringUtils::isPositiveDecimal(id)) {
        real_constant:

        unsigned symb;
        try {
          symb = env.signature->addRealConstant(id,false);
        } catch (Kernel::ArithmeticException&) {
          USER_ERROR("Cannot represent real "+id);
        }

        TermList res = TermList(Term::createConstant(symb));

        results.push(ParseResult(Sorts::SRT_REAL,res));

        continue;
      }

      USER_ERROR("Unrecognized term identifier "+id);
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

  ParseResult res = parseTermOrFormula(body);

  Formula* fla;
  if (!res.asFormula(fla)) {
    USER_ERROR("Asserted expression of non-boolean sort "+body->toString());
  }

  FormulaUnit* fu = new FormulaUnit(fla, new Inference(Inference::INPUT), Unit::AXIOM);

  UnitList::push(fu, _formulas);
}

}

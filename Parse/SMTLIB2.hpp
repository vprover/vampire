/**
 * @file SMTLIB.hpp
 * Defines class SMTLIB.
 */

#ifndef __SMTLIB2__
#define __SMTLIB2__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"

#include "Shell/LispParser.hpp"


namespace Parse {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class SMTLIB2 {
public:
  SMTLIB2(const Options& opts);

  void parse(istream& str);
  void parse(LExpr* bench);

  UnitList* getFormulas() const { return _formulas; }

private:

  enum SmtlibLogic {
    LO_ALIA,
    LO_AUFLIA,
    LO_AUFLIRA,
    LO_AUFNIRA,
    LO_BV,
    LO_LIA,
    LO_LRA,
    LO_NIA,
    LO_NRA,
    LO_QF_ABV,
    LO_QF_ALIA,
    LO_QF_ANIA,
    LO_QF_AUFBV,
    LO_QF_AUFLIA,
    LO_QF_AUFNIA,
    LO_QF_AX,
    LO_QF_BV,
    LO_QF_IDL,
    LO_QF_LIA,
    LO_QF_LIRA,
    LO_QF_LRA,
    LO_QF_NIA,
    LO_QF_NIRA,
    LO_QF_NRA,
    LO_QF_RDL,
    LO_QF_UF,
    LO_QF_UFBV,
    LO_QF_UFIDL,
    LO_QF_UFLIA,
    LO_QF_UFLRA,
    LO_QF_UFNIA,
    LO_QF_UFNRA,
    LO_UF,
    LO_UFBV,
    LO_UFIDL,
    LO_UFLIA,
    LO_UFLRA,
    LO_UFNIA,

    LO_INVALID
  };
  static const char * s_smtlibLogicNameStrings[];

  static SmtlibLogic getLogic(const vstring& str);

  bool _logicSet;
  vstring _logicName;
  SmtlibLogic _logic;

  bool _numeralsAreReal;

  void readLogic(const vstring& logicStr);

  vstring _statusStr;
  vstring _sourceInfo;

  enum BuiltInSorts
  {
    BS_ARRAY,
    BS_BOOL,
    BS_INT,
    BS_REAL,

    BS_INVALID
  };
  static const char * s_builtInSortNameStrings[];
  static BuiltInSorts getBuiltInSort(const vstring& str);

  bool isSortSymbol(const vstring& name);

  // smtlib name -> arity
  DHMap<vstring,unsigned> _declaredSorts;

  void readDeclareSort(const vstring& name, const vstring& arity);

  struct SortDefinition {
    SortDefinition() : args(0), body(0) {}
    SortDefinition(LExprList* args, LExpr* body)
     : args(args), body(body) {}

    LExprList* args;
    LExpr* body;
  };

  DHMap<vstring,SortDefinition> _sortDefinitions;

  void readDefineSort(const vstring& name, LExprList* args, LExpr* body);

  unsigned declareSort(LExpr* sExpr);

  enum FormulaSymbol
  {
    FS_LESS,
    FS_LESS_EQ,
    FS_EQ,
    FS_IMPLIES,
    FS_GREATER,
    FS_GREATER_EQ,
    FS_AND,
    FS_DISTINCT,
    FS_EXISTS,
    FS_FALSE,
    FS_FORALL,
    FS_IS_INT,
    FS_NOT,
    FS_OR,
    FS_TRUE,
    FS_XOR,

    FS_USER_PRED_SYMBOL
  };
  static const char * s_formulaSymbolNameStrings[];

  static FormulaSymbol getBuiltInFormulaSymbol(const vstring& str);

  enum TermSymbol
  {
    TS_MULTIPLY,
    TS_PLUS,
    TS_MINUS,
    TS_DIVIDE,
    TS_ABS,
    TS_DIV,
    TS_ITE,
    TS_LET,
    TS_MOD,
    TS_SELECT,
    TS_STORE,
    TS_TO_INT,
    TS_TO_REAL,

    TS_USER_FUNCTION
  };
  static const char * s_termSymbolNameStrings[];

  static TermSymbol getBuiltInTermSymbol(const vstring& str);

  // in the smt-lib sense, so either a function or predicate symbol
  bool isFunctionSymbol(const vstring& name);

  // <vampire signature id, is_function flag >
  typedef std::pair<unsigned,bool> DeclaredFunction;
  // functions are implicitly declared even when they are defined (see below)
  DHMap<vstring, DeclaredFunction> _declaredFunctions;

  DeclaredFunction declareFunctionOrPredicate(const vstring& name, signed rangeSort, const Stack<unsigned>& argSorts);

  void readDeclareFun(const vstring& name, LExprList* iSorts, LExpr* oSort);

  void readDefineFun(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body);

  // global parsing data structures

  unsigned _nextVar;

  typedef pair<TermList,unsigned> SortedTerm;
  typedef DHMap<vstring,SortedTerm> TermLookup;
  typedef Stack<TermLookup*> Scopes;
  Scopes _scopes;

  struct ParseResult {
    ParseResult() : sort(0), formula(true), frm(nullptr) {} // special separator value

    bool isSeparator() {return sort == 0 && formula && !frm; }

    ParseResult(Formula* frm) : sort(BS_BOOL), formula(true), frm(frm) {}
    ParseResult(unsigned sort, TermList trm) : sort(sort), formula(false), trm(trm) {}

    unsigned sort;
    bool formula;
    union {
      Formula* frm;
      TermList trm;
    };

    bool asFormula(Formula*& resFrm);
    unsigned asTerm(TermList& resTrm);
  };

  Interpretation getFormulaSymbolInterpretation(FormulaSymbol fs, unsigned firstArgSort);
  Interpretation getTermSymbolInterpretation(TermSymbol ts, unsigned firstArgSort);

  ParseResult parseTermOrFormula(LExpr* body);

  void readAssert(LExpr* body);

  UnitList* _formulas;

  void readBenchmark(LExprList* bench);
};

}

#endif // __SMTLIB2__

/**
 * @file SMTLIB.hpp
 * Defines class SMTLIB.
 */

#ifndef __SMTLIB2__
#define __SMTLIB2__

#include "Forwards.hpp"

#include "Lib/Set.hpp"

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

  /** Parse from an open stream */
  void parse(istream& str);
  /** Parse a ready lisp expression */
  void parse(LExpr* bench);

  /** Formulas obtained during parsing:
   *  1) equations collected from "define-fun"
   *  2) general formulas collected from "assert"
   *
   *  Global signature in env is updated on the fly.
   *
   *  We don't know what the conjecture is.
   **/
  UnitList* getFormulas() const { return _formulas; }

  /**
   * List of currently used logics:
   * QF (quantifier free) should be ground
   * A - arrays
   * (L/N)(I/R/both)A - linear/non-linear integer/real/both arithmetic
   * BV - bit vector - we don't support
   * (I/R)DL - difference logic - we don't treat specially (fragment of L(I/R)A)
   * UF - uninterpreted function = first order we know and love
   *
   * In general, the parser does not check that the parse content belongs to the advertised logic.
   */
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

  /**
   * Return the parsed logic (or LO_INVALID if not set).
   */
  SmtlibLogic getLogic() const {
    return _logic;
  }

private:

  static const char * s_smtlibLogicNameStrings[];

  /**
   * Maps a string to a SmtlibLogic value.
   */
  static SmtlibLogic getLogicFromString(const vstring& str);

  /**
   * Have we seen "set-logic" entry yet?
   */
  bool _logicSet;

  /**
   * The advertised logic.
   */
  SmtlibLogic _logic;

  /**
   * Logics which contains only reals allow numerals (like '123') to be understood as reals.
   * When both Ints and Reals are mixed numerals are Ints and decimals (like '123.0') are reals.
   *
   * This is determined based on the advertised logic (and not the actual content of the file).
   */
  bool _numeralsAreReal;

  /**
   * Handle "set-logic" entry.
   */
  void readLogic(const vstring& logicStr);

  /** Content of the ":status: info entry. */
  vstring _statusStr;
  /** Content of the ":source: info entry. */
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

  /**
   * Maps smtlib built-in sort name to BuiltInSorts value.
   */
  static BuiltInSorts getBuiltInSortFromString(const vstring& str);

  /**
   * Test string for being either a built-in sort
   * or a sort already declared or defined within this parser object.
   */
  bool isAlreadyKnownSortSymbol(const vstring& name);

  /** Maps smtlib name of a declared sort to its arity.
   *
   * Declared sorts are just names with arity-many "argument slots".
   * However, this is just a way to make new sorts from old ones.
   * There is no implied semantic relation to the argument sorts.
   */
  DHMap<vstring,unsigned> _declaredSorts;

  /**
   * Handle "declare-sort" entry.
   */
  void readDeclareSort(const vstring& name, const vstring& arity);

  /**
   * Sort definition is a macro (with arguments) for a complex sort expression.
   *
   * We don't parse the definition until it is used.
   *
   * Then a lookup context is created mapping
   * symbolic arguments from the definition to actual arguments from the invocation
   * and the invocation is parsed as the defined body in this context.
   */
  struct SortDefinition {
    SortDefinition() : args(0), body(0) {}
    SortDefinition(LExprList* args, LExpr* body)
     : args(args), body(body) {}

    LExprList* args;
    LExpr* body;
  };

  /**
   * Maps smtlib name of a defined sort to its SortDefinition struct.
   */
  DHMap<vstring,SortDefinition> _sortDefinitions;

  /**
   * Handle "define-sort" entry.
   */
  void readDefineSort(const vstring& name, LExprList* args, LExpr* body);

  /**
   * Take an smtlib sort expression, evaluate it in the context of previous
   * sort declarations and definitions,
   * register any missing sort in vampire and return vampire's sort id
   * corresponding to the give expression.
   */
  unsigned declareSort(LExpr* sExpr);

  /**
   * Some built-in symbols represent functions with result of sort Bool.
   * They are listed here.
   */
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

  /**
   * Lookup to see if vstring is a built-in FormulaSymbol.
   */
  static FormulaSymbol getBuiltInFormulaSymbol(const vstring& str);

  /**
   * Some built-in symbols represent functions with not-Bool result of sort
   * and are listed here.
   */
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

  /**
   * Lookup to see if vstring is a built-in TermSymbol.
   */
  static TermSymbol getBuiltInTermSymbol(const vstring& str);

  /**
   * Is the given vstring a built-in FormulaSymbol, built-in TermSymbol or a declared function?
   */
  bool isAlreadyKnownFunctionSymbol(const vstring& name);

  /** <vampire signature id, is_function flag (otherwise it is a predicate) > */
  typedef std::pair<unsigned,bool> DeclaredFunction;
  /** functions are implicitly declared also when they are defined (see below) */
  DHMap<vstring, DeclaredFunction> _declaredFunctions;

  /**
   * Given a symbol name, range sort (which can be Bool) and argSorts,
   * register a new function (or predicate) symbol in vampire,
   * store the ensuing DeclaredFunction in _declaredFunctions
   * and return it.
   */
  DeclaredFunction declareFunctionOrPredicate(const vstring& name, signed rangeSort, const Stack<unsigned>& argSorts);

  /**
   * Handle "declare-fun" entry.
   *
   * Declaring a function just extends the signature.
   */
  void readDeclareFun(const vstring& name, LExprList* iSorts, LExpr* oSort);

  /**
   * Handle "define-fun" entry.
   *
   * Defining a function extends the signature and adds the new function's definition into _formulas.
   */
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
    vstring toString();
  };

  Interpretation getFormulaSymbolInterpretation(FormulaSymbol fs, unsigned firstArgSort);
  Interpretation getUnaryMinusInterpretation(unsigned argSort);
  Interpretation getTermSymbolInterpretation(TermSymbol ts, unsigned firstArgSort);

  ParseResult parseTermOrFormula(LExpr* body);

  void readAssert(LExpr* body);

  UnitList* _formulas;

  Set<vstring> _overflow;

  void readBenchmark(LExprList* bench);
};

}

#endif // __SMTLIB2__

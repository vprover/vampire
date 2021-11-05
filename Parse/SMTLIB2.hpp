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
 * @file SMTLIB.hpp
 * Defines class SMTLIB.
 */

#ifndef __SMTLIB2__
#define __SMTLIB2__

#include "Forwards.hpp"

#include "Lib/Set.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
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
   * Return the parsed logic (or LO_INVALID if not set).
   */
  SMTLIBLogic getLogic() const {
    return _logic;
  }

  const vstring& getStatus() const {
    return _statusStr;
  }

private:

  static const char * s_smtlibLogicNameStrings[];

  /**
   * Maps a string to a SmtlibLogic value.
   */
  static SMTLIBLogic getLogicFromString(const vstring& str);

  /**
   * Have we seen "set-logic" entry yet?
   */
  bool _logicSet;

  /**
   * The advertised logic.
   */
  SMTLIBLogic _logic;

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
  TermList declareSort(LExpr* sExpr);

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
    TS_MATCH,
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
  DeclaredFunction declareFunctionOrPredicate(const vstring& name, TermList rangeSort, const TermStack& argSorts);

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
  void readDefineFun(const vstring& name, LExprList* iArgs, LExpr* oSort, LExpr* body, bool recursive = false);

  void readDeclareDatatype(LExpr* sort, LExprList* datatype);

  void readDeclareDatatypes(LExprList* sorts, LExprList* datatypes, bool codatatype = false);

  TermAlgebraConstructor* buildTermAlgebraConstructor(vstring constrName, TermList taSort,
                                                      Stack<vstring> destructorNames, TermStack argSorts);

  /**
   * Parse result of parsing an smtlib term (which can be of sort Bool and therefore represented in vampire by a formula)
   */
  struct ParseResult {
    /** Construct special separator value */
    ParseResult() : formula(true), frm(nullptr) {
      sort = TermList(0, true);
    }

    bool isSeparator() { return sort.isSpecialVar() && formula && !frm; }

    bool isSharedTerm() { return !formula && (!trm.isTerm() || trm.term()->shared()); }

    /** Construct ParseResult from a formula */
    ParseResult(Formula* frm) : sort(AtomicSort::boolSort()), formula(true), frm(frm) {}
    /** Construct ParseResult from a term of a given sort */
    ParseResult(TermList sort, TermList trm) : sort(sort), formula(false), trm(trm) {}

    TermList sort;
    bool formula;
    /** The label assigned to this formula using the ":named" annotation of SMT-LIB2;
     * empty string means no label. */
    vstring label;
    union {
      Formula* frm;
      TermList trm;
    };

    /**
     * Try interpreting ParseResult as a formula
     * (which may involve unwrapping a formula special term
     * or wrapping a Bool sorted term as BoolTermFormula)
     * and indicate success by returning true.
     */
    bool asFormula(Formula*& resFrm);
    /**
     * Interpret ParseResult as term
     * and return its vampire sort (which may be Sorts::SRT_BOOL).
     */
    TermList asTerm(TermList& resTrm);
    /**
     * Records a label for the formula represented by this `ParserResult`,
     * resulting from a ":named" SMT-LIB2 annotation.
     */
    void setLabel(vstring l){ label = l; }
    /**
     * Helper that attaches a label to a `Formula`
     * if a label is recorded for this `ParserResult`.
     * Returns the formula.
     */
    Formula* attachLabelToFormula(Formula* frm);

    vstring toString();
  };

  /** Return Theory::Interpretation for overloaded arithmetic comparison operators based on their argSort (either Int or Real) */
  Interpretation getFormulaSymbolInterpretation(FormulaSymbol fs, TermList firstArgSort);
  /** Return Theory::Interpretation for overloaded unary minus operator based on its argSort (either Int or Real) */
  Interpretation getUnaryMinusInterpretation(TermList argSort);
  /** Return Theory::Interpretation for overloaded arithmetic operators based on its argSort (either Int or Real) */
  Interpretation getTermSymbolInterpretation(TermSymbol ts, TermList firstArgSort);
  

  // global parsing data structures -- BEGIN

  /** For generating fresh vampire variables */
  unsigned _nextVar;

  /** < termlist, vampire sort id > */
  typedef pair<TermList,TermList> SortedTerm;
  /** mast an identifier to SortedTerm */
  typedef DHMap<vstring,SortedTerm> TermLookup;
  typedef Stack<TermLookup*> Scopes;
  /** Stack of parsing contexts:
   * for variables from quantifiers and
   * for symbols bound by let (which are variables from smtlib perspective,
   * but require a true function/predicate symbol by vampire )
   */
  Scopes _scopes;

  /**
   * Stack of partial results used by parseTermOrFormula below.
   */
  Stack<ParseResult> _results;

  /**
   * Possible operations during parsing a term.
   */
  enum ParseOperation {
    // general top level parsing request
    PO_PARSE,              // takes LExpr*
    // when parsing "(something args...)" the following operation will be scheduled for "something"
    PO_PARSE_APPLICATION,  // takes LExpr* (the whole term again, for better error reporting)
    // after "(something args...)" is parsed the following makes sure that there is exactly one proper result on the result stack above a previously inserted separator
    PO_CHECK_ARITY,        // takes LExpr* (again the whole, just for error reporting)
    // this is a special operation for handling :named labels
    PO_LABEL,              // takes a LExpr* of the label to be applied to the top _result
    // these two are intermediate cases for handling let
    PO_LET_PREPARE_LOOKUP, // takes LExpr* (the whole let expression again, why not)
    PO_LET_END,            // takes LExpr* (the whole let expression again, why not)
    PO_MATCH_CASE_START,   // takes LExpr*, a list containing the matched term, pattern, case
    PO_MATCH_CASE_END,     // takes LExpr*, a list containing the matched term, pattern, case
    PO_MATCH_END           // takes LExpr* (the whole match again)
  };
  /**
   * Main smtlib term parsing stack.
   */
  Stack<pair<ParseOperation,LExpr*> > _todo;

  // global parsing data structures -- END

  // a few helper functions enabling the body of parseTermOrFormula be of reasonable size

  [[noreturn]] void complainAboutArgShortageOrWrongSorts(const vstring& symbolClass, LExpr* exp);

  void parseLetBegin(LExpr* exp);
  void parseLetPrepareLookup(LExpr* exp);
  void parseLetEnd(LExpr* exp);

  bool isTermAlgebraConstructor(const vstring& name);
  void parseMatchBegin(LExpr* exp);
  void parseMatchCaseStart(LExpr* exp);
  void parseMatchCaseEnd(LExpr* exp);
  void parseMatchEnd(LExpr* exp);

  void parseQuantBegin(LExpr* exp);

  void parseAnnotatedTerm(LExpr* exp);

  /** Scope's are filled by forall, exists, and let */
  bool parseAsScopeLookup(const vstring& id);
  /** Currently either numeral or decimal */
  bool parseAsSpecConstant(const vstring& id);
  /** Declared or defined functions (and predicates) - which includes 0-arity ones */
  bool parseAsUserDefinedSymbol(const vstring& id, LExpr* exp);
  /** Whatever is built-in and looks like a formula from vampire perspective (see FormulaSymbol)
   * - includes the second half of parsing quantifiers */
  bool parseAsBuiltinFormulaSymbol(const vstring& id, LExpr* exp);
  /** Whatever is built-in and looks like a term from vampire perspective (see TermSymbol)
   * - excludes parts for dealing with let */
  bool parseAsBuiltinTermSymbol(const vstring& id, LExpr* exp);

  /** Parsing things like "((_ divisible 5) x)" */
  void parseRankedFunctionApplication(LExpr* exp);

  /**
   * Main term parsing routine.
   * Assumes "global parsing data structures" initialized.
   * Returns the body's value as a ParseResult.
   *
   * Currently unsupported features (see http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.5-r2015-06-28.pdf):
   * - qualified identifiers "(as f s)"
   * - hexadecimal, binary and string spec_constants
   * - :named expressions "(! (> x y) :named p1)" cause a user error.
   *    They could also be ignored, but smtlib dictates that
   *    1) the named term has to be closed (needs an extra check),
   *    2) the new name can be used elsewhere (also already in the term being parsed in the in-order traversal)
   *   So the proper behavior would be more difficult to support.
   * - "define-funs-rec" and "define-fun-rec"; syntactically these would be fine,
   *  but any reasonable use will rely on some well-founded semantics which can only be supported with care
   *
   * Ignored feature:
   * - quantifier patterns: " (forall (( x0 A) (x1 A) (x2 A)) (! (=> (and (r x0 x1) (r x1 x2 )) (r x0 x2 )) : pattern ((r x0 x1) (r x1 x2 )) : pattern ((p x0 a)) ))
   *  the patter information is lost and the pattern data is not checked semantically.
   *
   * Violates standard:
   * - requires variables under a single quantifier to be distinct
   * - the rule that "variables cannot have the same name as a theory function symbol in the same scope" is currently ignored
   */
  ParseResult parseTermOrFormula(LExpr* body);

  /**
   * Handle "assert" entry.
   *
   * On success results in a single formula added to _formulas.
   */
  void readAssert(LExpr* body);

  /**
   * Unofficial command
   *
   * Behaves like conjecture declaration in TPTP
   */
  void readAssertNot(LExpr* body);

  /**
   * Unofficial command
   *
   * Behaves like assert, but marks body clause as external theory axiom.
   * Assumes that body is already fully simplified (as this is usual the case for theory axioms).
   */
  void readAssertTheory(LExpr* body);

  /**
   * Unofficial command
   *
   * Behaves like conjecture declaration in TPTP
   */
  void colorSymbol(const vstring& name, Color color);

  /**
   * Units collected during parsing.
   */
  UnitList* _formulas;

  /**
   * To support a mechanism for dealing with large arithmetic constants.
   * Adapted from the tptp parser.
   */
  Set<vstring> _overflow;

  /**
   * Toplevel parsing dispatch for a benchmark.
   */
  void readBenchmark(LExprList* bench);
};

}

#endif // __SMTLIB2__

/**
 * @file SMTLIB.hpp
 * Defines class SMTLIB.
 */

#ifndef __SMTLIB2__
#define __SMTLIB2__

#include "Forwards.hpp"

#include "Lib/Set.hpp"

#include "Kernel/Signature.hpp"
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
   * Return the parsed logic (or LO_INVALID if not set).
   */
  SMTLIBLogic getLogic() const {
    return _logic;
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
    BS_BITVECTOR,
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
    FS_BVSGE,
    FS_BVSGT,
    FS_BVSLE,
    FS_BVSLT,
    FS_BVUGE,
    FS_BVUGT,
    FS_BVULE,
    FS_BVULT,
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
    TS_UNDERSCORE,
    TS_ABS,
    TS_BVADD,
    TS_BVAND,
    TS_BVASHR,
    TS_BVCOMP,
    TS_BVLSHR,
    TS_BVMUL,
    TS_BVNAND,
    TS_BVNEG,
    TS_BVNOR, 
    TS_BVNOT,
    TS_BVOR,
    TS_BVSDIV, 
    TS_BVSHL,
    TS_BVSMOD,
    TS_BVSREM,
    TS_BVSUB,
    TS_BVUDIV,
    TS_BVUREM,
    TS_BVXNOR,
    TS_BVXOR,
    TS_CONCAT,
    TS_DIV,
    TS_EXTRACT,
    TS_ITE,
    TS_LET,
    TS_MOD,
    TS_REPEAT,
    TS_BV_ROTATE_LEFT,
    TS_BV_ROTATE_RIGHT,
    TS_SELECT,
    TS_BV_SIGN_EXTEND,
    TS_STORE,
    TS_TO_INT,
    TS_TO_REAL,
    TS_BV_ZERO_EXTEND,
    
    TS_USER_FUNCTION
  };
  static const char * s_termSymbolNameStrings[];
  /////////////// TODO: move operations
  DArray<char> getHexArrayFromString(vstring& input)
{
    DArray<char> result(input.length());
    for (int i = input.length()-1, j = 0; i>=0; --i,++j){
        if ((input.at(i) >= '0' && input.at(i) <= '9') || (input.at(i) >= 'a' && input.at(i) <= 'f') || (input.at(i) >= 'A' && input.at(i) <= 'F'))
            result[j] = input[j];
        else
            USER_ERROR("Problem with the hexadecimal");
    }
    return result;
}  
int getNumberFromHexArray(DArray<char> input)
{
    int result = 0;
     for (int i = 0 ; i< input.size();++i)
         result += ((input[i] - '0') * pow(16,i));
    return result;
}
  
int getIntValueFromHex(char in)
{
    if (in>= '0' && in<= '9')
        return (in - '0');
    switch (in){
        case 'a':
        case 'A':
            return 10;
        case 'b':
        case 'B':
            return 11;
        case 'c':
        case 'C':
            return 12;
        case 'd':
        case 'D':
            return 13; 
        case 'e':
        case 'E':
            return 14;
        case 'f':
        case 'F':
            return 15; 
        default:
            USER_ERROR("expected a numeral or char between a and f");
            
    }
}

 DArray<bool> getBoolArrayFromString(vstring& input)
 {
    DArray<bool> result(input.length());
    for (int j = 0, i = input.length()-1; i>=0;--i, ++j){
        if (input.at(j) == '0')
            result[i] = false;
        else if (input.at(j) == '1')
            result[i] = true;
        else
            USER_ERROR("Zero or ones expected");
        
    }
    return result;

  }
 
 int getNumberFromBoolArray(DArray<bool> a){
     int result = 0;
     for (int i = 0 ; i< a.size();++i){
         unsigned toAdd = 0;
         if (a[i] == true)
             toAdd = pow(2,i);
         result+=toAdd;
     }
     return result;
 }
  //////////////
 /* get the ssi from ts, eg: argument is TS_CONCAT, it returns StructuredSortInterpretation::CONCAT*/
  Theory::StructuredSortInterpretation getSSIfromTS(TermSymbol ts){
      switch(ts){
          case TS_BVADD:
              return Theory::StructuredSortInterpretation::BVADD;
          case TS_BVAND:
              return Theory::StructuredSortInterpretation::BVAND;
          case TS_BVASHR:
              return Theory::StructuredSortInterpretation::BVASHR;
          case TS_BVCOMP:
              return Theory::StructuredSortInterpretation::BVCOMP;
          case TS_BVLSHR:
              return Theory::StructuredSortInterpretation::BVLSHR;
          case TS_BVMUL:
              return Theory::StructuredSortInterpretation::BVMUL;
          case TS_BVNAND:
              return Theory::StructuredSortInterpretation::BVNAND;
          case TS_BVNEG:
              return Theory::StructuredSortInterpretation::BVNEG;
          case TS_BVNOR:
              return Theory::StructuredSortInterpretation::BVNOR;
          case TS_BVNOT:
              return Theory::StructuredSortInterpretation::BVNOT;
          case TS_BVOR:
              return Theory::StructuredSortInterpretation::BVOR;
          case TS_BVSDIV:
              return Theory::StructuredSortInterpretation::BVSDIV;
          case TS_BVSMOD:
              return Theory::StructuredSortInterpretation::BVSMOD;
          case TS_BVSHL:
              return Theory::StructuredSortInterpretation::BVSHL;
          case TS_BVSREM:
              return Theory::StructuredSortInterpretation::BVSREM;
           case TS_BVSUB:
              return Theory::StructuredSortInterpretation::BVSUB;
          case TS_BVUDIV:
              return Theory::StructuredSortInterpretation::BVUDIV;
          case TS_BVUREM:
              return Theory::StructuredSortInterpretation::BVUREM;
          case TS_BVXNOR:
              return Theory::StructuredSortInterpretation::BVXNOR;
          case TS_BVXOR:
              return Theory::StructuredSortInterpretation::BVXOR;
          case TS_BV_ZERO_EXTEND:
              return Theory::StructuredSortInterpretation::BV_ZERO_EXTEND;
          case TS_BV_SIGN_EXTEND:
              return Theory::StructuredSortInterpretation::BV_SIGN_EXTEND;
          case TS_BV_ROTATE_LEFT:
              return Theory::StructuredSortInterpretation::BV_ROTATE_LEFT;
          case TS_BV_ROTATE_RIGHT:
              return Theory::StructuredSortInterpretation::BV_ROTATE_RIGHT;
          case TS_REPEAT:
              return Theory::StructuredSortInterpretation::REPEAT;    
          default:
              ASS_EQ(1,2);    
              
      }
  }
  
  Theory::StructuredSortInterpretation getSSIfromFS(FormulaSymbol fs){
      switch(fs){
          case FS_BVSLT:
              return Theory::StructuredSortInterpretation::BVSLT;
          case FS_BVULE:
              return Theory::StructuredSortInterpretation::BVULE;
          case FS_BVUGT:
              return Theory::StructuredSortInterpretation::BVUGT;
          case FS_BVUGE:
              return Theory::StructuredSortInterpretation::BVUGE;
          case FS_BVSLE:
              return Theory::StructuredSortInterpretation::BVSLE;
          case FS_BVSGT:
              return Theory::StructuredSortInterpretation::BVSGT;
          case FS_BVSGE:
              return Theory::StructuredSortInterpretation::BVSGE;
          case FS_BVULT:
              return Theory::StructuredSortInterpretation::BVULT;
              
          default:
              ASS_EQ(1,2);    
        }
  }
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

  void readDeclareDatatypes(LExprList* sorts, LExprList* datatypes, bool codatatype = false);

  TermAlgebraConstructor* buildTermAlgebraConstructor(vstring constrName, unsigned taSort,
                                                      Stack<vstring> destructorNames, Stack<unsigned> argSorts);

  /**
   * Parse result of parsing an smtlib term (which can be of sort Bool and therefore represented in vampire by a formula)
   */
  struct ParseResult {
    /** Construct special separator value */
    ParseResult() : sort(0), formula(true), frm(nullptr) {}

    bool isSeparator() { return sort == 0 && formula && !frm; }

    bool isSharedTerm() { return !formula && (!trm.isTerm() || trm.term()->shared()); }

    /** Construct ParseResult from a formula */
    ParseResult(Formula* frm) : sort(Sorts::SRT_BOOL), formula(true), frm(frm) {}
    /** Construct ParseResult from a term of a given sort */
    ParseResult(unsigned sort, TermList trm) : sort(sort), formula(false), trm(trm) {}

    unsigned sort;
    bool formula;
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
    unsigned asTerm(TermList& resTrm);

    vstring toString();
  };

  /** Return Theory::Interpretation for overloaded arithmetic comparison operators based on their argSort (either Int or Real) */
  Interpretation getFormulaSymbolInterpretation(FormulaSymbol fs, unsigned firstArgSort);
  /** Return Theory::Interpretation for overloaded unary minus operator based on its argSort (either Int or Real) */
  Interpretation getUnaryMinusInterpretation(unsigned argSort);
  /** Return Theory::Interpretation for overloaded arithmetic operators based on its argSort (either Int or Real) */
  Interpretation getTermSymbolInterpretation(TermSymbol ts, unsigned firstArgSort);


  // global parsing data structures -- BEGIN

  /** For generating fresh vampire variables */
  unsigned _nextVar;

  /** < termlist, vampire sort id > */
  typedef pair<TermList,unsigned> SortedTerm;
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
    // these two are intermediate cases for handling let
    PO_LET_PREPARE_LOOKUP, // takes LExpr* (the whole let expression again, why not)
    PO_LET_END             // takes LExpr* (the whole let expression again, why not)
  };
  /**
   * Main smtlib term parsing stack.
   */
  Stack<pair<ParseOperation,LExpr*> > _todo;

  // global parsing data structures -- END

  // a few helper functions enabling the body of parseTermOrFormula be of reasonable size

  void complainAboutArgShortageOrWrongSorts(const vstring& symbolClass, LExpr* exp) NO_RETURN;

  void parseLetBegin(LExpr* exp);
  void parseLetPrepareLookup(LExpr* exp);
  void parseLetEnd(LExpr* exp);

  void parseQuantBegin(LExpr* exp);

  void parseAnnotatedTerm(LExpr* exp);
  void parseUnderScoredExpression(LExpr* exp);
  /** Scope's are filled by forall, exists, and let */
  bool parseAsScopeLookup(const vstring& id);
  /** Currently either numeral or decimal */
  bool parseAsSpecConstant(const vstring& id);
  /** to parse bv231 and the like*/
  bool parseAsBitVectorDescriptor(const vstring& id);
  /* to parse constants such as #b0101 or #xA891f */
  bool parseAsBitVectorConstant(const vstring& id);
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

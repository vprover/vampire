
/*
 * File SMTLIB.hpp.
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
 * @file SMTLIB.hpp
 * Defines class SMTLIB.
 */

#ifndef __SMTLIB__
#define __SMTLIB__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"

#include "Shell/LispParser.hpp"


namespace Parse {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class SMTLIB {
public:
  enum Mode {
    READ_BENCHMARK = 0,
    DECLARE_SORTS = 1,
    DECLARE_SYMBOLS = 2,
    BUILD_FORMULA = 3
  };

  /**
   * Information from a function or predicate declaration
   */
  struct FunctionInfo {
    FunctionInfo(vstring name, Stack<vstring> argSorts, vstring domainSort)
     : name(name), argSorts(argSorts), rangeSort(domainSort) {}

    vstring name;
    Stack<vstring> argSorts;
    vstring rangeSort;
  };

  SMTLIB(const Options& opts, Mode mode = BUILD_FORMULA);
  void setIntroducedSymbolColor(Color clr) { _introducedSymbolColor = clr; }

  /**
   * @param bench lisp list having atom "benchmark" as the first element
   */
  void parse(LExpr* bench);
  void parse(istream& str);

  //these functions can be used after a call to a parse() function
  const Stack<vstring>& getUserSortNames() const { return _userSorts; }
  const Stack<FunctionInfo>& getFuncInfos() const { return _funcs; }
  LExpr* getLispFormula() const { ASS(_lispFormula); return _lispFormula; }

  /**
   * Return type of a function specified by fnInfo.
   *
   * This function can be called if the mode is at least DECLARE_SORTS.
   */
  OperatorType* getSymbolType(const FunctionInfo& fnInfo);

  /**
   * Return parsed formula.
   *
   * This function can be called after calling some of the parse() functions and
   * when the mode in is set to BUILD_FORMULA.
   */
  UnitList* getFormulas() const { ASS(_formulas); return _formulas; }
  UnitList* getDefinitions() const { ASS(_formulas); return _definitions; }

private:

  enum BuiltInSorts
  {
    BS_ARRAY1,
    BS_ARRAY2,
    BS_INT,
    BS_REAL,
    BS_U,

    BS_INVALID
  };
  static const char * s_builtInSortNameStrings[];

  static BuiltInSorts getBuiltInSort(vstring str);

  void readBenchmark(LExprList* bench);
  void readSort(vstring name);
  void readFunction(LExprList* decl);
  void readPredicate(LExprList* decl);

  unsigned getSort(vstring name);
  unsigned getSort(BuiltInSorts srt);
  void doSortDeclarations();
  void doFunctionDeclarations();

  vstring _benchName;
  vstring _statusStr;

  Stack<vstring> _userSorts;
  Stack<FunctionInfo> _funcs;
  LExprList* _lispAssumptions;
  LExpr* _lispFormula;

  UnitList* _definitions;
  /**
   * Contains definitions and the top formula
   */
  UnitList* _formulas;

  Mode _mode;
  bool _treatIntsAsReals;
  // unsigned _defIntroThreshold;
  bool _fletAsDefinition;
  Color _introducedSymbolColor;
#if VDEBUG
  bool _haveParsed;
#endif

private:
  //theory support

  //if value is zero, it means the sort wasn't introduced yet
  unsigned _array1Sort;
  unsigned _array2Sort;

private:
  //formula building

  /**
   * Possible symbols in the beginning of a lisp list representing formula
   */
  enum FormulaSymbol
  {
    FS_LESS,
    FS_LESS_EQ,
    FS_EQ,
    FS_GREATER,
    FS_GREATER_EQ,
    FS_AND,
    FS_DISTINCT,
    FS_EXISTS,
    FS_FLET,
    FS_FORALL,
    FS_IF_THEN_ELSE,
    FS_IFF,
    FS_IMPLIES,
    FS_LET,
    FS_NOT,
    FS_OR,
    FS_XOR,

    FS_USER_PRED_SYMBOL
  };
  static const char * s_formulaSymbolNameStrings[];

  enum TermSymbol
  {
    TS_MULTIPLY,
    TS_PLUS,
    TS_MINUS,
    TS_DIVIDE,
    TS_ITE,
    TS_SELECT,
    TS_STORE,
    TS_UMINUS,
      
    TS_USER_FUNCTION
  };
  static const char * s_termSymbolNameStrings[];

  DHMap<LExpr*,Formula*> _forms;
  DHMap<LExpr*,TermList> _terms;

  //lets are set when we their scope appears on a to-do stack and unset
  //when we remove them from there
  DHMap<vstring,Formula*> _formVars;
  DHMap<vstring,TermList> _termVars;

  /** Next quantified variable index to be used */
  unsigned _nextQuantVar;

  /**
   * _varSorts[i] contains sort of variable Xi.
   */
  Stack<unsigned> _varSorts;

  /**
   * The second element in the pair is a bool determining whether the
   * lisp expression denotes a formula (true) or a term (false).
   */
  typedef pair<LExpr*,bool> ToDoEntry;
  /**
   * Stack with lisp expressions that need have their corresponding
   * terms and formulas built.
   */
  Stack<ToDoEntry> _todo;

  /**
   * True if we are entering a new list expression on the to-do stack.
   * False if we have returned to the expression after evaluating its children.
   */
  bool _entering;
  ToDoEntry _current;

  bool tryGetArgumentTerm(LExpr* parent, LExpr* argument, TermList& res);
  bool tryGetArgumentFormula(LExpr* parent, LExpr* argument, Formula*& res);

  void requestSubexpressionProcessing(LExpr* subExpr, bool formula);

  static FormulaSymbol getFormulaSymbol(vstring str);
  static TermSymbol getTermSymbol(vstring str, unsigned arity);
  static Interpretation getFormulaSymbolInterpretation(FormulaSymbol ts, unsigned firstArgSort);
  static Interpretation getTermSymbolInterpretation(TermSymbol ts, unsigned firstArgSort);
  static unsigned getMandatoryConnectiveArgCnt(FormulaSymbol fsym);
//  unsigned getPredSymbolArity(FormulaSymbol fsym, vstring str);

  unsigned getSort(TermList t);
  void ensureArgumentSorts(bool pred, unsigned symNum, TermList* args);

  bool readTermArgs(LExpr* parent, LispListReader& rdr, TermStack& args);


  TermList readTermFromAtom(vstring str);
  bool tryReadTermIte(LExpr* e, TermList& res);
  unsigned getTermSelectOrStoreFn(LExpr* e, TermSymbol tsym, const TermStack& args);
  bool tryReadTerm(LExpr* e, TermList& res);

  Formula* readFormulaFromAtom(vstring str);
  bool tryReadNonPropAtom(FormulaSymbol fsym, LExpr* e, Literal*& res);
  bool tryReadConnective(FormulaSymbol fsym, LExpr* e, Formula*& res);
  bool tryReadQuantifier(bool univ, LExpr* e, Formula*& res);
  bool tryReadDistinct(LExpr* e, Formula*& res);
  bool tryReadFlet(LExpr* e, Formula*& res);
  bool tryReadLet(LExpr* e, Formula*& res);
  bool tryReadFormula(LExpr* e, Formula*& res);
  Formula* readFormula(LExpr* e);
  void buildFormula();

  Formula* nameFormula(Formula* f, vstring fletVarName);

};

}

#endif // __SMTLIB__

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
 * @file Parse/TPTP.hpp
 * Defines class TPTP for parsing TPTP files
 *
 * @since 08/04/2011 Manchester
 */

#ifndef __Parser_TPTP__
#define __Parser_TPTP__

#include <filesystem>
#include <iostream>
#include <unordered_set>

#include "Forwards.hpp"
#include "Lib/Array.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Exception.hpp"
#include "Lib/IntNameTable.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"

//#define DEBUG_SHOW_STATE

namespace Kernel {
  class Clause;
};

namespace Parse {
  using namespace Kernel;

/**
 * Implements a TPTP parser
 * @since 08/04/2011 Manchester
 */
class TPTP
{
public:
  /** Token types */
  enum Tag {
    /** end of file */
    T_EOF,
    /** name, identifier beginning with a lower-case letter */
    T_NAME,
    /** variable name, identifier beginning with an upper-case letter */
    T_VAR,
    /** '(' */
    T_LPAR,
    /** ')' */
    T_RPAR,
    /** '[' */
    T_LBRA,
    /** ']' */
    T_RBRA,
    /** ',' */
    T_COMMA,
    /** ':' */
    T_COLON,
    /** '~' */
    T_NOT,
    /** '&' */
    T_AND,
    /** '=' */
    T_EQUAL,
    /** string */
    T_STRING,
    /** inequality */
    T_NEQ,
    /** universal quantifier */
    T_FORALL,
    /** existential quantifier */
    T_EXISTS,
    /** type universal quantifier */
    T_PI,
    /** type existential quantifier */
    T_SIGMA,
    /** implication */
    T_IMPLY,
    /** exclusive or */
    T_XOR,
    /** equivalence */
    T_IFF,
    /** reverse implication */
    T_REVERSE_IMP,
    /** dot */
    T_DOT,
    /** real number */
    T_REAL,
    /** rational number */
    T_RAT,
    /** integer */
    T_INT,
    /** connective or */
    T_OR,
    /** := */
    T_ASS,
    /** lambda operator */
    T_LAMBDA,
    /** (higher-order) application */
    T_APP,
    /** star (product type) */
    T_STAR,
    /** union type? */
    T_UNION,
    /** arrow type */
    T_ARROW,
    /** Subtype */
    T_SUBTYPE,
    /** Geoff's invention, one connective for the price of two */
    T_NOT_OR,
    /** Geoff's invention, one connective for the price of two */
    T_NOT_AND,
    /** sequent */
    T_SEQUENT,
    /** !> */
    T_TYPE_QUANT,
    /** ?* */
    T_THF_QUANT_SOME,
    /** @+  choice operator */
    T_CHOICE,
    /** @- definite description */
    T_DEF_DESC,
    /** @@+  choice operator */
    T_POLY_CHOICE,
    /** @@- definite description */
    T_POLY_DEF_DESC,
    /** $true */
    T_TRUE,
    /** $false */
    T_FALSE,
    /** $tType */
    T_TTYPE,
    /** $o */
    T_BOOL_TYPE,
    /** $i */
    T_DEFAULT_TYPE,
    /** $int */
    T_INTEGER_TYPE,
    /** $rat */
    T_RATIONAL_TYPE,
    /** $real */
    T_REAL_TYPE,
    /** $tuple type */
    T_TUPLE,
    /** theory functions */
    T_THEORY_FUNCTION,
    /** theory sorts */
    T_THEORY_SORT,
    /** $fot, probably useless */
    T_FOT,
    /** $fof, probably useless */
    T_FOF,
    /** $tff, probably useless */
    T_TFF,
    /** $thf, probably useless */
    T_THF,
    /** anything that begins with $$ */
    T_DOLLARS,
    /** $ite: FOOL level-polymorphic if-then-else */
    T_ITE,
    /** $let: FOOL level-polymorphic let-in */
    T_LET
  };

  /** parser state, numbers are just temporarily for debugging */
  enum State {
    /** list of units */
    UNIT_LIST,
    /** cnf() declaration */
    CNF,
    /** fof() declaration */
    FOF,
    /** vampire() declaration */
    VAMPIRE,
    /** read formula */
    FORMULA,
    /** process end of fof() declaration */
    END_FOF,
    /** read a simple formula */
    SIMPLE_FORMULA,
    /** build formula from a connective and one or more formulas */
    END_FORMULA,
    /** read a formula that whould be put inside a term */
    FORMULA_INSIDE_TERM,
    /** */
    TERM_INFIX,
    /** wrap built formula inside a term */
    END_FORMULA_INSIDE_TERM,
    /** make built boolean term a formula */
    END_TERM_AS_FORMULA,
    /** read a variable list (for a quantifier) */
    VAR_LIST,
    /** read a function application */
    FUN_APP,
    /** process application of = or != to an atom */
    FORMULA_INFIX,
    /** read arguments */
    ARGS,
    /** read term */
    TERM,
    /** read arguments after a term */
    END_TERM,
    /** read a single token and do nothing */
    TAG,
    /** include directive */
    INCLUDE,
    /** after the equality */
    END_EQ,
    /** Read a HOL formula */
    HOL_FORMULA,
    /** build a HOL formula from a connective and one or more formulas */
    END_HOL_FORMULA,
    /** Read a higher-order constant or variable */
    HOL_TERM,
    /** create an application term after reading an app */
    END_APP,
    /** tff declaration */
    TFF,
    /** THF declaration */
    THF,
    /** read type declaration */
    TYPE,
    /** after a top-level type declaration */
    END_TFF,
    /** after a type declaration */
    END_TYPE,
    /** simple type */
    SIMPLE_TYPE,
    /** unbinding previously quantified variables */
    UNBIND_VARIABLES,
    /** end of an if-then-else expression */
    END_ITE,
    /** read tuple */
    END_TUPLE,
    /** check the end of arguments */
    END_ARGS,
    /** middle of equality */
    MID_EQ,
    /** end of $let expression */
    END_LET,
    /** a type signature in a let expression */
    LET_TYPE,
    /** end of let type signature */
    END_LET_TYPES,
    /** start of a binding inside $let */
    DEFINITION,
    MID_DEFINITION,
    /** end of a definition inside $let */
    END_DEFINITION,
    /** start of a definition of a function or predicate symbol */
    SYMBOL_DEFINITION,
    /** start of tuple definition inside $let */
    TUPLE_DEFINITION,
    /** end of a theory function */
    END_THEORY_FUNCTION
  };

  enum LastPushed {
    /**last item pushed was a formula */
    FORM,
    /**last item pushed was a term */
    TM,
  };

  static const int HOL_CONSTANTS_LOWER_BOUND;
  /** operator lambda */
  static const int LAMBDA;
  /** application of any number of terms */
  static const int APP;
  /** Pi function for universal quantification */
  static const int PI;
  /** Sigma function for existential quantification */
  static const int SIGMA;

  /** token */
  struct Token {
    /** token type */
    Tag tag;
    /** content */
    std::string content;
    std::string toString() const;
  };

  /**
   * Implements lexer and parser exceptions.
   */
  class ParseErrorException
    : public ParsingRelatedException
  {
  public:
    ParseErrorException(std::string message, std::filesystem::path path, unsigned ln)
      : _message(message), _path(path), _ln(ln) {}
    ParseErrorException(std::string message, Token& tok, std::filesystem::path path, unsigned ln)
      : ParseErrorException(message + " (text: " + tok.toString() + ')', path, ln) {}
    void cry(std::ostream&) const;
    ~ParseErrorException() {}
  protected:
    std::string _message;
    std::filesystem::path _path;
    unsigned _ln = 0;
  }; // TPTP::ParseErrorException

#define PARSE_ERROR_TOK(msg,tok) \
  throw ParseErrorException(msg,tok,currentFile.path,currentFile.lineNumber)
#define PARSE_ERROR(msg) \
  throw ParseErrorException(msg,currentFile.path,currentFile.lineNumber)

  /**
   * @brief Construct a new TPTP parser.
   *
   * @param in is the stream with the raw input to read
   * @param unitBuffer is FIFO of units to which newly parsed Clauses/Formulas
   *   will be added (via pushBack);
   *
   *  if left unspeficied, and empty fifo is created and used instead.
   *  (use this default behaviour if you do not want to collect formulas
   *   from multiple parser calls)
   */
  TPTP(std::istream &in, UnitList::FIFO unitBuffer = UnitList::FIFO());
  ~TPTP();
  void parse();
  static UnitList* parse(std::istream& str);
  static Clause* parseClauseFromString(const std::string& str);
  /** Return the list of parsed units */
  UnitList* units() const { return _units.list(); }
  /** Return the current unitBuffer (on top of units() you also get a pointer to the last added unit in constant time). */
  UnitList::FIFO unitBuffer() const { return _units; }
  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem" or "Unsatisfiable"
   * based on this value.
   */
  bool containsConjecture() const { return _containsConjecture; }
  static bool findAxiomName(const Unit* unit, std::string& result);
  //this function is used also by the API
  static void assignAxiomName(const Unit* unit, std::string& name);
  unsigned lineNumber(){ return currentFile.lineNumber; }
  std::string currentPath(){ return currentFile.path; }

  static Map<int,std::string>* findQuestionVars(unsigned questionNumber) {
    auto res = _questionVariableNames.findPtr(questionNumber);
    return res ? *res : nullptr;
  }
  static bool seenQuestions() {
    return !_questionVariableNames.isEmpty();
  }
private:
  void parseImpl(State initialState = State::UNIT_LIST);
  /** Return the input string of characters */
  const char* input() { return _chars.content(); }

  enum TypeTag {
    TT_ATOMIC,
    TT_PRODUCT,
    TT_ARROW,
    TT_QUANTIFIED
  };

  /**
   * Class of types. Should be removed when the Vampire type system is
   * improved.
   * @since 14/07/2011 Manchester
   */
  class Type {
  public:
    explicit Type(TypeTag tag) : _tag(tag) {}
    /** return the kind of this sort */
    TypeTag tag() const {return _tag;}
  protected:
    /** kind of this type */
    TypeTag _tag;
  };

  /** An atomic type is simply a sort */
  class AtomicType
    : public Type
  {
  public:
    explicit AtomicType(TermList sort)
      : Type(TT_ATOMIC), _sort(sort)
    {}
    /** return the sort number */
    TermList sort() const {return _sort;}
  private:
    /** the sort identified by its number in the signature */
    TermList _sort;
  }; // AtomicType

  /** Arrow type */
  class ArrowType
    : public Type
  {
  public:
    ArrowType(Type* lhs,Type* rhs)
      : Type(TT_ARROW), _lhs(lhs), _rhs(rhs)
    {}
    /** the argument type */
    Type* argumentType() const {return _lhs;}
    /** the return type */
    Type* returnType() const {return _rhs;}
  private:
    /** the argument type */
    Type* _lhs;
    /** the return type */
    Type* _rhs;
  }; // ArrowType

  /** Product type. It now only uses a product of two types, which might be
   * wrong for higher-order logic, yet appropriate for parsing first-order
   * types.
   */
  class ProductType
    : public Type
  {
  public:
    ProductType(Type* lhs,Type* rhs)
      : Type(TT_PRODUCT), _lhs(lhs), _rhs(rhs)
    {}
    /** the left hand side type */
    Type* lhs() const {return _lhs;}
    /** the right hand side type */
    Type* rhs() const {return _rhs;}
  private:
    /** the argument type */
    Type* _lhs;
    /** the return type */
    Type* _rhs;
  }; // ProductType

  /**
   */
  class QuantifiedType
    : public Type
  {
  public:
    QuantifiedType(Type* t, VList* vars)
      : Type(TT_QUANTIFIED), _type(t), _vars(vars)
    {}
    /** the bound type variables */
    VList* vars() const {return _vars;}
    /** the right hand side type */
    Type* qtype() const {return _type;}
  private:
    /** the quantified type */
    Type* _type;
    /** bound type variables */
     VList* _vars;
  }; // ProductType

  enum TheorySort {
    /** $array theoy */
    TS_ARRAY,
  };
  static bool findTheorySort(const std::string name, TheorySort &ts) {
    static const std::string theorySortNames[] = {
      "$array"
    };
    static const unsigned theorySorts = sizeof(theorySortNames)/sizeof(std::string);
    for (unsigned sort = 0; sort < theorySorts; sort++) {
      if (theorySortNames[sort] == name) {
        ts = static_cast<TheorySort>(sort);
        return true;
      }
    }
    return false;
  }
  static bool isTheorySort(const std::string name) {
    static TheorySort dummy;
    return findTheorySort(name, dummy);
  }
  static TheorySort getTheorySort(const Token tok) {
    ASS_REP(tok.tag == T_THEORY_SORT, tok.content);
    TheorySort ts;
    if (!findTheorySort(tok.content, ts)) {
      ASSERTION_VIOLATION_REP(tok.content);
    }
    return ts;
  }

  enum TheoryFunction {
    /** $array theory */
    TF_SELECT, TF_STORE
  };
  static bool findTheoryFunction(const std::string name, TheoryFunction &tf) {
    static const std::string theoryFunctionNames[] = {
      "$select", "$store"
    };
    static const unsigned theoryFunctions = sizeof(theoryFunctionNames)/sizeof(std::string);
    for (unsigned fun = 0; fun < theoryFunctions; fun++) {
      if (theoryFunctionNames[fun] == name) {
        tf = static_cast<TheoryFunction>(fun);
        return true;
      }
    }
    return false;
  }
  static bool isTheoryFunction(const std::string name) {
    static TheoryFunction dummy;
    return findTheoryFunction(name, dummy);
  }
  static TheoryFunction getTheoryFunction(const Token tok) {
    ASS_REP(tok.tag == T_THEORY_FUNCTION, tok.content);
    TheoryFunction tf;
    if (!findTheoryFunction(tok.content, tf)) {
      ASSERTION_VIOLATION_REP(tok.content);
    }
    return tf;
  }

  TermList* nLastTermLists(unsigned n)
  { return n == 0 ? nullptr : &_termLists[_termLists.size() - n]; }

  /** true if the input contains a conjecture */
  bool _containsConjecture;

  // all the state associated with parsing a single file
  struct FileState {
    // the input stream: raw pointer because UIHelper might own it
    // TODO fix ownership of streams
    std::istream *in = nullptr;
    // include() can optionally give a formula_selection list of names to import: the rest should be ignored
    std::unordered_set<std::string> allowedNames;

    // name of the file for error reporting
    std::filesystem::path path;
    // current line number for parse errors
    unsigned lineNumber;
  } currentFile;
  // stack of states to restore after finishing an include() directive
  std::vector<FileState> restoreFiles;

  /** input characters */
  Array<char> _chars;
  /** the position beyond the last read characters */
  int _cend;
  /** tokens currently at work */
  Array<Token> _tokens;
  /** the position beyond the last processed token */
  int _tend;
  /** The list of units read (with additions directed to the end) */
  UnitList::FIFO _units;
  /** stack of unprocessed states */
  Stack<State> _states;
  /** input type of the last read unit */ // it must be int since -1 can be used as a value
  UnitInputType _lastInputType;
  /** true if the last read unit is a question */
  bool _isQuestion;
  /** */
  bool _isThf;
  /** */
  bool _containsPolymorphism;
  /** various strings saved during parsing */
  Stack<std::string> _strings;
  /** various connectives saved during parsing */ // they must be int, since non-existing value -1 can be used
  Stack<int> _connectives;
  /** various boolean values saved during parsing */
  Stack<bool> _bools;
  /** various integer values saved during parsing */
  Stack<int> _ints;
  /** variable lists for building formulas */
  Stack<VList*> _varLists;
  /** sort lists for building formulas */
  Stack<SList*> _sortLists;
  /** variable lists for binding variables */
  Stack<VList*> _bindLists;
  /** various tokens to consume */
  Stack<Tag> _tags;
  /** various formulas */
  Stack<Formula*> _formulas;
  /** various literals */
  Stack<Literal*> _literals;
  /** term lists */
  Stack<TermList> _termLists;
  /** name table for variable names */
  IntNameTable _vars;
  /** When parsing a question, make note of the inverse mapping to _vars, i.e. from the ints back to the vstrings, for better user reporting */
  Map<int,std::string> _curQuestionVarNames;
  /** parsed types */
  Stack<Type*> _types;
  /** various type tags saved during parsing */
  Stack<TypeTag> _typeTags;
  /**  */
  Stack<TheoryFunction> _theoryFunctions;
  /** bindings of variables to sorts */
  Map<unsigned,SList*> _variableSorts;
  /** current color, if the input contains colors */
  Color _currentColor;
  /** a robsubstitution object to be used temporarily that is kept around to safe memory allocation time  */
  RobSubstitution _substScratchpad;

  /** a function name and arity */
  typedef std::pair<std::string, unsigned> LetSymbolName;

  /** a symbol number with a predicate/function flag */
  typedef std::pair<unsigned, bool> LetSymbolReference;
  #define SYMBOL(ref) (ref.first)
  #define IS_PREDICATE(ref) (ref.second)

  /** a definition of a function symbol, defined in $let */
  typedef std::pair<LetSymbolName, LetSymbolReference> LetSymbol;

  /** a scope of function definitions */
  typedef Stack<LetSymbol> LetSymbols;

  /** a stack of scopes */
  Stack<LetSymbols> _letSymbols;
  Stack<LetSymbols> _letTypedSymbols;

  /** Record wheter a formula or term has been pushed more recently */
  LastPushed _lastPushed;

  /** finds if the symbol has been defined in an enclosing $let */
  bool findLetSymbol(LetSymbolName symbolName, LetSymbolReference& symbolReference);
  bool findLetSymbol(LetSymbolName symbolName, LetSymbols scope, LetSymbolReference& symbolReference);

  typedef Stack<LetSymbolReference> LetDefinitions;
  Stack<LetDefinitions> _letDefinitions;

  /** model definition formula */
  bool _modelDefinition;

  // A hack to hard-code the precedence of = and != higher than connectives
  // This is needed for implementation of FOOL
  unsigned _insideEqualityArgument;

  /**
   * Get the next characters at the position pos.
   */
  inline char getChar(int pos)
  {
    while (_cend <= pos) {
      int c = currentFile.in->get();
      //      if (c == -1) { std::cout << "<EOF>"; } else {std::cout << char(c);}
      _chars[_cend++] = c == -1 ? 0 : c;
    }
    return _chars[pos];
  } // getChar

  /**
   * Shift characters in the buffer by n positions left.
   */
  inline void shiftChars(int n)
  {
    ASS(n > 0);
    ASS(n <= _cend);

    for (int i = 0;i < _cend-n;i++) {
      _chars[i] = _chars[n+i];
    }
    _cend -= n;
  } // shiftChars

  /**
   * Reset the character buffer.
   * @since 10/04/2011 Manchester
   */
  inline void resetChars()
  {
    _cend = 0;
  } // resetChars

  /**
   * Get the token at the position pos.
   */
  inline Token& getTok(int pos)
  {
    while (_tend <= pos) {
      Token& tok = _tokens[_tend++];
      readToken(tok);
    }
    return _tokens[pos];
  } // getTok

  /**
   * Shift tokens in the buffer by n positions left.
   */
  inline void shiftToks(int n)
  {
    ASS(n > 0);
    ASS(n <= _tend);

    for (int i = 0;i < _tend-n;i++) {
      _tokens[i] = _tokens[n+i];
    }
    _tend -= n;
  } // shiftToks

  /**
   * Reset the character buffer.
   * @since 10/04/2011 Manchester
   */
  inline void resetToks()
  {
    _tend = 0;
  } // resetToks

  // lexer functions
  bool readToken(Token& t);
  void skipWhiteSpacesAndComments();
  void readName(Token&);
  void readReserved(Token&);
  void readString(Token&);
  void readAtom(Token&);
  Tag readNumber(Token&);
  int decimal(int pos);
  int positiveDecimal(int pos);
  static std::string toString(Tag);

  // parser functions
  static Formula* makeJunction(Connective c,Formula* lhs,Formula* rhs);
  void unitList();
  void fof(bool fo);
  void tff();
  void vampire();
  void consumeToken(Tag);
  std::string name();
  void formula();
  void funApp();
  void simpleFormula();
  void simpleType();
  void args();
  void varList();
  void symbolDefinition();
  void tupleDefinition();
  void term();
  void termInfix();
  void endTerm();
  void endArgs();
  Literal* createEquality(bool polarity,TermList& lhs,TermList& rhs);
  Formula* createPredicateApplication(std::string name,unsigned arity);
  TermList createFunctionApplication(std::string name,unsigned arity);
  TermList createTypeConApplication(std::string name,unsigned arity);
  void endEquality();
  void midEquality();
  void formulaInfix();
  void endFormula();
  void formulaInsideTerm();
  void endFormulaInsideTerm();
  void endTermAsFormula();
  void endType();
  void tag();
  void endFof();
  void endTff();
  std::filesystem::path resolveInclude(const std::filesystem::path included);
  void include();
  void type();
  void endIte();
  void letType();
  void endLetTypes();
  void definition();
  void midDefinition();
  void endDefinition();
  void endLet();
  void endTheoryFunction();
  void endTuple();
  void addTagState(Tag);
  TermList readSort();
  unsigned getConstructorArity();

  //Higher-order parsing
  //these functions were all written in early 2017 (start of PhD) and are consequently
  //pretty nasty and don't follow the philosophy of the parser. However, they should
  //not impact standard parsing functions in any way.
  void endApp();
  void holFormula();
  void endHolFormula();
  void holTerm();
  void foldl(TermStack*);
  TermList readArrowSort();
  void readTypeArgs(unsigned arity);
  //End of higher-order specific functions

  void bindVariable(unsigned var,TermList sort);
  void unbindVariables();
  void skipToRPAR();
  void skipToRBRA();
  unsigned addFunction(std::string name,int arity,bool& added,TermList& someArgument);
  int addPredicate(std::string name,int arity,bool& added,TermList& someArgument);
  unsigned addOverloadedFunction(std::string name,int arity,int symbolArity,bool& added,TermList& arg,
				 Theory::Interpretation integer,Theory::Interpretation rational,
				 Theory::Interpretation real);
  unsigned addOverloadedPredicate(std::string name,int arity,int symbolArity,bool& added,TermList& arg,
				  Theory::Interpretation integer,Theory::Interpretation rational,
				  Theory::Interpretation real);
  TermList sortOf(TermList term);
  static bool higherPrecedence(int c1,int c2);
  std::string convert(Tag t);

  bool findInterpretedPredicate(std::string name, unsigned arity);

  OperatorType* constructOperatorType(Type* t, VList* vars = 0);

public:

  /**
   * Add a numeral constant by reading it from the std::string name.
   */
  template<class Numeral>
  static unsigned addNumeralConstant(const std::string& name)
  {
    if (auto n = Numeral::parse(name)) {
      return env.signature->addNumeralConstant(*n);
    } else {
      throw UserErrorException("not a valid ", Numeral::getSort(), " literal: ", name);
    }
  } 


  static unsigned addUninterpretedConstant(const std::string& name, bool& added);

  // also here, simply made public static to share the code with another use site
  static Unit* processClaimFormula(Unit* unit, Formula* f, const std::string& nm);

  /**
   * Used to store the contents of the 'source' of an input formula
   * This is based on the 'file' and 'inference' record description in
   * http://pages.cs.miami.edu/~tptp/TPTP/QuickGuide/Derivations.html
   */
  struct SourceRecord{
    virtual bool isFile() = 0;
  };
  struct FileSourceRecord : SourceRecord {
    const std::string fileName;
    const std::string nameInFile;
    bool isFile(){ return true; }
    FileSourceRecord(std::string fN, std::string nF) : fileName(fN), nameInFile(nF) {}
  };
  struct InferenceSourceRecord : SourceRecord{
    const std::string name;
    Stack<std::string> premises;
    bool isFile(){ return false; }
    InferenceSourceRecord(std::string n) : name(n) {}
  };

  void setUnitSourceMap(DHMap<Unit*,SourceRecord*>* m){
    _unitSources = m;
  }
  SourceRecord* getSource();

  void setFilterReserved(){ _filterReserved=true; }

private:
  DHMap<Unit*,SourceRecord*>* _unitSources;

  /** This field stores names of input units if the
   * output_axiom_names option is enabled */
  static DHMap<unsigned, std::string> _axiomNames;

  /**
   * During question parsing, we store the mapping from int variables
   * back to their original (v)string names, for nicer user reporting.
   *
   * This map stores, for each question (by unit number)
   * a map of such parsed variable name bingings.
   *
   * (Can there be more than one question? Yes, e.g., in the interactive mode.)
   */
  static DHMap<unsigned, Map<int,std::string>*> _questionVariableNames;

  /** Stores the type arities of function symbols */
  DHMap<std::string, unsigned> _typeArities;
  DHMap<std::string, unsigned> _typeConstructorArities;

  bool _filterReserved;
  bool _seenConjecture;


#if VDEBUG
  void printStates(std::string extra);
  void printInts(std::string extra);
  const char* toString(State s);
#endif
#ifdef DEBUG_SHOW_STATE
  void printStacks();
#endif
}; // class TPTP

}

#endif


/**
 * @file Parse/TPTP.hpp
 * Defines class TPTP for parsing TPTP files
 *
 * @since 08/04/2011 Manchester
 */

#ifndef __Parser_TPTP__
#define __Parser_TPTP__

#include <iostream>

#include "Lib/Array.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Exception.hpp"
#include "Lib/IntNameTable.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

namespace Kernel {
  class Clause;
};

namespace Parse {

class TPTP;

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
    T_THF_QUANT_ALL,
    /** ?* */
    T_THF_QUANT_SOME,
    /** some THF quantifier */
    T_APP_PLUS,
    /** some THF quantifier */
    T_APP_MINUS,
    /** $true */
    T_TRUE,
    /** $false */
    T_FALSE,
    /** tType */
    T_TTYPE,
  };

  /** parser state, numbers are just temporarily for debugging */
  enum State {
    /** list of units */
    UNIT_LIST = 1,
    /** cnf() declaration */
    CNF = 2,
    /** fof() declaration */
    FOF = 3,
    /** vampire() declaration */
    VAMPIRE = 4,
    /** read formula */
    FORMULA = 5,
    /** process end of fof() declaration */
    END_FOF = 6,
    /** read a simple formula */
    SIMPLE_FORMULA = 7,
    /** build formula from a connective and one or more formulas */
    END_FORMULA = 8,
    /** read a variable list (for a quantifier) */
    VAR_LIST = 9,
    /** read an atom */
    ATOM = 10,
    /** process mid-atom: either end of atom or = or != */
    MID_ATOM = 11,
    /** read arguments */
    ARGS = 12,
    /** read term */
    TERM = 13,
    /** read arguments after a term */
    END_TERM = 14,
    /** read a single token and do nothing */
    TAG = 15,
    /** include directive */
    INCLUDE = 16,
    /** after the equality */
    END_EQ = 17,
    /** tff declaration */
    TFF = 18,
    /** read type declaration */
    TYPE = 19,
    /** after a type declaration */
    END_TFF = 20,
  };

  /** token */
  struct Token {
    /** token type */
    Tag tag;
    /** position of the beginning of this token */
    int start;
    /** content */
    string content;
    string toString() const;
  };

  /**
   * Implements lexer and parser exceptions.
   */
  class Exception 
    : public ::Exception
  {
  public:
    Exception(string message,Token& tok);
    Exception(string message,int position);
    void cry(ostream&);
    ~Exception() {}
  protected:
    string _message;
  }; // TPTP::Exception
  friend class Exception;

  TPTP(istream& in);
  ~TPTP();
  void parse();
  /** Return the input string of characters */
  const char* input() { return _chars.content(); }

private:
  /** depth of include directives */
  int _includeDepth;
  /** true if the input contains a conjecture */
  bool _containsConjecture;
  /** Allowed names of formulas.
   * If non-null, ignore formulas not included in _allowedNames.
   * This is to support the feature formula_selection of the include
   * directive of the TPTP format.
 */
  Set<string>* _allowedNames;
  /** stacks of allowed names when include is used */
  Stack<Set<string>*> _allowedNamesStack;
  /** set of files whose inclusion should be ignored */
  Set<string> _forbiddenIncludes;
  /** the input stream */
  istream* _in;
  /** in the case include() is used, previous streams will be saved here */
  Stack<istream*> _inputs;
  /** input characters */
  Array<char> _chars;
  /** position in the input stream of the 0th characater in _chars[] */
  int _gpos;
  /** the position beyond the last read characters */
  int _cend;
  /** tokens currently at work */
  Array<Token> _tokens;
  /** the position beyond the last processed token */
  int _tend;
  /** The stack of units read */
  Stack<Unit*> _units;
  /** stack of unprocessed states */
  Stack<State> _states;
  /** input type of the last read unit */
  Unit::InputType _lastInputType;
  /** various strings saved during parsing */
  Stack<string> _strings;
  /** various connectives saved during parsing */
  Stack<Connective> _connectives;
  /** various boolean values saved during parsing */
  Stack<bool> _bools;
  /** various integer values saved during parsing */
  Stack<int> _ints;
  /** various variable lists */
  Stack<Formula::VarList*> _varLists;
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

  // various next character and next token reading commands

  /**
   * Get the next characters at the position pos.
   */
  inline char getChar(int pos)
  {
    CALL("TPTP::getChar");

    while (_cend <= pos) {
      int c = _in->get();
      if (c == -1) { cout << "<EOF>"; } else {cout << char(c);}
      _chars[_cend++] = c == -1 ? 0 : c;
    }
    return _chars[pos];
  } // getChar

  /**
   * Shift characters in the buffer by n positions left.
   */
  inline void shiftChars(int n)
  {
    CALL("TPTP::shiftChars");
    ASS(n > 0);
    ASS(n <= _cend);

    for (int i = 0;i < _cend-n;i++) {
      _chars[i] = _chars[n+i];
    }
    _cend -= n;
    _gpos += n;
  } // shiftChars

  /**
   * Reset the character buffer.
   * @since 10/04/2011 Manchester
   */
  inline void resetChars()
  {
    _gpos += _cend;
    _cend = 0;
  } // resetChars

  /**
   * Get the token at the position pos.
   */
  inline Token& getTok(int pos)
  {
    CALL("TPTP::getTok");

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
    CALL("TPTP::shiftToks");

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
  static string toString(Tag);

  // parser functions
  static Formula* makeJunction(Connective c,Formula* lhs,Formula* rhs);
  void unitList();
  void fof(bool fo);
  void tff();
  void consumeToken(Tag);
  string name();
  void formula();
  void atom();
  void simpleFormula();
  void args();
  void varList();
  void term();
  void endTerm();
  void buildTerm();
  void makeTerm(TermList& ts,Token& tok);
  void midAtom();
  void endEquality();
  void endFormula();
  void endSimpleFormula();
  void tag();
  void endFof();
  void include();
  void type();

  static bool higherPrecedence(Connective c1,Connective c2);

#if VDEBUG
  void printStates(string extra);
  void printInts(string extra);
  const char* toString(State s);
#endif
}; // class TPTP

}

#endif


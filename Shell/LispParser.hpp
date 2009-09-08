/**
 * @file LispParser.hpp
 * Defines class LispParser for parsing Lisp files.
 *
 * @since 26/08/2009 Redmond
 */

#ifndef __LispParser__
#define __LispParser__

#include <string>
#include "../Forwards.hpp"
#include "../Lib/Exception.hpp"
#include "../Lib/List.hpp"

#include "Parser.hpp"

namespace Shell {

using namespace std;

class LispLexer;

/**
 * Class LispParser, implements a Lisp Parser.
 * @since 26/08/2009 Redmond
 */
class LispParser
  : public Parser
{
public:
  /** Tags of Lisp expressions */
  enum Tag {
    /** atom */
    ATOM = 0,
    /** list */
    LIST = 1
  };

  /** expressions */
  struct Expression {
    /** type of the expression */
    Tag tag;
    /** the value (for atoms and numbers) */
    string str;
    /** list of expressions */
    List<Expression*>* list;
    /** build a list expressions with the list initially empty */
    explicit Expression(Tag t)
      : tag(t),
	str("?"),
	list(0)
    {}
    /** build a string-values expression */
    Expression(Tag t,string s)
      : tag(t),
	str(s),
	list(0)
    {}
    string toString() const;
  };

  typedef Lib::List<Expression*> List;

  explicit LispParser(LispLexer& lexer);
  Expression* parse();
  void parse(List**);
private:
  /** balance of parenthesis */
  int _balance;
}; // class LispParser

}

#endif


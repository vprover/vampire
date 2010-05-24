/**
 * @file TPTPParser.hpp
 * Defines class TPTPParser for parsing TPTP files.
 *
 * @since 17/07/2004 Helsinki airport
 */

#ifndef __TPTPParser__
#define __TPTPParser__

#include "Forwards.hpp"

#include "Lib/Exception.hpp"
#include "Lib/List.hpp"

#include "Kernel/Unit.hpp"

#include "Parser.hpp"

namespace Shell {

using namespace std;
using namespace Kernel;

class TPTPLexer;

/**
 * Class TPTPParser, implements a TPTP Parser.
 * @since 17/07/2004 Helsinki airport
 */
class TPTPParser
  : public Parser
{
public:
  explicit TPTPParser(TPTPLexer& lexer, int includeDepth=0);
  TPTPParser(TPTPLexer& lexer, List<string>* allowedNames, int includeDepth=0);
  UnitList* units();

private:
  class UnitStack;
  class LiteralStack;
  class TermStack;
  class TermArray;

  void recognizeTopLevelTokens();

  Formula* formula();
  void units(UnitStack&);
  Unit* unit();
  Clause* clause(int inputType);
  Clause* formulaClause(int inputType);
  Formula* xorFormula();
  Formula* iffFormula();
  Formula* impFormula();
  Formula* orFormula();
  Formula* andFormula();
  Formula* simpleFormula();
  List<int>* varList();
  Literal* atom(bool polarity);
  void args(TermStack& ts);
  Term* term(int& varNumber);
  string name();
  Literal* literal();
  Literal* formulaLiteral();
  void literals(LiteralStack&);
  void formulaLiterals(LiteralStack&);
  void include(UnitStack&);
  Term* makeTerm(const string& functor,TermStack& args);
  Literal* makeAtom(const string& functor,TermStack& args,bool polarity);
  static void fillArgs (Term* t,TermStack& ts);
  Clause* createClause(LiteralStack&,int inputType);
  static Formula* makeJunction(int connective,Formula* lhs,Formula* rhs);
  void vampire();

  /** Set to true if the constant true was read during reading the
   * last clause */
  bool _trueRead;
  /** if left_formula or right_formula declarations are used, then the
   *  color defined by the currently active declaration*/
  Color _currentColor;
  /** if include() is used, then the depth of includes, 0 if top-level */
  int _includeDepth;
  /** used for claims */
  Formula* _claim;

  /**
   * Is set true by the constructor, if this instance of the parser
   * should yield only formulas with names from @b _allowedNames
   *
   * This is to support the feature formula_selection of the include
   * directive of the TPTP format.
   */
  bool _namesLimited;
  /**
   * Allowed names of formulas (see @b _namesLimited)
   */
  List<string>* _allowedNames;
}; // class TPTPParser

}

#endif


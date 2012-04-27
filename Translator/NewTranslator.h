/* 
 * File:   newTranslator.h
 * Author: ioan
 *
 */

#ifndef NEWTRANSLATOR_H
#define	NEWTRANSLATOR_H

#include <clang/AST/Stmt.h>
#include <clang/AST/StmtVisitor.h>
#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"
#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Array.hpp"
#include "Lib/Map.hpp"

#include "Forwards.hpp"

#include "CollectionOfObjects.hpp"

namespace Translator
{

using namespace clang;
using namespace std;

using namespace Program;
class Variable;
using namespace Lib;

class newTranslator: public ConstStmtVisitor<newTranslator, void> {
public:
  newTranslator(Stmt* body, ASTContext* ctx);
  ~newTranslator();

  void SetWhileToAnalyze(int n)
  {
    _whileToAnalyze = n;
  }
  void RunRewriting();
  void GetVariableDecl();

  virtual void VisitStmt(const Stmt* stmt);
  virtual void VisitIfStmt(const IfStmt* stmt);
  virtual void VisitWhileStmt(const WhileStmt *stmt);
  virtual void VisitDeclStmt(const DeclStmt *stmt);

  virtual void VisitBinAssign(const BinaryOperator* bop);
  virtual void VisitBinEQ(const BinaryOperator* bop);
  virtual void VisitBinNE(const BinaryOperator* bop);

  virtual void VisitBinAddAssign(const BinaryOperator* bop);
  virtual void VisitBinSubAssign(const BinaryOperator* bop);
  virtual void VisitBinMulAssign(const BinaryOperator* bop);
  virtual void VisitBinDivAssign(const BinaryOperator* bop);
  virtual void VisitBinShlAssign(const BinaryOperator* bop);
  virtual void VisitBinShrAssign(const BinaryOperator* bop);

  virtual void VisitBinAdd(const BinaryOperator* bop);
  virtual void VisitBinSub(const BinaryOperator* bop);
  virtual void VisitBinMul(const BinaryOperator* bop);
  virtual void VisitBinDiv(const BinaryOperator* bop);
  virtual void VisitBinShl(const BinaryOperator* bop);
  virtual void VisitBinShr(const BinaryOperator* bop);

  virtual void VisitBinAnd(const BinaryOperator* bop);
  virtual void VisitBinXor(const BinaryOperator* bop);
  virtual void VisitBinOr(const BinaryOperator* bop);
  virtual void VisitBinLOr(const BinaryOperator* bop);
  virtual void VisitBinLAnd(const BinaryOperator* bop);

  virtual void VisitBinLT(const BinaryOperator* bop);
  virtual void VisitBinGT(const BinaryOperator* bop);
  virtual void VisitBinLE(const BinaryOperator* bop);
  virtual void VisitBinGE(const BinaryOperator* bop);

  // this part takes care of the unary operators +/-/not
  virtual void VisitUnaryMinus(const UnaryOperator *op);
  virtual void VisitUnaryPreInc(const UnaryOperator * uop);
  virtual void VisitUnaryPreDec(const UnaryOperator * uop);
  virtual void VisitUnaryPostInc(const UnaryOperator * uop);
  virtual void VisitUnaryPostDec(const UnaryOperator *uop);
  virtual void VisitUnaryLNot(const UnaryOperator *uop);

  virtual void VisitReturnStmt(const ReturnStmt* stmt);

protected:

  std::string simpleExpression(const clang::Expr* e);
  void treatSingleDeclaration(const Decl* stmt);
  bool isSimpleExpression(const Expr *exp);
  const VarDecl * GetVarDecl(const Expr *exp);
  string getLiteralName(const Expr *exp);
  string getSignedValue(const Expr *exp);

  Program::ConstantFunctionExpression* getConstFunction(std::string op);
  string WriteSimpleAssignment(const ::clang::Expr* lhs, const Expr* rhs,
	  string operation);
  string WriteSimpleStatement(const ::clang::Expr *lhs,
	  const ::clang::Expr *rhs, ::std::string operation);

  void AddValues(int val);
  void AddArrayName(string name);
  void AddVariableName(string name);
  void getVariables(const Stmt *stmt);

  void writeIfStatments(string att);
  void writeWhileStatments();

  void addToMainProgram(string exp);
  int stringToInt(string s);

  //checks the kind of a expression
  bool isVariable(const Expr *exp);
  bool isNumber(const Expr *exp);
  bool isArray(const Expr *exp);

  //this function is called in order to treat expressions of the form
  // var++ or var-- and so on
  void treatSpecialCase(const Expr *lhs, string operation);

  //take care of th case var+= exp
  void treatSpecial(const Expr *lhs, const Expr *rhs, string op);
  std::string treatSimpleBinaryOperation(const clang::Expr* lhs,
	  const clang::Expr*, std::string op);
  string noToString(int n);
  string numeUitat;
  vector<string> _mainProgram;
  vector<string> Body;
  //flag is the indicator if the loop/if construction is in the outermost structure
  //or is in the body of some construction
  bool flag;

private:
  collectionOfObjects* colect;
  int _whileToAnalyze;
  Stmt* decl_body;
  ASTContext* ctx;
};

} /* namespace translator */

#endif	/* NEWTRANSLATOR_H */

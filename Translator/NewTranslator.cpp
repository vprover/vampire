/* 
 * File: newTranslator.cpp
 * Author: Ioan Dragan
 * 
 */

#include "NewTranslator.h"

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

#include <iostream>
#include <sstream>
#include <map>

#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"
#include "Lib/List.hpp"
#include "Lib/Array.hpp"
#include "Lib/Numbering.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Map.hpp"

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/Tracer.hpp"
#include "Debug/Assertion.hpp"

#include "Forwards.hpp"

#include "CollectionOfObjects.hpp"

using namespace Translator;
using namespace llvm;
using namespace std;

newTranslator::newTranslator(::clang::Stmt* body, ::clang::ASTContext* CTX)
  : decl_body(body), ctx(CTX), innerWhile(99)
{
  colect = new collectionOfObjects();
}

void newTranslator::VisitReturnStmt(const clang::ReturnStmt* stmt)
{
  CALL("newTranslator::VisitReturnStmt");
  cout << "Visited the return statement" << endl;
}

/**
 * treatSingleDeclaration: it treats the special case when the variables
 * are initialized in the declaration e.g int a=10;
 */
void newTranslator::treatSingleDeclaration(const Decl* stmt)
{
  CALL("newTranslator::treatSingleDeclaration");
  ::std::string name = "", value = "", expr = "";

  Program::VariableExpression* varE;
  Program::Assignment* ass;
  Program::ConstantIntegerExpression* ct;
  if (stmt->getKind() == Decl::Var) {
    const VarDecl* var_decl = (const VarDecl*) stmt;
    if (var_decl->hasInit()) {
      const Expr* init = var_decl->getInit();
      name = var_decl->getNameAsString();
      // TODO add check
      const IntegerLiteral* int_literal = (const IntegerLiteral*) init;
      APSInt val;
      int_literal->EvaluateAsInt(val, *ctx);
      int int_value;
      int_value = stringToInt(val.toString(10));
      if (colect->findVarExpression(name))
	varE = colect->getVarExpression(name);
      else {
	Program::Variable* var;
	var = new Program::Variable(name, Program::Type::integerType());
	varE = new Program::VariableExpression(var);
	colect->insertVariableExpression(name, varE);
      }

      if (colect->findConstantInteger(int_value))
	ct = colect->getConstantIntegerExpr(int_value);
      else {
	ct = new Program::ConstantIntegerExpression(int_value);
	colect->insertConstantIntegerExpr(int_value, ct);
      }

      expr = name + "_ASS__" + val.toString(10);
      if (!colect->findAssignemt(expr)) {
	ass = new Program::Assignment(varE, ct);
	colect->insertAssignment(expr, ass);
      }

      ASS(ass);
      if (flag)
	colect->insertMainProgramStatement(ass);

    }
    else {
      // TODO HANDLE CORRECLTLY THE CASE OF ARRAY DECLARATION AND VARIABLE DECLARATION
      /*	name = var_decl->getNameAsString();
       var_decl->dump();
       Program::VariableExpression* varE;
       if (colect->findVarExpression(name))
       varE = colect->getVarExpression(name);
       else {
       Program::Variable* var;
       var = new Program::Variable(name, Program::Type::integerType());
       varE = new Program::VariableExpression(var);
       colect->insertVariableExpression(name, varE);
       }*/
    }
  }
  // TODO here one can add treatment for other types of declarations;
}

void newTranslator::VisitDeclStmt(const DeclStmt* stmt)
{
  //stmt->dump();
  CALL("newTranslator::VisitDeclStmt");
  ::std::string name = "", value = "", expr = "";
  const Decl* decl;
  if (stmt->isSingleDecl()) {
    decl = stmt->getSingleDecl();
    treatSingleDeclaration(decl);
  } else {
    for (::clang::DeclGroupRef::const_iterator ci = stmt->decl_begin(); ci
	    != stmt->decl_end(); ci++) {
      decl = (*ci);
      treatSingleDeclaration(decl);
    }
  }
}

void newTranslator::VisitStmt(const Stmt* stmt)
{
  CALL("newTranslator::visitStmt");
  for (::clang::Stmt::const_child_iterator it = stmt->child_begin(); it
	  != stmt->child_end(); ++it) {
    numeUitat = "";

    //case the statement is a while statement
    if (::clang::WhileStmt::classof(*it)) {
      const ::clang::WhileStmt *ws = (const ::clang::WhileStmt *) (*it);
      clang::SourceLocation sl = ws->getWhileLoc();
      //sl.dump(ctx->getSourceManager());
      clang::SourceManager &sm = ctx->getSourceManager();
      clang::FullSourceLoc fsl(sl, sm);

      if(_whileToAnalyze == -1){
      cout << "WHILE LOCATION: " << fsl.getSpellingLineNumber()<<endl;
      }

      if (flag == true) {
	Visit(ws->getCond());
	addToMainProgram("Whl_" + numeUitat);
	numeUitat = "";
	flag = false;
	Visit(ws->getBody());
	flag = true;
	writeWhileStatments();
      } else {
	Visit(ws->getCond());
	string bac = "Whl_" + numeUitat;
	std::vector<std::string> back = Body;
	Body.clear();
	Body.insert(Body.end(), "begin_while");
	Body.insert(Body.end(), numeUitat);
	numeUitat = "";

	flag = false;
	Visit(ws->getBody());
	Body.insert(Body.end(), "end_while");
	writeWhileStatments();
	bac=Body[Body.size()-1];
	Body = back;
	Body.insert(Body.end(), bac);

      }

    } else //case if statement
    if (::clang::IfStmt::classof(*it)) {
      const ::clang::IfStmt *ifStmt = dyn_cast<IfStmt> (*it);
      const ::clang::Stmt *_then, *_else;

      Visit(ifStmt->getCond());

      if (flag == true)
	addToMainProgram("if_" + numeUitat);

      string att = numeUitat;
      Body.insert(Body.end(), att + "begin_if");
      string bac = "if_" + numeUitat;
      numeUitat = "";
      bool oldF = flag;
      flag = false;
      Visit(ifStmt->getCond());

      Body.insert(Body.end(), numeUitat);
      Body.insert(Body.end(), att + "if_then");

      numeUitat = "";
      _then = ifStmt->getThen();
      _else = ifStmt->getElse();
      Visit(_then);
      Body.insert(Body.end(), att + "end_then");

      if (_else != NULL) {
	numeUitat = "";

	Body.insert(Body.end(), att + "if_else");
	Visit(_else);
	Body.insert(Body.end(), att + "end_else");

      }
      Body.insert(Body.end(), att + "end_if");
      flag = oldF;
      writeIfStatments(att);
      if (flag == false)
	Body.insert(Body.end(), bac);
      else
	if (_else!=NULL)
	colect->insertMainProgramStatement(colect->getIfThenElse(bac));
	else colect->insertMainProgramStatement(colect->getIfThen(bac));

    } else {
      //all the other cases (assignments, initialization expressions)
      Visit(*it);
      if (!::clang::DeclStmt::classof(*it) && flag == true
	      && !clang::ReturnStmt::classof(*it)) {
	addToMainProgram(numeUitat);
	if (colect->findAssignemt(numeUitat)) {
	  colect->insertMainProgramStatement(colect->getAssignment(numeUitat));
	}

      }
    }

  }

}

void newTranslator::VisitIfStmt(const IfStmt* stmt)
{
  CALL("newTranslator::VisitIfStmt");
  Visit(stmt->getCond());
  Visit(stmt->getThen());
  Visit(stmt->getElse());

}

void newTranslator::VisitWhileStmt(const ::clang::WhileStmt *stmt)
{
  CALL("newTranslator::VisitWhileStmt");
  Visit(stmt->getCond());
  cout<<numeUitat<<endl;
  stmt->getWhileLoc().dump(ctx->getSourceManager());
  Visit(stmt->getBody());

}

void newTranslator::VisitBinAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinAssign");

  if (isSimpleExpression(bop->getRHS())) {
    WriteSimpleStatement(bop->getLHS(), bop->getRHS(), "Assign");
  } else {
    std::string nn = simpleExpression(bop->getLHS());
    Visit(bop->getRHS());
    std::string name = nn + "_ASS_" + numeUitat;
    Program::VariableExpression* v;
    Program::ArrayApplicationExpression* ae;
    Program::Assignment* ass;
    if (isVariable(bop->getLHS())) {
      v = colect->getVarExpression(nn);
      Program::FunctionApplicationExpression* fc =
	      colect->getFunctionApplicationExpression(numeUitat);
      ass = new Program::Assignment(v, fc);
    } else {
      ae = colect->getArrayApplicationExpression(nn);
      ass = new Program::Assignment(ae,
	      colect->getFunctionApplicationExpression(numeUitat));
    }

    if (!colect->findAssignemt(name))
      colect->insertAssignment(name, ass);
    else {
      name = name+ "_@1";
      colect->insertAssignment(name,ass);
    }
    numeUitat = name;
    if (flag == false)
      Body.insert(Body.end(), numeUitat);

  }

}

void newTranslator::VisitBinEQ(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinEQ");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerEq");

}

//take care of this case: it should be transformed in a case
//the translation works as follows:
//treat the expression as it would be Logical equality,
//and then negate the result

void newTranslator::VisitBinNE(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinNE");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerNEq");
  /*cout << "Operation not supported : BINARY INEQUALITY";
  exit(1);

   treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerEq");

   ::std::string name = "integerNegation_", label;
   label = numeUitat;
   name.append(label);

   Program::FunctionApplicationExpression* ineg = new Program::FunctionApplicationExpression(Program::ConstantFunctionExpression::integerNegation());
   ineg->setArgument(0, colect->getFunctionApplicationExpression(label));

   if(!colect->findFunctionApplication(name))
   colect->insertFunctionApplication(name, ineg);

   if (flag == false)
   Body.insert(Body.end(), name);
   else numeUitat = name;
   */

}

void newTranslator::VisitBinAddAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinAddAssign");
  const ::clang::Expr *lhs, *rhs;
  lhs = (const ::clang::Expr*) bop->getLHS();
  rhs = (const ::clang::Expr*) bop->getRHS();
  treatSpecial(lhs, rhs, "PlusEq");

}

void newTranslator::VisitBinSubAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinSubAssign");
  const ::clang::Expr *lhs, *rhs;
  lhs = (const ::clang::Expr*) bop->getLHS();
  rhs = (const ::clang::Expr*) bop->getRHS();

  treatSpecial(lhs, rhs, "MinusEq");
}

void newTranslator::VisitBinMulAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinMUlAssign");
  const ::clang::Expr *lhs, *rhs;
  lhs = (const ::clang::Expr*) bop->getLHS();
  rhs = (const ::clang::Expr*) bop->getRHS();

  treatSpecial(lhs, rhs, "MultEq");

}

void newTranslator::VisitBinDivAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinDivAssign");
  cout << "Division operation not supported yet!" << endl;
  exit(1);
}

void newTranslator::VisitBinShlAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinShlAssign");
  cout << "Shift operation not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinShrAssign(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinShrAssign");
  cout << "Shift operation not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinAdd(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinAdd");
  ::std::string op = "integerPlus";
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), op);
}

void newTranslator::VisitUnaryLNot(const ::clang::UnaryOperator* uop)
{
  CALL("newTranslator::VisitUnaryLNot");
  treatSimpleBinaryOperation(uop->getSubExpr(), NULL, "booleanNeg");
  /*Visit(uop->getSubExpr());
  ::std::string name = "booleanNegation_" + numeUitat;
  Program::FunctionApplicationExpression* neg =
	  new Program::FunctionApplicationExpression(
		  Program::ConstantFunctionExpression::booleanNeg());
  neg->setArgument(0, colect->getFunctionApplicationExpression(numeUitat));
  if (!colect->findFunctionApplication(name))
    colect->insertFunctionApplication(name, neg);
    Body.insert(Body.end(), name);
    cout<<"THRE "<<name<<endl;
    numeUitat="GOE"+numeUitat;
*/

}

void newTranslator::VisitUnaryMinus(const UnaryOperator* op)
{
  CALL("newTranslator::VisitUnaryMinus");
  ::clang::Expr *exp;

  exp = op->getSubExpr();
  ::std::string name = "integerNegation_", label;
  label = simpleExpression(exp);
  Program::VariableExpression* varExp = colect->getVarExpression(label);
  name.append(label);

  Program::FunctionApplicationExpression* tempFC =
	  new Program::FunctionApplicationExpression(
		  Program::ConstantFunctionExpression::integerNegation());
  tempFC->setArgument(0, varExp);

  if (!colect->findFunctionApplication(label))
    colect->insertFunctionApplication(label, tempFC);

  if (flag == false)
    Body.insert(Body.end(), name);
  else
    numeUitat = name;

}

void newTranslator::VisitBinSub(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinSUb");

  ::std::string op = "integerMinus";
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerMinus");

}

void newTranslator::VisitBinMul(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinMult");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerMult");
}

void newTranslator::VisitBinDiv(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinDiv");
  cout << "Division operation not supported yet!" << endl;
  exit(1);
}

void newTranslator::VisitBinShl(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinShl");
  cout << "Shift operation not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinShr(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinShr");
  cout << "Shift operation not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinAnd(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinAnd");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "booleanAnd");
}

void newTranslator::VisitBinXor(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinXor");
  cout << "Logical operations not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinOr(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinOr");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "booleanOr");
}

void newTranslator::VisitBinLOr(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinLOr");
  cout << "Logical operations not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinLAnd(const BinaryOperator* bop)
{
  CALL("newTranslator::VisitBinLAnd");
  cout << "Logical operations not supported" << endl;
  exit(1);
}

void newTranslator::VisitBinLT(const BinaryOperator* bop)
{
  //less then
  CALL("newTranslator::VisitBinLT");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerLess");

}

void newTranslator::VisitBinGT(const BinaryOperator* bop)
{
  //greater than
  CALL("newTranslator::VisitBinGT");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerGreater");
}

void newTranslator::VisitBinLE(const BinaryOperator* bop)
{
  //less or equal
  CALL("newTranslator::VisitBinLE");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerLessEq");
}

void newTranslator::VisitBinGE(const BinaryOperator* bop)
{
  //greater or equal
  CALL("newTranslator::VisitBinGE");
  treatSimpleBinaryOperation(bop->getLHS(), bop->getRHS(), "integerGreaterEq");
}

// this part takes care of the unary operators +/-/not

void newTranslator::VisitUnaryPreInc(const UnaryOperator * uop)
{
  //cout<<"Increment"<<endl;
  CALL("newTranslator::VisitUnaryPReInc");
  treatSpecialCase(uop->getSubExpr(), "PlusPlus");
}

void newTranslator::VisitUnaryPreDec(const UnaryOperator * uop)
{
  //cout<<"decrement "<<endl;
  CALL("newTranslator::VisitUnaryPreDec");
  treatSpecialCase(uop->getSubExpr(), "MinusMinus");
}

void newTranslator::VisitUnaryPostInc(const UnaryOperator* uop)
{
  //cout<<"Post increment"<<endl;
  CALL("newTranslator::VisitUnaryPostInc");
  treatSpecialCase(uop->getSubExpr(), "PlusPlus");
}

void newTranslator::VisitUnaryPostDec(const ::clang::UnaryOperator* uop)
{
  CALL("newTranslator::VisitUnaryPostDec");
  treatSpecialCase(uop->getSubExpr(), "MinusMinus");

}

bool newTranslator::isArray(const ::clang::Expr* exp)
{
  CALL("newwTranslatpr::isArray");
  if (::clang::ArraySubscriptExpr::classof(exp))
    return true;

  if (::clang::ImplicitCastExpr::classof(exp)) {
    const ::clang::ImplicitCastExpr *e = dyn_cast< ::clang::ImplicitCastExpr>(exp);
    if (::clang::ArraySubscriptExpr::classof(e->getSubExpr()))
      return true;
    // exp->dump();

  }
  return false;
}

bool newTranslator::isNumber(const ::clang::Expr* exp)
{
  CALL("newTranslator::isNumber");
  if (::clang::IntegerLiteral::classof(exp))
    return true;

  if (::clang::UnaryOperator::classof(exp)) {

    const ::clang::UnaryOperator* uop = llvm::dyn_cast< ::clang::UnaryOperator>(exp);
    if (uop->isArithmeticOp()) {
      //takes care not to accept the unary minus (negation of a literal)
      if (::clang::ImplicitCastExpr::classof(uop->getSubExpr()))
	return false;

      return true;
    }

  }

  return false;
}

bool newTranslator::isVariable(const ::clang::Expr* exp)
{
  CALL("newTranslator::isVariable");
  if (exp->isLValue() && !(::clang::ArraySubscriptExpr::classof(exp)))
    return true;

  if (clang::ImplicitCastExpr::classof(exp)) {
    clang::ImplicitCastExpr* ice = (clang::ImplicitCastExpr*) exp;
    //ice->dump();
    if (clang::DeclRefExpr::classof(ice->getSubExpr()))
      return true;
  }
  return false;
}

//checks if a Expression is "simple" - either array application, integer value
// or variable

bool newTranslator::isSimpleExpression(const ::clang::Expr* exp)
{
  CALL("newTranslator::isSimpleExpression");
  //takes care of the variables from the right side of the = sign
  if (::clang::ImplicitCastExpr::classof(exp)) {
    const ::clang::ImplicitCastExpr *ie = dyn_cast< ::clang::ImplicitCastExpr>(exp);
    if (::clang::DeclRefExpr::classof(ie->getSubExpr()))
      if (isVariable(ie->getSubExpr()))
	return true;
  }

  if (isVariable(exp))
    return true;
  if (isArray(exp)) {
    return true;
  }
  if (isNumber(exp))
    return true;
  return false;
}

void newTranslator::AddVariableName(::std::string name)
{
  CALL("newTranslator::AddVariableName");

  if (!colect->findVarExpression(name)) {
    Program::VariableExpression* tempVarE;
    Program::Variable* tempVar;
    tempVar = new Program::Variable(name, Program::Type::integerType());
    tempVarE = new Program::VariableExpression(tempVar);
    colect->insertVariableExpression(name, tempVarE);
  }

}

/**
 * adds the array name to the map of VariableExpressions* 
 * @param name - the name of the array found in the program
 */
void newTranslator::AddArrayName(::std::string name)
{
  CALL("newTranslator::AddArrayName");
  if (!colect->findVarExpression(name)) {
    Program::ArrayType* arr = new Program::ArrayType(
	    Program::Type::integerType());
    Program::Variable* tempVar = new Program::Variable(name, arr);
    Program::VariableExpression* tempVarE = new Program::VariableExpression(
	    tempVar);
    colect->insertVariableExpression(name, tempVarE);
  }

}

void newTranslator::AddValues(int val)
{
  CALL("newTranslator::AddValues");
  if (!colect->findConstantInteger(val)) {
    Program::ConstantIntegerExpression* con =
	    new Program::ConstantIntegerExpression(val);
    colect->insertConstantIntegerExpr(val, con);
  }
}

/**
 * main like function which initiates the translation
 * @param stmt
 */
void newTranslator::getVariables(const Stmt* stmt)
{
  CALL("newTranslator::getVariables");
  Visit(stmt);
}

/**
 * convert an integer into a string
 * @param n integer value
 * @return a string
 */
::std::string newTranslator::noToString(int n)
{
  CALL("newTranslator::noToString");
  ::std::string name = "";
  ::std::stringstream ss;
  ss << n; //"   "<<l->getValue().getHashValue();
  name.append(ss.str());
  return name;

}

/**
 * convert a string to an integer
 * @param s string
 * @return integer value
 */
int newTranslator::stringToInt(std::string s)
{
  CALL("newTranslator::stringToInt");
  int value;
  stringstream ss(s);
  ss >> value;
  return value;
}
//one improvement could be write in a file gave as a command line


void newTranslator::RunRewriting()
{
  CALL("newTranslator::RunRewriting");
  flag = true;
  getVariables(decl_body);
  if(_whileToAnalyze!=-1);
    colect->runAnalysis(_whileToAnalyze);

}

Program::Statement* newTranslator::getWhile(int n){
  CALL("newTranslator::getWhile");
  flag=true;
  getVariables(decl_body);
  if(_whileToAnalyze!=-1)
    return colect->getWhile(n);
  else USER_ERROR("The value should be positive");
}
//composes the statements to be written in the new program
//and sorts them into the two main categories: outer most or inside of a construction

void newTranslator::writeWhileStatments()
{
  CALL("newTranslator::writeWhileStatements");

  int b_while = -1, e_while = -1, no;

  Program::WhileDo* whileDoS;
  Program::Block* wBlock;
  //the while belongs to a inner loop/if construction
  if (flag == false) {
    int j;
    for (j = 0; j < Body.size(); j++)
      if (Body[j] == "begin_while")
	b_while = j;
    for (j = 0; j < Body.size(); j++)
      if (Body[j] == "end_while") {
	e_while = j;
	break;
      }

    if (b_while != -1 && e_while != -1) {

      wBlock = new Program::Block(e_while - b_while - 2);
      for (j = b_while + 2; j < e_while; j++) {
	if (colect->findAssignemt(Body[j]))
	  wBlock->setStatement(j - b_while - 2, colect->getAssignment(Body[j]));
	else if (colect->findWhileDo(Body[j]))
	  wBlock->setStatement(j - b_while - 2, colect->getWhile(Body[j]));
	else if (colect->findIfThenElse(Body[j]))
	  wBlock->setStatement(j - b_while - 2, colect->getIfThenElse(Body[j]));
	else if (colect->findIfThen(Body[j]))
	  wBlock->setStatement(j-b_while-2, colect->getIfThen(Body[j]));
	else {
	  ASSERTION_VIOLATION;
	}
      }

      //condition, body
      innerWhile++;
      Program::FunctionApplicationExpression* condit =
	      colect->getFunctionApplicationExpression(Body[b_while + 1]);
      whileDoS = new Program::WhileDo(condit, wBlock);

      colect->insertWhileDo("Whl_" + Body[b_while + 1]+noToString(innerWhile), whileDoS);
      no = e_while - b_while;
      Body[b_while++] = "Whl_" + Body[b_while + 1]+noToString(innerWhile);

      for (j = e_while + 1; j < Body.size(); j++)
	Body[b_while++] = Body[j];
      while (no != 0) {
	Body.pop_back();
	no--;
      }
      b_while = 1;
      //endif
    }

  }

  if (flag == true) {
    wBlock = new Program::Block(Body.size());
    for (uint j = 0; j < Body.size(); j++) {
      if (colect->findAssignemt(Body[j]))
	wBlock->setStatement(j, colect->getAssignment(Body[j]));
      else if (colect->findIfThenElse(Body[j]))
	wBlock->setStatement(j, colect->getIfThenElse(Body[j]));
      else if (colect->findIfThen(Body[j]))
	wBlock->setStatement(j, colect->getIfThen(Body[j]));
      else
	wBlock->setStatement(j, colect->getWhile(Body[j]));
    }

    string condName = _mainProgram[_mainProgram.size()-1].substr(4);
    string whileName = condName+ noToString(_mainProgram.size());
     _mainProgram[_mainProgram.size()-1]= whileName;
    colect->insertBlock("loop" + whileName, wBlock);
    while (!Body.empty())
      Body.pop_back();
    Program::FunctionApplicationExpression* condit =
	    colect->getFunctionApplicationExpression(condName);
    whileDoS = new Program::WhileDo(condit, wBlock);
    colect->insertWhileDo(whileName, whileDoS);
    colect->insertMainProgramStatement(whileDoS);
  }

}

///TODO: add the appropriate behaviour for if cond then ; else statements
//one idea would be to negate the condition and create an IfThen* structure
//with then branch as the else
void newTranslator::writeIfStatments(string att)
{
  CALL("newTranslator::writeIfStatements");
  int b_then = -1, b_else = -1, e_then = -1, e_else = -1;
  uint i;
    //go to first then - outer if
  int b_inIf = -1, e_inIf = -1;
  std::vector<string> backup;
  for (i = 0; i < Body.size(); i++) {
    if (Body[i] == att + "begin_if") {
      b_inIf = i;
      break;
    }
    backup.insert(backup.end(), Body[i]);
  }
  for (i = 0; i < Body.size(); i++)
    if (Body[i] == att + "end_if") {
      e_inIf = i;
      break;
    }

  for (i = 0; i < Body.size(); i++)
    if (Body[i] == att + "if_then") {
      b_then = i;
      break;
    }

  for (i = 0; i < Body.size(); i++)
    if (Body[i] == att + "end_then") {
      e_then = i;
      break;
    }

  for (i = 0; i < Body.size(); i++)
    if (Body[i] == att + "if_else") {
      b_else = i;
      break;
    }

  for (i = 0; i < Body.size(); i++)
    if (Body[i] == att + "end_else") {
      e_else = i;
      break;
    }
  int n;
  ::std::string _then, _else;
  n = (e_then - b_then - 1);


  Program::Block* _thenP, *_elseP;

  _thenP = new Program::Block(n);

  if (b_then != -1 && e_then != -1) {
    for (i = b_then + 1; i < e_then; i++) {
      if (colect->findAssignemt(Body[i]))
	_thenP->setStatement(i - b_then - 1, colect->getAssignment(Body[i]));
      else if (colect->findWhileDo(Body[i]))
	_thenP->setStatement(i - b_then - 1, colect->getWhile(Body[i]));
      else
	_thenP->setStatement(i - b_then - 1, colect->getIfThenElse(Body[i]));
    }
    if (!colect->findBlock(_then))
      colect->insertBlock(_then, _thenP);
  } else
    _then = "NULL";
  //pe ramura lui else trebuie sa adaug null


  n = (e_else - b_else - 1);
  if (n>0){
  _elseP = new Program::Block(n);
  if (b_else != -1 && e_else != -1) {
    for (i = b_else + 1; i < e_else; i++) {
      if (colect->findAssignemt(Body[i]))
	_elseP->setStatement(i - b_else - 1, colect->getAssignment(Body[i]));
      else if (colect->findWhileDo(Body[i]))
	_elseP->setStatement(i - b_else - 1, colect->getWhile(Body[i]));
      else
	_elseP->setStatement(i - b_else - 1, colect->getIfThenElse(Body[i]));
    }
    if (!colect->findBlock(_else))
      colect->insertBlock(_else, _elseP);
  } else
    _else = "NULL";
  }
  int c = b_inIf;

  for (i = e_inIf + 1; i < Body.size(); i++) {
    //   cout<<Body[i]<<endl;
    Body[c++] = Body[i];
  }

  ::std::string st = "if_" + Body[b_inIf + 1];
  if (n>0)
    {
    Program::IfThenElse* ite;
    ite = new Program::IfThenElse(colect->getFunctionApplicationExpression(
	  Body[b_inIf + 1]), _thenP, _elseP);
    colect->insertIfThenElse("if_" + Body[b_inIf + 1], ite);
    }
  else
    {
    Program::IfThen* ift = new Program::IfThen(colect->getFunctionApplicationExpression(Body[b_inIf+1]), _thenP);
    colect->insertIfThen("if_"+ Body[b_inIf+1],ift);
    }

  Body.clear();

  Body = backup;

}

//take each statement at a time and treat it, according to the defined rules


//helping function which returns the declaration of a variable
/**
 * function which returns the declaration of a variable
 * @param expr - constant clang expression
 * @return clang::VarDecl
 */
const ::clang::VarDecl * newTranslator::GetVarDecl(const ::clang::Expr* expr)
{
  CALL("newTranslator::GetVarDecl");
  const VarDecl* var_decl = NULL;

  if (DeclRefExpr::classof(expr)) {
    //
    const ValueDecl* val_decl = ((const DeclRefExpr*) expr)->getDecl();
    if (VarDecl::classof(val_decl)) {
      var_decl = (const VarDecl*) val_decl;

    }
  }

  //clang::QualType type = var_decl->getType();
  //cout<<"cuala tip"<< clang::QualType::getAsString(type.split())<<endl;
  return var_decl;

}

///
///The function is meant to be used for retrieving the integer value written in the
/// source code. It can be called when you are sure that there is an actual value
///

::std::string newTranslator::getSignedValue(const ::clang::Expr *exp)
{
  CALL("newTranslator::getSignedValue");
  ::std::string value = "";
  ::std::stringstream ss;

  if (::clang::UnaryOperator::classof(exp)) {
    //on the signed values I have to take care of how we represent them in the program

    const ::clang::UnaryOperator* uop = (const ::clang::UnaryOperator *) exp;

    if (uop->isArithmeticOp()) {
      value = uop->getOpcodeStr(uop->getOpcode());
    }

    if (::clang::FloatingLiteral::classof(uop->getSubExpr())) {
      ::std::cout << "NOT TAKEN CARE OF FLOATS YET" << ::std::endl;
    }

    ///
    /// Check if it is a IntegerLiteral, and print out the actual value
    ///
    if (::clang::IntegerLiteral::classof(uop->getSubExpr())) {
      ::clang::IntegerLiteral *l =
	      (::clang::IntegerLiteral *) uop->getSubExpr();
      APSInt val;
      l->EvaluateAsInt(val, *ctx);
      value += val.toString(10);

    }

  }

  if (::clang::ImplicitCastExpr::classof(exp)) {

    const ::clang::ImplicitCastExpr *impc =
	    (const ::clang::ImplicitCastExpr *) exp;
    const ::clang::Expr * expr = impc->getSubExpr();

    if (::clang::FloatingLiteral::classof(expr)) {

      ::std::cout << "NOT YET TAKEN CARE OF!" << ::std::endl;

    }

  }
  if (::clang::IntegerLiteral::classof(exp)) {
    const ::clang::IntegerLiteral *l = (const ::clang::IntegerLiteral *) exp;

    ss << l->getValue().getSExtValue();
    value = ss.str();

  }

  return value;
}

///
///Returns the name of a variable from the expression being parsed
///

::std::string newTranslator::getLiteralName(const ::clang::Expr *exp)
{
  CALL("newTranslator::GetLiteralName");
  return GetVarDecl(exp)->getNameAsString();
}

void newTranslator::addToMainProgram(::std::string exp)
{
  CALL("newTranslator::addToMainProgram");

  _mainProgram.insert(_mainProgram.end(), exp);

}

void newTranslator::treatSpecialCase(const ::clang::Expr *lhs,
	::std::string operation)
{
  CALL("newTranslator::treatSpecialCase");
  ::std::string construction = "";
  ::std::string c0 = "", constr = "";
  ::std::string newop;

  c0 = simpleExpression(lhs);
  AddValues(1);

  Program::FunctionApplicationExpression* fapp;

  if (operation == "PlusPlus") {
    newop = "integerPlus";
    fapp = new Program::FunctionApplicationExpression(
	    Program::ConstantFunctionExpression::integerPlus());
  } else {
    fapp = new Program::FunctionApplicationExpression(
	    Program::ConstantFunctionExpression::integerMinus());
    newop = "integerMinus";
  }

  Program::VariableExpression* variable = colect->getVarExpression(c0);

  if (variable == NULL) {
    Program::Variable* vv = new Program::Variable(c0,
	    Program::Type::integerType());
    Program::VariableExpression* v = new Program::VariableExpression(vv);

    colect->insertVariableExpression(c0, v);
    variable = v;
  }

  fapp->setArgument(0, variable);
  fapp->setArgument(1, colect->getConstantIntegerExpr(1));
  construction = c0 + "_" + newop + "__1";

  if (!colect->findFunctionApplication(construction))
    colect->insertFunctionApplication(construction, fapp);

  Program::Assignment* ass = new Program::Assignment(variable, fapp);

  if (!colect->findAssignemt(c0 + "_ASS_" + construction))
    colect->insertAssignment(c0 + "_ASS_" + construction, ass);

  if (flag == false)
    Body.insert(Body.end(), c0 + "_ASS_" + construction);
  else
    numeUitat = c0 + "_ASS_" + construction;

}

void newTranslator::treatSpecial(const ::clang::Expr *lhs,
	const ::clang::Expr *rhs, ::std::string operation)
{
  CALL("newTranslator::treatSpecial");
  ::std::string construction = "";
  ::std::string c0 = "", constr = "";
  ::std::string newop;

  if (operation == "PlusEq" || operation == "MinusEq" || operation == "MultEq") {

    if (operation == "PlusEq")
      newop = "integerPlus";
    else if (operation == "MinusEq")
      newop = "integerMinus";
    else
      newop = "integerMult";

    ::std::string construction = "";
    ::std::string c0 = "", constr = "";
    c0 = simpleExpression(lhs);

    Program::VariableExpression* variable;
    Program::FunctionApplicationExpression* fapp =
	    new Program::FunctionApplicationExpression(getConstFunction(newop));

    if (!colect->findVarExpression(c0)) {
      Program::Variable* vv = new Program::Variable(c0,
	      Program::Type::integerType());
      Program::VariableExpression* v = new Program::VariableExpression(vv);
      colect->insertVariableExpression(c0, v);
      variable = v;
    } else
      variable = colect->getVarExpression(c0);

    fapp->setArgument(0, variable);

    if (isSimpleExpression(rhs)) {
      construction = simpleExpression(rhs);
      if (isNumber(rhs)) {
	int s = stringToInt(construction);
	Program::ConstantIntegerExpression* cie =
		colect->getConstantIntegerExpr(s);
	fapp->setArgument(1, cie);
      } else if (isVariable(rhs)) {
	Program::VariableExpression* varE = colect->getVarExpression(
		construction);
	fapp->setArgument(1, varE);
      } else {
	Program::ArrayApplicationExpression* arr =
		colect->getArrayApplicationExpression(construction);
	fapp->setArgument(1, arr);
      }

    }//aici am ramas cu tradus la treatSpecial .. trebuie adaugat pe cazuri
    else //si mai trebuie adaugate expresiile in map.
    {
      numeUitat = "";
      Visit(rhs);
      construction = numeUitat;
      Program::FunctionApplicationExpression* f =
	      colect->getFunctionApplicationExpression(numeUitat);
      fapp->setArgument(1, f);

    }

    if (!colect->findFunctionApplication(c0 + "_" + newop + "_" + construction))
      colect->insertFunctionApplication(c0 + "_" + newop + "_" + construction,
	      fapp);

    Program::Assignment* ass = new Program::Assignment(
	    colect->getVarExpression(c0), fapp);
    if (!colect->findAssignemt(c0 + "_ASS_" + c0 + "_" + newop + "_"
	    + construction))
      colect->insertAssignment(c0 + "_ASS_" + c0 + "_" + newop + "_"
	      + construction, ass);

    if (flag == false)
      Body.insert(Body.end(), c0 + "_ASS_" + c0 + "_" + newop + "_"
	      + construction);
    else
      numeUitat = c0 + "_ASS_" + c0 + "_" + newop + "_" + construction;

  }

}

std::string newTranslator::WriteSimpleAssignment(const ::clang::Expr* lhs,
	const Expr* rhs, string operation)
{
  CALL("newTranslator::WriteSimpleAssignment");

  string name = "";
  bool flg = true;
  Program::Assignment* ass;
  Program::VariableExpression* leftH;
  Program::ArrayApplicationExpression* arra, *arraR;
  numeUitat = simpleExpression(lhs);
  name = simpleExpression(rhs);

  if (isVariable(lhs)) {
    if (colect->findVarExpression(numeUitat))
      leftH = colect->getVarExpression(numeUitat);
    else {
      Program::Variable* v = new Program::Variable(numeUitat,
	      Program::Type::integerType());
      leftH = new Program::VariableExpression(v);
      colect->insertVariableExpression(numeUitat, leftH);
    }
  } else {
    flg = false;
    if (colect->findArrayApplication(numeUitat)) {
      arra = colect->getArrayApplicationExpression(numeUitat);
    } else {
      std::string name = simpleExpression(lhs);
      arra = colect->getArrayApplicationExpression(name);
    }
  }

  numeUitat.append("_ASS_" + name);

  if (isNumber(rhs)) {
    Program::ConstantIntegerExpression* numb;
    if (colect->findConstantInteger(stringToInt(name)))
      numb = colect->getConstantIntegerExpr(stringToInt(name));
    else {
      numb = new Program::ConstantIntegerExpression(stringToInt(name));
      colect->insertConstantIntegerExpr(stringToInt(name), numb);
    }
    if (flg == true)
      ass = new Program::Assignment(leftH, numb);
    else
      ass = new Program::Assignment(arra, numb);
  } else if (isVariable(rhs)) {
    Program::VariableExpression* rightE;
    if (colect->findVarExpression(name))
      rightE = colect->getVarExpression(name);
    else {
      Program::Variable* va = new Program::Variable(name,
	      Program::Type::integerType());
      rightE = new Program::VariableExpression(va);
      colect->insertVariableExpression(name, rightE);
    }
    if (flg == true)
      ass = new Program::Assignment(leftH, rightE);
    else
      ass = new Program::Assignment(arra, rightE);
  } else {
    if (colect->findArrayApplication(name))
      arraR = colect->getArrayApplicationExpression(name);
    else
      simpleExpression(rhs);
    if (flg == true)
      ass = new Program::Assignment(leftH, arraR);
    else
      ass = new Program::Assignment(arra, arraR);
  }

  if (!colect->findAssignemt(numeUitat))
    colect->insertAssignment(numeUitat, ass);
  //LOG("trans_ass", ass->prettyPrint(std::cout, 3));

  if (flag == false)
    Body.insert(Body.end(), numeUitat);

  return numeUitat;

}

std::string newTranslator::simpleExpression(const clang::Expr* exp)
{
  CALL("newTranslator::simpleExpression");
  string name = "";

  if (isVariable(exp)) {

    string nm;
    if (clang::ImplicitCastExpr::classof(exp)) {
      const clang::ImplicitCastExpr* ice = dyn_cast< ::clang::ImplicitCastExpr>(exp);
      nm = getLiteralName(ice->getSubExpr());
    } else
      nm = getLiteralName(exp);
    AddVariableName(nm);
    name = nm;

  }
  if (isNumber(exp)) {
    name = getSignedValue(exp);
    int val;
    val = stringToInt(name);
    if (!colect->findConstantInteger(val)) {
      Program::ConstantIntegerExpression* value =
	      new Program::ConstantIntegerExpression(val);
      colect->insertConstantIntegerExpr(val, value);
    }
  }

  if (isArray(exp)) {
    if (::clang::ArraySubscriptExpr::classof(exp)) {
      const ::clang::ArraySubscriptExpr *s = dyn_cast<
	      ::clang::ArraySubscriptExpr> (exp);
      //aici se extrage indexul
      const ::clang::Expr *index, *base;
      index = s->getIdx();
      //aici se extrage numele arrayului
      base = s->getBase();

      ::std::string composition = "", idx = "", nme = "";
      if (::clang::ImplicitCastExpr::classof(base)) {
	const ::clang::ImplicitCastExpr *ice = dyn_cast<
		::clang::ImplicitCastExpr> (base);
	name = getLiteralName(ice->getSubExpr());
	AddArrayName(name);
	nme = name;
	composition = name + ",";
      }

      Program::ArrayApplicationExpression* arrApp;

      Program::VariableExpression* tmp = colect->getVarExpression(nme);

      if (isSimpleExpression(index)) {

	idx = simpleExpression(index);
	name = name + "_" + idx + "_";
	composition = composition + idx + ");";
	if (isNumber(index)) {
	  int val;
	  stringstream ss(idx);
	  ss >> val;
	  Program::ConstantIntegerExpression* ct =
		  colect->getConstantIntegerExpr(val);
	  arrApp = new Program::ArrayApplicationExpression(tmp, ct);

	} else if (isVariable(index)) {
	  arrApp = new Program::ArrayApplicationExpression(
		  colect->getVarExpression(nme), colect->getVarExpression(idx));
	} else {
	  arrApp = new Program::ArrayApplicationExpression(
		  colect->getVarExpression(nme),
		  colect->getArrayApplicationExpression(idx));
	}
	if (!colect->findArrayApplication(name))
	  colect->insertArrayApplication(name, arrApp);
      } else {
	//constraint: for the moment we can handle only FunctionApplicationExpressions
	numeUitat = " ";
	Visit(index);
	name = name + "_" + numeUitat + "_";

	if (colect->findFunctionApplication(numeUitat))
	  arrApp = new Program::ArrayApplicationExpression(
		  colect->getVarExpression(nme),
		  colect->getFunctionApplicationExpression(numeUitat));
	else
	  arrApp = new Program::ArrayApplicationExpression(
		  colect->getVarExpression(nme),
		  colect->getArrayApplicationExpression(numeUitat));
	if (!colect->findArrayApplication(name))
	  colect->insertArrayApplication(name, arrApp);
	composition = composition + numeUitat + ");";
	numeUitat = "";
      }

    }

    if (::clang::ImplicitCastExpr::classof(exp)) {
      const ::clang::ImplicitCastExpr *e = dyn_cast< ::clang::ImplicitCastExpr> (exp);
      ::std::string composition = "", idx = "", nme = "";
      Program::ArrayApplicationExpression* arrApp;

      if (::clang::ArraySubscriptExpr::classof(e->getSubExpr())) {
	const ::clang::ArraySubscriptExpr *s = dyn_cast<
		::clang::ArraySubscriptExpr> (e->getSubExpr());
	//here the index is extracted
	const ::clang::Expr *index, *base;
	index = s->getIdx();
	//get the name of the array
	base = s->getBase();

	if (::clang::ImplicitCastExpr::classof(base)) {

	  const ::clang::ImplicitCastExpr *ice = dyn_cast<
		  ::clang::ImplicitCastExpr> (base);
	  name = getLiteralName(ice->getSubExpr());
	  nme = name;
	  AddArrayName(name);
	  composition = name + ",";

	}

	if (isSimpleExpression(index)) {

	  idx = simpleExpression(index);
	  composition = composition + idx + ");";
	  name = name + "_" + idx + "_";
	  composition = composition + idx + ");";

	  if (isNumber(index)) {
	    int val;
	    stringstream ss(idx);
	    ss >> val;
	    arrApp = new Program::ArrayApplicationExpression(
		    colect->getVarExpression(nme),
		    colect->getConstantIntegerExpr(val));
	  } else if (isVariable(index)) {

	    arrApp = new Program::ArrayApplicationExpression(
		    colect->getVarExpression(nme),
		    colect->getVarExpression(idx));

	  } else {
	    arrApp = new Program::ArrayApplicationExpression(
		    colect->getVarExpression(nme),
		    colect->getArrayApplicationExpression(idx));
	  }
	} else {
	  numeUitat = " ";
	  Visit(index);
	  if (colect->findFunctionApplication(numeUitat))
	    arrApp = new Program::ArrayApplicationExpression(
		    colect->getVarExpression(nme),
		    colect->getFunctionApplicationExpression(numeUitat));
	  else
	    arrApp = new Program::ArrayApplicationExpression(
		    colect->getVarExpression(nme),
		    colect->getArrayApplicationExpression(numeUitat));

	  name = name + "_" + numeUitat + "_";
	  composition = composition + numeUitat + ");";
	  numeUitat = "";
	}

      }

      if (!colect->findArrayApplication(name))
	colect->insertArrayApplication(name, arrApp);

    }

  }

  return name;

}

::std::string newTranslator::WriteSimpleStatement(const ::clang::Expr *lhs,
	const ::clang::Expr *rhs, ::std::string operation)
{
  CALL("newTranslator::WriteSimpleStatement");
  std::string name = "";

  if (operation == "Assign")
    return WriteSimpleAssignment(lhs, rhs, "Assign");
  else {
    Program::ConstantFunctionExpression* cfe = getConstFunction(operation);
    Program::FunctionApplicationExpression* fcapp =
	    new Program::FunctionApplicationExpression(cfe);
    std::string cName;
    name = simpleExpression(lhs);
    string name1 = simpleExpression(rhs);

    if (isNumber(lhs)) {
      Program::ConstantIntegerExpression* numb;
      if (colect->findConstantInteger(stringToInt(name)))
	numb = colect->getConstantIntegerExpr(stringToInt(name));
      else {

	numb = new Program::ConstantIntegerExpression(stringToInt(name));
	colect->insertConstantIntegerExpr(stringToInt(name), numb);
      }

      fcapp->setArgument(0, numb);

    } else if (isVariable(lhs)) {
      Program::VariableExpression* rightE;
      if (colect->findVarExpression(name))
	rightE = colect->getVarExpression(name);
      else {
	cout << colect->getVarExpression("a")->toString(1)
		<< colect->getVarExpression(name)->toString(2) << endl;
	Program::Variable* va = new Program::Variable(name,
		Program::Type::integerType());
	rightE = new Program::VariableExpression(va);
	colect->insertVariableExpression(name, rightE);
      }
      fcapp->setArgument(0, rightE);
    } else if (isArray(lhs)) {
      Program::ArrayApplicationExpression* arra;
      if (colect->findArrayApplication(name))
	arra = colect->getArrayApplicationExpression(name);
      else {
	string s = simpleExpression(lhs);
	arra = colect->getArrayApplicationExpression(s);
      }
      fcapp->setArgument(0, arra);
    }
    cName = name;
    name = name1;
    cName.append("_" + operation + "_");
    cName.append(name);
    if (isNumber(rhs)) {
      Program::ConstantIntegerExpression* numb;
      if (colect->findConstantInteger(stringToInt(name)))
	numb = colect->getConstantIntegerExpr(stringToInt(name));
      else {
	numb = new Program::ConstantIntegerExpression(stringToInt(name));
	colect->insertConstantIntegerExpr(stringToInt(name), numb);
      }

      fcapp->setArgument(1, numb);
    } else if (isVariable(rhs)) {
      Program::VariableExpression* rightE;
      if (colect->findVarExpression(name))
	rightE = colect->getVarExpression(name);
      else {
	Program::Variable* va = new Program::Variable(name,
		Program::Type::integerType());
	rightE = new Program::VariableExpression(va);
	colect->insertVariableExpression(name, rightE);
      }
      fcapp->setArgument(1, rightE);
    } else {
      Program::ArrayApplicationExpression* arra =
	      colect->getArrayApplicationExpression(name);
      fcapp->setArgument(1, arra);
    }
    colect->insertFunctionApplication(cName, fcapp);
    return cName;
  }

  return NULL;
}

Program::ConstantFunctionExpression* newTranslator::getConstFunction(
	std::string op)
{
  CALL("newTranslator::getCosntFunction");
  if (op == "integerEq" || op == "integerNEq")
    return Program::ConstantFunctionExpression::integerEq();
  else if (op == "integerGreater")
    return Program::ConstantFunctionExpression::integerGreater();
  else if (op == "integerGreaterEq")
    return Program::ConstantFunctionExpression::integerGreaterEq();
  else if (op == "integerLess")
    return Program::ConstantFunctionExpression::integerLess();
  else if (op == "integerLessEq")
    return Program::ConstantFunctionExpression::integerLessEq();
  else if (op == "integerMinus")
    return Program::ConstantFunctionExpression::integerMinus();
  else if (op == "integerMult")
    return Program::ConstantFunctionExpression::integerMult();
  else if (op == "integerPlus")
    return Program::ConstantFunctionExpression::integerPlus();
  else if (op == "booleanAnd")
    return Program::ConstantFunctionExpression::booleanAnd();
  else if (op == "booleanOr")
    return Program::ConstantFunctionExpression::booleanOr();
  else if (op == "booleanNeg")
    return Program::ConstantFunctionExpression::booleanNeg();
  return NULL;
}

std::string newTranslator::treatSimpleBinaryOperation(const clang::Expr* lhs,
	const clang::Expr* rhs, std::string op)
{
  CALL("newTranslator::treatSimpleBinaryOperation");
  Program::FunctionApplicationExpression* fcapp =
	  new Program::FunctionApplicationExpression(getConstFunction(op));
  string name = "", namer = "";
  bool flg = false;
  if (isSimpleExpression(lhs)) {
    flg = true;
    name = simpleExpression(lhs);
  } else {
    Visit(lhs);
    name = numeUitat;
    numeUitat = "";
  }

  if (flg) {
    if (isNumber(lhs))
      fcapp->setArgument(0, colect->getConstantIntegerExpr(stringToInt(name)));
    else if (isVariable(lhs))
      fcapp->setArgument(0, colect->getVarExpression(name));
    else
      fcapp->setArgument(0, colect->getArrayApplicationExpression(name));

  } else
    fcapp->setArgument(0, colect->getFunctionApplicationExpression(name));
 if(rhs!=NULL){
  flg = false;
  if (isSimpleExpression(rhs)) {
    flg = true;
    namer = simpleExpression(rhs);
  } else {
    Visit(rhs);
    namer = numeUitat;
    numeUitat = "";
  }

  if (flg) {
    if (isNumber(rhs))
      fcapp->setArgument(1, colect->getConstantIntegerExpr(stringToInt(namer)));
    else if (isVariable(rhs))
      fcapp->setArgument(1, colect->getVarExpression(namer));
    else
      fcapp->setArgument(1, colect->getArrayApplicationExpression(namer));

  } else
    fcapp->setArgument(1, colect->getFunctionApplicationExpression(namer));
 }
  numeUitat = name + "_" + op + "_" + namer;

  if(op == "integerNEq"){
    numeUitat = "negation_"+numeUitat;
    Program::FunctionApplicationExpression* fcneg =
	    new Program::FunctionApplicationExpression(Program::ConstantFunctionExpression::booleanNeg());
    fcneg->setArgument(0,fcapp);
    if(!colect->findFunctionApplication(numeUitat));
      colect->insertFunctionApplication(numeUitat, fcneg);
  }
  else
    if (!colect->findFunctionApplication(numeUitat))
        colect->insertFunctionApplication(numeUitat, fcapp);
  return numeUitat;
}

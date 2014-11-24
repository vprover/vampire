/* 
 * File:   collectionOfObjects.hpp
 * Author: ioan
 *
 * Definition of a class which stores the objects needed for the analysis.
 * The objects are created during the traversal of the AST in newTranslator.
 */

#ifndef COLLECTIONOFOBJECTS_HPP
#define	COLLECTIONOFOBJECTS_HPP

#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"

#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Array.hpp"
#include "Lib/Map.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"

#include <iostream>

#include "Forwards.hpp"

namespace Translator
{

using namespace Program;
using namespace std;
using namespace Lib;

class collectionOfObjects {
public:
  collectionOfObjects();
  void trySEI(Program::Statement* s);
  bool insertVariableExpression(vstring key,
	  Program::VariableExpression* obj);
  void insertConstantIntegerExpr(int val,
	  Program::ConstantIntegerExpression* obj);
  void insertAssignment(vstring key, Program::Assignment* obj);
  void insertBlock(vstring key, Program::Block* obj);
  void insertFunctionApplication(vstring key,
	  Program::FunctionApplicationExpression* obj);
  void insertArrayApplication(vstring key,
	  Program::ArrayApplicationExpression* obj);
  void insertWhileDo(vstring key, Program::WhileDo* obj);
  void insertIfThenElse(vstring key, Program::IfThenElse* obj);
  void insertIfThen(vstring key, Program::IfThen* obj);
  Program::Assignment* getAssignment(vstring key);
  Program::Block* getBlock(vstring key);
  Program::VariableExpression* getVarExpression(vstring key);
  Program::ConstantIntegerExpression* getConstantIntegerExpr(int key);
  Program::FunctionApplicationExpression* getFunctionApplicationExpression(
	  vstring key);
  Program::ArrayApplicationExpression* getArrayApplicationExpression(
	  vstring key);
  Program::WhileDo* getWhile(vstring key);
  Program::IfThenElse* getIfThenElse(vstring key);
  Program::IfThen* getIfThen(vstring key);
  bool findAssignemt(vstring key);
  bool findBlock(vstring key);
  bool findVarExpression(vstring key);
  bool findConstantInteger(int key);
  bool findFunctionApplication(vstring key);
  bool findArrayApplication(vstring key);
  bool findWhileDo(vstring key);
  bool findIfThenElse(vstring key);
  bool findIfThen(vstring key);
  void insertMainProgramStatement(int number, Program::Statement* stmt);
  void insertMainProgramStatement(Program::Statement* stmt);
  void insertVariable(vstring key, Program::Variable* obj);
  bool findVariable(vstring key);
  Program::Variable* getVariable(vstring key);

  bool multipleLoops(Program::Statement* s);

  virtual ~collectionOfObjects();

  void runAnalysis(int n);
  Statement* getWhile(int wNumber);
  bool testASS(vstring key);
  int chekMaps(vstring key);
  Lib::Stack<Program::VariableExpression*> getVarExpStack();
private:

  Lib::Map<vstring, Program::Block*> _mapOfBlocks;
  Lib::Map<vstring, Program::ArrayApplicationExpression*> _mapOfArrayApplic;
  Lib::Map<vstring, Program::Assignment*> _mapOfAssignments;
  Lib::Map<vstring, Program::FunctionApplicationExpression*> _mapOfFcApplic;
  Lib::Map<vstring, Program::VariableExpression*> _mapOfVariableExpr;
  Lib::Map<int, Program::ConstantIntegerExpression*> _mapOfIntegers;
  Lib::Map<vstring, Program::Variable*> _mapOfVariables;

  Lib::Map<vstring, Program::WhileDo*> _mapOfWhile;
  Lib::Map<vstring, Program::IfThenElse*> _mapOfThenElse;
  Lib::Map<vstring, Program::IfThen*> _mapOfIfThen;
  Lib::Map<int, Program::Statement*> _mapOfMainProgramStatements;

};

}
#endif	/* COLLECTIONOFOBJECTS_HPP */


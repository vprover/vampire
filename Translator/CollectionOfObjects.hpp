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
  bool insertVariableExpression(std::string key,
	  Program::VariableExpression* obj);
  void insertConstantIntegerExpr(int val,
	  Program::ConstantIntegerExpression* obj);
  void insertAssignment(std::string key, Program::Assignment* obj);
  void insertBlock(std::string key, Program::Block* obj);
  void insertFunctionApplication(std::string key,
	  Program::FunctionApplicationExpression* obj);
  void insertArrayApplication(std::string key,
	  Program::ArrayApplicationExpression* obj);
  void insertWhileDo(std::string key, Program::WhileDo* obj);
  void insertIfThenElse(std::string key, Program::IfThenElse* obj);
  void insertIfThen(std::string key, Program::IfThen* obj);
  Program::Assignment* getAssignment(std::string key);
  Program::Block* getBlock(std::string key);
  Program::VariableExpression* getVarExpression(std::string key);
  Program::ConstantIntegerExpression* getConstantIntegerExpr(int key);
  Program::FunctionApplicationExpression* getFunctionApplicationExpression(
	  std::string key);
  Program::ArrayApplicationExpression* getArrayApplicationExpression(
	  std::string key);
  Program::WhileDo* getWhile(std::string key);
  Program::IfThenElse* getIfThenElse(std::string key);
  Program::IfThen* getIfThen(std::string key);
  bool findAssignemt(std::string key);
  bool findBlock(std::string key);
  bool findVarExpression(std::string key);
  bool findConstantInteger(int key);
  bool findFunctionApplication(std::string key);
  bool findArrayApplication(std::string key);
  bool findWhileDo(std::string key);
  bool findIfThenElse(std::string key);
  bool findIfThen(std::string key);
  void insertMainProgramStatement(int number, Program::Statement* stmt);
  void insertMainProgramStatement(Program::Statement* stmt);
  void insertVariable(std::string key, Program::Variable* obj);
  bool findVariable(std::string key);
  Program::Variable* getVariable(std::string key);

  bool multipleLoops(Program::Statement* s);

  virtual ~collectionOfObjects();

  void runAnalysis(int n);
  bool testASS(std::string key);
  int chekMaps(std::string key);
  Lib::Stack<Program::VariableExpression*> getVarExpStack();
private:

  Lib::Map<std::string, Program::Block*> _mapOfBlocks;
  Lib::Map<std::string, Program::ArrayApplicationExpression*> _mapOfArrayApplic;
  Lib::Map<std::string, Program::Assignment*> _mapOfAssignments;
  Lib::Map<std::string, Program::FunctionApplicationExpression*> _mapOfFcApplic;
  Lib::Map<std::string, Program::VariableExpression*> _mapOfVariableExpr;
  Lib::Map<int, Program::ConstantIntegerExpression*> _mapOfIntegers;
  Lib::Map<std::string, Program::Variable*> _mapOfVariables;

  Lib::Map<std::string, Program::WhileDo*> _mapOfWhile;
  Lib::Map<std::string, Program::IfThenElse*> _mapOfThenElse;
  Lib::Map<std::string, Program::IfThen*> _mapOfIfThen;
  Lib::Map<int, Program::Statement*> _mapOfMainProgramStatements;

};

}
#endif	/* COLLECTIONOFOBJECTS_HPP */


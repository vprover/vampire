/* 
 * File:   collectionOfObjects.cpp
 * Author: ioan
 * 
 */

#include <iostream>

#include "CollectionOfObjects.hpp"

#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"

#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Unit.hpp"

#include "Debug/Tracer.hpp"
#include "Forwards.hpp"



namespace Translator
{

collectionOfObjects::collectionOfObjects()
{
}

collectionOfObjects::~collectionOfObjects()
{
}

bool collectionOfObjects::insertVariableExpression(std::string key,
	Program::VariableExpression* obj)
{
  CALL("collectionOfObjects::insertVariableExpression");
  _mapOfVariableExpr.insert(key, obj);
  return true;
}

Program::VariableExpression* collectionOfObjects::getVarExpression(
	std::string key)
{
  CALL("getVariableExpression");
  Program::VariableExpression* varE = NULL;
  _mapOfVariableExpr.find(key, varE);
  if (varE == NULL) {
    Program::Variable* vv = (new Program::Variable(key,
	    Program::Type::integerType()));
    _mapOfVariableExpr.insert(key, (new Program::VariableExpression(vv)));
    _mapOfVariableExpr.find(key, varE);
  }

  return varE;
}

void collectionOfObjects::insertConstantIntegerExpr(int val,
	Program::ConstantIntegerExpression* obj)
{
  CALL("insertConstrantIntegerExpression");
  _mapOfIntegers.insert(val, obj);
}

void collectionOfObjects::insertAssignment(std::string key,
	Program::Assignment* obj)
{
  CALL("insertAssignment");
  if (_mapOfAssignments.find(key) == false)
    _mapOfAssignments.insert(key, obj);

}

Program::Assignment* collectionOfObjects::getAssignment(std::string key)
{
  CALL("getAssignment");
  Program::Assignment* vas = NULL;
  _mapOfAssignments.find(key, vas);
  return vas;
}
Program::ConstantIntegerExpression* collectionOfObjects::getConstantIntegerExpr(
	int key)
{
  CALL("getConstantIntegerExpr");
  Program::ConstantIntegerExpression* cie = NULL;
  _mapOfIntegers.find(key, cie);
  return cie;
}

void collectionOfObjects::insertBlock(std::string key, Program::Block* obj)
{
  CALL("insertBlock");
  _mapOfBlocks.insert(key, obj);
}

Program::Block* collectionOfObjects::getBlock(std::string key)
{
  CALL("getBlock");
  Program::Block* blk = NULL;
  _mapOfBlocks.find(key, blk);

  return blk;

}

void collectionOfObjects::insertFunctionApplication(std::string key,
	Program::FunctionApplicationExpression* obj)
{
  CALL("insertFunctionApplication");
  if (_mapOfFcApplic.find(key) != true)
    _mapOfFcApplic.insert(key, obj);

}

Program::FunctionApplicationExpression* collectionOfObjects::getFunctionApplicationExpression(
	std::string key)
{
  CALL("getFunctionApplicationExpression");
  Program::FunctionApplicationExpression* fca = NULL;
  _mapOfFcApplic.find(key, fca);
  return fca;
}

void collectionOfObjects::insertWhileDo(std::string key, Program::WhileDo* obj)
{
  CALL("insertWhileDo");
  if (_mapOfWhile.find(key) != 1)
    _mapOfWhile.insert(key, obj);
}

void collectionOfObjects::insertIfThenElse(std::string key,
	Program::IfThenElse* obj)
{
  CALL("insertIfThenElse");
  if (_mapOfThenElse.find(key) != 1)
    _mapOfThenElse.insert(key, obj);
}

Program::IfThenElse* collectionOfObjects::getIfThenElse(std::string key)
{
  CALL("getIfThenElse");
  Program::IfThenElse* ite = NULL;
  _mapOfThenElse.find(key, ite);
  return ite;
}

Program::WhileDo* collectionOfObjects::getWhile(std::string key)
{
  CALL("getWhile");
  Program::WhileDo* wdo = NULL;
  _mapOfWhile.find(key, wdo);
  return wdo;
}

void collectionOfObjects::insertArrayApplication(std::string key,
	Program::ArrayApplicationExpression* obj)
{
  CALL("insertArrayApplication");
  _mapOfArrayApplic.insert(key, obj);
}

Program::ArrayApplicationExpression* collectionOfObjects::getArrayApplicationExpression(
	std::string key)
{
  CALL("getArrayApplicationExpression");
  Program::ArrayApplicationExpression* arr = NULL;
  _mapOfArrayApplic.find(key, arr);
  return arr;
}

int collectionOfObjects::chekMaps(std::string key)
{
  CALL("collectionOfObjects::checkMaps");
  if (_mapOfAssignments.find(key))
    return 1;
  else if (_mapOfWhile.find(key))
    return 2;
  else if (_mapOfThenElse.find(key))
    return 3;
  /*  else if(_mapOfFcApplic.find(key)) return 4;

   if(_mapOfBlocks.find(key)) return 5;
   */
  return 0;
}

bool collectionOfObjects::testASS(std::string key)
{
  return _mapOfAssignments.find(key);
}

bool collectionOfObjects::multipleLoops(Program::Statement* s)
{
  CALL("collectionOfObjects::multipleLoops");
  Program::Statement::SubstatementIterator site(s);
  site.next();
  while (site.hasNext())
    if (site.next()->kind() == Program::Statement::WHILE_DO)
      return true;
  return false;
}

void collectionOfObjects::trySEI(Program::Statement* s){
  CALL("collectionOfObjects::trySEI");

  //set the symbol elimination mod on;
  env.options->setSEI(true);

  Lib::List<Kernel::Unit *>* unitList;

  Program::Analyze analyzer(s);
  analyzer.analyze();



}

void collectionOfObjects::runAnalysis(int wN)
{
  CALL("collectionOfObjects::runAnalysis");
  cout<<"se ajunge si aici"<<endl;
  int whileNumber= env.options->getWhileNumber();
  if (_mapOfWhile.numberOfElements() < whileNumber || whileNumber <= 0)
    USER_ERROR("you have less whiles than the number introduced! take care @ -wno option!");
  else {
    int whileNo = 1;
    Program::Statement* s;
    Lib::Map<int, Program::Statement*>::Iterator mpi(
	    _mapOfMainProgramStatements);
    for (int i = 1; i <= _mapOfMainProgramStatements.numberOfElements(); i++) {
      _mapOfMainProgramStatements.find(i, s);
      if (s->kind() == Program::Statement::WHILE_DO) {
	if (whileNumber == whileNo) {
	  if (multipleLoops(s)) {
	    USER_ERROR("We do not handle nested whiles yet!");
	  }
	 /* cout<<env.options->showSymbolElimination()<<" SEI"<<endl;
	  Program::Analyze analyzer(s);
	  analyzer.analyze();*/
	  trySEI(s);
	  break;
	} else
	  whileNo++;
      }
    }
    	  if(whileNo<whileNumber)
     USER_ERROR("less whiles than the number introduced!");
  }


}

bool collectionOfObjects::findArrayApplication(std::string key)
{
  CALL("collectionOfObjects::findArrayApplication");
  return _mapOfArrayApplic.find(key);
}

bool collectionOfObjects::findAssignemt(std::string key)
{
  CALL("collectionOfObjects::findAssignment");
  return _mapOfAssignments.find(key);
}

bool collectionOfObjects::findBlock(std::string key)
{
  CALL("collectionOfObjects::findBlock");
  return _mapOfBlocks.find(key);
}

bool collectionOfObjects::findConstantInteger(int key)
{
  CALL("collectionOfObjects::findConstantInteger");
  return _mapOfIntegers.find(key);
}

bool collectionOfObjects::findFunctionApplication(std::string key)
{
  CALL("collectionOfObjects::findFunctionApplication");
  return _mapOfFcApplic.find(key);
}

bool collectionOfObjects::findVarExpression(std::string key)
{
  CALL("collectionOfObjects::findVarExpression");
  return _mapOfVariableExpr.find(key);
}

void collectionOfObjects::insertMainProgramStatement(int number,
	Program::Statement* stmt)
{
  CALL("collectionOfObjects::insertMainProgramStatement");
  _mapOfMainProgramStatements.insert(number, stmt);
}

void collectionOfObjects::insertMainProgramStatement(Program::Statement* stmt)
{
  CALL("collectionOfObjects::insertMainProgramStatement");
  _mapOfMainProgramStatements.insert(
	  _mapOfMainProgramStatements.numberOfElements() + 1, stmt);
}

void collectionOfObjects::insertVariable(std::string key,
	Program::Variable* obj)
{
  CALL("collectionOfObjects::insertVariable");
  _mapOfVariables.insert(key, obj);
}
bool collectionOfObjects::findVariable(std::string key)
{
  CALL("collectionOfObjects::findVariable");
  return _mapOfVariables.find(key);
}

Program::Variable* collectionOfObjects::getVariable(std::string key)
{
  CALL("collectionOfObjects::getVariable");
  Program::Variable* var = NULL;
  _mapOfVariables.find(key, var);
  return var;
}

bool collectionOfObjects::findWhileDo(std::string key)
{
  CALL("collectionOfObjects::findWhileDo");
  return _mapOfWhile.find(key);
}

bool collectionOfObjects::findIfThenElse(std::string key)
{
  CALL("collectionOfObjects::findIfThenElse");
  return _mapOfThenElse.find(key);
}

}

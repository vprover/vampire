/**
 * @file tProgramAnalysisCopy.cpp
 * Implements class ProgramAnalysis.
 */

#include "Test/UnitTesting.hpp"



#define UNIT_ID pgm_analysis_copy  //the UNIT_ID must be a valid variable name
UT_CREATE;

#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"

using namespace Program;

//array_copy example, added 5/10/2010

// void copy () { // from paper by
//   int a, m, b;
//   int *aa, *bb;
//   //This is the program for which Vampire is ran
//   //Vampire generates invariants with universal quantifiers
// 1   a = 0;
// 2   b = 0;
// 3   while ( a < m ) {
// 4   bb[b] = aa[a];
// 5    b = b+1;
// 6    a = a+1;
// 7   }
//8 }

TEST_FUN(arraycopy)
{


  Variable* va = new Variable("a",Type::integerType());
  Variable* vb = new Variable("b",Type::integerType());
  Variable* vm = new Variable("m",Type::integerType());

  VariableExpression* a = new VariableExpression(va);
  VariableExpression* b = new VariableExpression(vb);
  VariableExpression* m = new VariableExpression(vm);

  ArrayType* arrayType = new ArrayType(Type::integerType());
  Variable* vaa = new Variable("aa",arrayType);
  Variable* vbb = new Variable("bb",arrayType);
 
  VariableExpression* aa = new VariableExpression(vaa);
  VariableExpression* bb = new VariableExpression(vbb);
 
  ConstantIntegerExpression* zero = new ConstantIntegerExpression(0);
  ConstantIntegerExpression* one = new ConstantIntegerExpression(1);

  // 1   a = 0;
  Program::Assignment* a_ASS_0 = new Program::Assignment(a,zero);

  // 2   b = 0;
  Program::Assignment* b_ASS_0 = new Program::Assignment(b,zero);

  // (a < m) in
  // 3   while ( a < m ) {
  FunctionApplicationExpression* a_less_m = new FunctionApplicationExpression(ConstantFunctionExpression::integerLess());
  a_less_m->setArgument(0,a);
  a_less_m->setArgument(1,m);

  // aa[a]
  ArrayApplicationExpression* aa_a = new ArrayApplicationExpression(aa,a);
  // bb[b]
  ArrayApplicationExpression* bb_b = new ArrayApplicationExpression(bb,b);

  // (a+1)
  FunctionApplicationExpression* a_plus_1 = new FunctionApplicationExpression(ConstantFunctionExpression::integerPlus());
  a_plus_1->setArgument(0,a);
  a_plus_1->setArgument(1,one);
  // (b+1)
  FunctionApplicationExpression* b_plus_1 = new FunctionApplicationExpression(ConstantFunctionExpression::integerPlus());
  b_plus_1->setArgument(0,b);
  b_plus_1->setArgument(1,one);

  //6       a = a+1;
  Program::Assignment* a_ASS_a_plus_1 = new Program::Assignment(a,a_plus_1);
  //5       b = b+1;
  Program::Assignment* b_ASS_b_plus_1 = new Program::Assignment(b,b_plus_1);
  //4       bb[b] = aa[a];
  Program::Assignment* bb_b_ASS_aa_a = new Program::Assignment(bb_b,aa_a);
  
  // 4-5  bb[b] = aa[a]; b = b+1;
  Block* loopBody = new Block(3);
  loopBody->setStatement(0,bb_b_ASS_aa_a);
  loopBody->setStatement(1,b_ASS_b_plus_1);
  loopBody->setStatement(2,a_ASS_a_plus_1);

  WhileDo* loop = new WhileDo(a_less_m,loopBody);
  // block 1-14
  Block* program = new Block(3);
  program->setStatement(0,a_ASS_0);
  program->setStatement(1,b_ASS_0);
  program->setStatement(2,loop);
  cout << "\n";
  Analyze analysis(program);
  analysis.analyze();
 
}
